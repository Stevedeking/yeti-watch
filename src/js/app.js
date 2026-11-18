const API = 'https://deepbook-indexer.mainnet.mystenlabs.com';
const POOL = 'SUI_USDC';

const DEPTH = 12, BOOK_DEPTH = 100;
const MARKET_POLL_MS = 3000, LIFECYCLE_POLL_MS = 10000;

const WALL_MIN = { asks: 5000, bids: 10000 };
const TRACK_MIN = 250;

const API_LIMIT = 100, INITIAL_LOOKBACK_SECONDS = 120, OVERLAP_SECONDS = 30;
const MAX_SPLIT_DEPTH = 8, REQUEST_TIMEOUT_MS = 15000;
const HISTORY_MS = 30 * 60 * 1000;
const EPISODE_GAP_MS = 5 * 60 * 1000;

const DB_NAME = 'yeti-watch-tracker-v2', DB_VERSION = 2;
const MAX_TRACKED_ORDERS = 8000, MAX_ORDER_EVENTS = 30000, MAX_SAVED_TRADES = 20000;

const normalizeTimestampMs = (value, fallback = Date.now()) => {
  if (value instanceof Date) {
    const ms = value.getTime();
    return Number.isFinite(ms) ? ms : fallback;
  }

  if (typeof value === 'string') {
    const trimmed = value.trim();
    if (/^\d+(?:\.\d+)?$/.test(trimmed)) {
      value = Number(trimmed);
    } else {
      const ms = Date.parse(trimmed);
      return Number.isFinite(ms) ? ms : fallback;
    }
  }

  const n = Number(value);
  if (!Number.isFinite(n)) return fallback;

  // API values may be seconds, milliseconds, or microseconds.
  if (n > 1e14) return n / 1000;
  if (n > 1e11) return n;
  return n * 1000;
};

const $ = id => document.getElementById(id);

const elements = {
  price: $('mid-price'),
  asks: $('asks'),
  bids: $('bids'),
  spread: $('spread'),
  trustScore: $('trust-score'),
  wallList: $('wall-list'),
  wallCount: $('wall-count')
};

const setText = (sel, text) => {
  const el = document.querySelector(sel);
  if (el) el.textContent = text;
};

setText('.trust-label', 'Cancelled, no fill');
setText('.trust-content p', 'SUI cancelled with no recorded fill (30 min window)');
setText(
  '.wall-description',
  'Big price levels, split into the orders Yeti has seen placed, filled or cancelled.'
);

let db = null;
let storageReady = false;
let marketBusy = false;
let lifecycleBusy = false;
let lifecyclePolls = 0;
let latestBook = null;

const trackedOrders = new Map();
const knownOrderEvents = new Set();
const knownTradeIds = new Set();
const makerTrades = new Map();
const wallEpisodes = new Map();

let latestLifecycleComplete = false;
let latestLifecycleIncomplete = false;

// ---------- FORMATTING ----------

const num = (v, d = 0) => {
  const n = Number(v);
  return Number.isFinite(n) ? n : d;
};

const formatPrice = v => Number(v).toFixed(8);

const formatQty = v => Number(v).toLocaleString('en-US', {
  minimumFractionDigits: 2,
  maximumFractionDigits: 2
});

const compact = n =>
  n >= 1e6 ? (n / 1e6).toFixed(1) + 'M'
    : n >= 1e3 ? (n / 1e3).toFixed(1) + 'k'
      : String(Math.round(n));

function formatAge(ts) {
  const timestamp = normalizeTimestampMs(ts, Date.now());
  const s = Math.max(
    0,
    Math.floor((Date.now() - timestamp) / 1000)
  );

  if (s < 60) return `${s}s`;

  const m = Math.floor(s / 60);

  return m < 60
    ? `${m}m ${s % 60}s`
    : `${Math.floor(m / 60)}h ${m % 60}m`;
}

function formatDurationSince(ts) {
  const timestamp = normalizeTimestampMs(ts, Date.now());
  const s = Math.max(0, Math.floor((Date.now() - timestamp) / 1000));

  if (s < 60) return `${s}s`;

  const m = Math.floor(s / 60);
  if (m < 60) return `${m}m ${s % 60}s`;

  const h = Math.floor(m / 60);
  return `${h}h ${m % 60}m`;
}

const sideFromType = t =>
  t === 'sell' ? 'asks' : t === 'buy' ? 'bids' : null;

function normalizeStatus(s) {
  const v = String(s || '').toLowerCase();

  if (['placed', 'modified', 'active'].includes(v)) return 'Active';
  if (['canceled', 'cancelled'].includes(v)) return 'Canceled';
  if (['filled', 'fully_filled'].includes(v)) return 'Filled';

  return s ? String(s) : 'Unknown';
}

// ---------- INDEXEDDB ----------

function openDatabase() {
  return new Promise((resolve, reject) => {
    if (!('indexedDB' in window)) {
      return reject(new Error('IndexedDB is unavailable.'));
    }

    const req = indexedDB.open(DB_NAME, DB_VERSION);

    req.onupgradeneeded = () => {
      const d = req.result;

      [
        ['orders', 'orderId'],
        ['orderEvents', 'eventKey'],
        ['trades', 'tradeId'],
        ['wallEpisodes', 'episodeId'],
        ['meta', 'key']
      ].forEach(([name, key]) => {
        if (!d.objectStoreNames.contains(name)) {
          d.createObjectStore(name, { keyPath: key });
        }
      });
    };

    req.onsuccess = () => resolve(req.result);

    req.onerror = () => reject(
      req.error || new Error('IndexedDB open failed.')
    );

    req.onblocked = () => reject(
      new Error('Close other Yeti Watch tabs and reload.')
    );
  });
}

const dbGet = (store, key) =>
  !db ? Promise.resolve(undefined) : new Promise((res, rej) => {
    const r = db.transaction(store, 'readonly')
      .objectStore(store).get(key);

    r.onsuccess = () => res(r.result);
    r.onerror = () => rej(r.error);
  });

const dbGetAll = store =>
  !db ? Promise.resolve([]) : new Promise((res, rej) => {
    const r = db.transaction(store, 'readonly')
      .objectStore(store).getAll();

    r.onsuccess = () => res(r.result || []);
    r.onerror = () => rej(r.error);
  });

const dbPutMany = (store, rows) =>
  (!db || !rows.length) ? Promise.resolve() : new Promise((res, rej) => {
    const t = db.transaction(store, 'readwrite');
    const s = t.objectStore(store);

    rows.forEach(r => s.put(r));

    t.oncomplete = () => res();
    t.onerror = () => rej(t.error);
    t.onabort = () => rej(t.error || new Error('Write aborted'));
  });

async function pruneStore(store, max, keyField, timeField) {
  const rows = await dbGetAll(store);

  if (rows.length <= max) return [];

  rows.sort((a, b) => num(b[timeField]) - num(a[timeField]));

  const gone = rows.slice(max).map(r => r[keyField]);

  await new Promise((res, rej) => {
    const t = db.transaction(store, 'readwrite');
    const s = t.objectStore(store);

    gone.forEach(k => s.delete(k));

    t.oncomplete = () => res();
    t.onerror = () => rej(t.error);
  });

  return gone;
}

async function initializeStorage() {
  try {
    db = await openDatabase();

    const [orders, events, trades, episodes] = await Promise.all([
      dbGetAll('orders'),
      dbGetAll('orderEvents'),
      dbGetAll('trades'),
      dbGetAll('wallEpisodes')
    ]);

    orders.forEach(o => trackedOrders.set(String(o.orderId), o));
    events.forEach(e => knownOrderEvents.add(e.eventKey));
    trades.forEach(t => {
      knownTradeIds.add(String(t.tradeId));
      indexMaker(t);
    });
    episodes.forEach(e => wallEpisodes.set(String(e.episodeId), e));

    console.log('Yeti Watch history restored', {
      orders: orders.length,
      events: events.length,
      trades: trades.length,
      episodes: episodes.length
    });

  } catch (e) {
    db = null;

    console.warn(
      'Yeti Watch: storage unavailable, tracking this session only.',
      e
    );

  } finally {
    storageReady = true;
  }
}

// ---------- API ----------

async function getJSON(path) {
  const c = new AbortController();
  const timer = setTimeout(
    () => c.abort(),
    REQUEST_TIMEOUT_MS
  );

  try {
    const r = await fetch(`${API}${path}`, {
      signal: c.signal
    });

    if (!r.ok) {
      throw new Error(`Indexer HTTP ${r.status}: ${path}`);
    }

    const body = await r.json();

    if (
      body &&
      typeof body === 'object' &&
      Array.isArray(body.value)
    ) {
      return body.value;
    }

    return body;

  } catch (e) {
    throw e.name === 'AbortError'
      ? new Error(`Indexer request timed out: ${path}`)
      : e;

  } finally {
    clearTimeout(timer);
  }
}

async function fetchCompleteTimeRange(
  endpoint,
  start,
  end,
  depth = 0
) {
  const q = new URLSearchParams({
    start_time: String(start),
    end_time: String(end),
    limit: String(API_LIMIT)
  });

  const rows = await getJSON(`/${endpoint}/${POOL}?${q}`);

  if (!Array.isArray(rows)) {
    throw new Error(`Unexpected ${endpoint} response.`);
  }

  if (rows.length < API_LIMIT) {
    return { rows, complete: true, saturated: 0 };
  }

  if (start >= end || depth >= MAX_SPLIT_DEPTH) {
    console.warn(
      `Yeti Watch: ${endpoint} hit its result limit.`,
      { start, end, depth }
    );

    return { rows, complete: false, saturated: 1 };
  }

  const mid = Math.floor((start + end) / 2);

  const a = await fetchCompleteTimeRange(
    endpoint, start, mid, depth + 1
  );

  const b = await fetchCompleteTimeRange(
    endpoint, mid + 1, end, depth + 1
  );

  return {
    rows: [...a.rows, ...b.rows],
    complete: a.complete && b.complete,
    saturated: a.saturated + b.saturated
  };
}

const normalizeLevels = lv =>
  lv.map(([p, q]) => ({
    price: Number(p),
    quantity: Number(q)
  })).filter(l =>
    Number.isFinite(l.price) &&
    Number.isFinite(l.quantity)
  );

async function fetchMarketBook() {
  const raw = await getJSON(
    `/orderbook/${POOL}?level=2&depth=${BOOK_DEPTH}`
  );

  const book = {
    asks: normalizeLevels(raw.asks || []),
    bids: normalizeLevels(raw.bids || [])
  };

  if (!book.asks.length || !book.bids.length) {
    throw new Error('Order book is empty.');
  }

  book.asks.sort((a, b) => a.price - b.price);
  book.bids.sort((a, b) => b.price - a.price);

  return book;
}

// ---------- INDIVIDUAL ORDERS ----------

const eventKey = e => [
  e.event_digest || e.digest || '',
  e.order_id,
  e.status,
  e.timestamp,
  e.original_quantity ?? '',
  e.filled_quantity ?? '',
  e.remaining_quantity ?? '',
  e.price ?? ''
].join('|');

function createOrder(e, side) {
  const orig = num(
    e.original_quantity,
    num(e.remaining_quantity)
  );

  const t = normalizeTimestampMs(e.timestamp, Date.now());

  return {
    orderId: String(e.order_id),
    side,
    price: num(e.price),
    originalQuantity: orig,
    reportedFilled: 0,
    matchedVolume: 0,
    matchedTradeIds: [],
    filledQuantity: 0,
    remainingQuantity: num(e.remaining_quantity, orig),
    cancelledQuantity: 0,
    status: 'Active',
    firstSeen: t,
    lastUpdatedAt: t,
    completedAt: null
  };
}

function refresh(o) {
  const orig = o.originalQuantity;

  // Order updates and trades can describe the same fill.
  // Use the larger cumulative figure, never add them together.
  o.filledQuantity = Math.min(
    orig || Infinity,
    Math.max(o.reportedFilled, o.matchedVolume)
  );

  if (o.status === 'Filled') {
    if (orig) o.filledQuantity = orig;

    o.remainingQuantity = 0;
    o.cancelledQuantity = 0;

  } else if (o.status === 'Canceled') {
    o.remainingQuantity = 0;

    o.cancelledQuantity = Math.max(
      0,
      orig - o.filledQuantity
    );

  } else {
    o.cancelledQuantity = 0;

    o.remainingQuantity = Math.max(
      0,
      orig - o.filledQuantity
    );

    if (
      orig > 0 &&
      o.filledQuantity >= orig * 0.999
    ) {
      o.status = 'Filled';
      o.completedAt = o.lastUpdatedAt;
      o.remainingQuantity = 0;
    }
  }
}

// ---------- TRADES: MAKER ORDER ONLY ----------

function indexMaker(t) {
  if (!t.makerOrderId) return;

  if (!makerTrades.has(t.makerOrderId)) {
    makerTrades.set(t.makerOrderId, new Map());
  }

  makerTrades.get(t.makerOrderId).set(
    String(t.tradeId),
    t
  );
}

function applyTrade(o, t) {
  if (o.matchedTradeIds.includes(String(t.tradeId))) {
    return false;
  }

  o.matchedTradeIds.push(String(t.tradeId));
  o.matchedVolume += t.baseVolume;

  refresh(o);

  return true;
}

function backfill(o) {
  const m = makerTrades.get(o.orderId);

  if (m) {
    m.forEach(t => applyTrade(o, t));
  }
}

// ---------- PROCESS ORDER UPDATES ----------

function processOrderUpdates(updates) {
  const rows = [...updates].sort(
    (a, b) => normalizeTimestampMs(a.timestamp) - normalizeTimestampMs(b.timestamp)
  );

  const changed = new Set();
  const newKeys = [];

  for (const e of rows) {
    if (!e.order_id || !e.status) continue;

    const key = eventKey(e);

    if (knownOrderEvents.has(key)) continue;

    const id = String(e.order_id);
    let o = trackedOrders.get(id);

    if (!o) {
      const side = sideFromType(e.type);

      const size = num(
        e.original_quantity,
        num(e.remaining_quantity)
      );

      if (!side || size < TRACK_MIN) continue;

      o = createOrder(e, side);
      trackedOrders.set(id, o);
    }

    const t = normalizeTimestampMs(e.timestamp, Date.now());

    if (t >= o.lastUpdatedAt) {
      const p = num(e.price, NaN);

      if (Number.isFinite(p)) {
        o.price = p;
      }

      if (num(e.original_quantity) > 0) {
        o.originalQuantity = num(e.original_quantity);
      }

      if (e.filled_quantity !== undefined) {
        o.reportedFilled = Math.max(
          o.reportedFilled,
          num(e.filled_quantity)
        );
      }

      const s = normalizeStatus(e.status);

      if (s === 'Canceled' || s === 'Filled') {
        o.status = s;
        o.completedAt = t;

      } else if (
        s === 'Active' &&
        o.status !== 'Canceled' &&
        o.status !== 'Filled'
      ) {
        o.status = 'Active';
        o.completedAt = null;
      }

      o.lastUpdatedAt = t;

      backfill(o);
      refresh(o);
    }

    knownOrderEvents.add(key);
    newKeys.push({ eventKey: key, timestamp: t });
    changed.add(o);
  }

  return { changed, newKeys };
}

// ---------- PROCESS TRADES ----------

function processTrades(trades) {
  const rows = [...trades].sort(
    (a, b) => normalizeTimestampMs(a.timestamp) - normalizeTimestampMs(b.timestamp)
  );

  const fresh = [];
  const changed = new Set();

  for (const t of rows) {
    const id = String(t.trade_id || '');

    if (!id || knownTradeIds.has(id)) continue;

    const vol = num(t.base_volume);

    if (vol <= 0) continue;

    const rec = {
      tradeId: id,
      timestamp: normalizeTimestampMs(t.timestamp, Date.now()),
      makerOrderId: String(t.maker_order_id || ''),
      baseVolume: vol,
      price: num(t.price)
    };

    knownTradeIds.add(id);
    fresh.push(rec);
    indexMaker(rec);

    const o = trackedOrders.get(rec.makerOrderId);

    if (o && applyTrade(o, rec)) {
      changed.add(o);
    }
  }

  return { fresh, changed };
}

// ---------- LIFECYCLE SCAN ----------

async function getScanStart(now) {
  const cp = await dbGet('meta', 'lastScanSecond');

  if (!cp || !Number.isFinite(Number(cp.value))) {
    return Math.max(0, now - INITIAL_LOOKBACK_SECONDS);
  }

  return Math.max(
    0,
    Math.min(now, Number(cp.value)) - OVERLAP_SECONDS
  );
}

async function fetchAndProcessLifecycle(now) {
  const start = await getScanStart(now);

  const [u, t] = await Promise.all([
    fetchCompleteTimeRange('order_updates', start, now),
    fetchCompleteTimeRange('trades', start, now)
  ]);

  const up = processOrderUpdates(u.rows);
  const tr = processTrades(t.rows);

  const changed = new Set([
    ...up.changed,
    ...tr.changed
  ]);

  await dbPutMany('orders', [...changed]);
  await dbPutMany('orderEvents', up.newKeys);
  await dbPutMany('trades', tr.fresh);

  const complete = u.complete && t.complete;

  if (complete) {
    await dbPutMany('meta', [
      { key: 'lastScanSecond', value: now }
    ]);
  }

  return {
    newEvents: up.newKeys.length,
    newTrades: tr.fresh.length,
    changed: changed.size,
    complete,
    saturated: u.saturated + t.saturated
  };
}

// ---------- GROUP ORDERS BY SIDE AND PRICE ----------

const priceKey = o =>
  `${o.side}|${Number(o.price).toFixed(8)}`;

function groupOrders() {
  const cutoff = Date.now() - HISTORY_MS;
  const m = new Map();

  for (const o of trackedOrders.values()) {
    if (
      o.status !== 'Active' &&
      normalizeTimestampMs(o.lastUpdatedAt) < cutoff
    ) {
      continue;
    }

    const k = priceKey(o);
    let g = m.get(k);

    if (!g) {
      g = {
        side: o.side,
        price: o.price,
        n: 0,
        open: 0,
        openQty: 0,
        orig: 0,
        filled: 0,
        cxNoFill: 0,
        cxPartial: 0,
        openFirst: Infinity,
        last: 0
      };

      m.set(k, g);
    }

    g.n++;
    g.orig += o.originalQuantity;
    g.filled += o.filledQuantity;
    g.last = Math.max(g.last, normalizeTimestampMs(o.lastUpdatedAt));

    if (o.status === 'Active') {
      g.open++;
      g.openQty += o.remainingQuantity;
      g.openFirst = Math.min(
        g.openFirst,
        normalizeTimestampMs(o.firstSeen, normalizeTimestampMs(o.lastUpdatedAt))
      );

    } else if (o.status === 'Canceled') {
      if (o.filledQuantity > 0) {
        g.cxPartial += o.cancelledQuantity;
      } else {
        g.cxNoFill += o.cancelledQuantity;
      }
    }
  }

  return m;
}

// ---------- UI ----------

function addCard(title, status, cls, lines) {
  const c = document.createElement('div');
  c.className = 'wall-card';

  const h = document.createElement('div');
  h.className = 'wall-card-heading';

  const a = document.createElement('strong');
  a.textContent = title;

  const b = document.createElement('span');
  b.className = cls;
  b.textContent = status;

  if (cls === 'wall-mixed') {
    b.style.color = '#b7791f';
  }

  h.append(a, b);

  const d = document.createElement('div');
  d.className = 'wall-details';

  lines.forEach(t => {
    const s = document.createElement('span');
    s.textContent = t;
    d.appendChild(s);
  });

  c.append(h, d);
  elements.wallList.appendChild(c);
}

// ---------- CORRECTED WALL MONITOR ----------

function renderWallMonitor() {
  if (!elements.wallList || !elements.wallCount) return;

  rebuildWallEpisodes();

  const groups = groupOrders();

  // Current walls from the live order book.
  const levels = latestBook
    ? ['asks', 'bids'].flatMap(side =>
        latestBook[side]
          .filter(level => level.quantity >= WALL_MIN[side])
          .map(level => ({
            side,
            price: level.price,
            qty: level.quantity
          }))
      )
    : [];

  levels.sort((a, b) => b.qty - a.qty);

  // Keep historical activity separate from current walls.
  // A historical event at a price is not hidden just because
  // a new wall currently exists at that same price.
  const outcomes = [...wallEpisodes.values()]
    .filter(g => {
      const cancelled = g.cxNoFill + g.cxPartial;

      return (
        g.orig >= WALL_MIN[g.side] &&
        (
          cancelled > 0 ||
          g.filled > 0
        )
      );
    })
    .sort((a, b) => b.last - a.last)
    .slice(0, 8);

  elements.wallCount.textContent =
    `${levels.length} open walls · ${trackedOrders.size} orders seen`;

  elements.wallList.innerHTML = '';

  // 1. CURRENT WALLS

  levels.slice(0, 6).forEach(l => {
    const g = groups.get(priceKey(l));

    const seen = g
      ? Math.min(
          100,
          Math.round(100 * g.openQty / l.qty)
        )
      : 0;

    const lines = [
      `Price: ${formatPrice(l.price)}`,
      `On the book: ${formatQty(l.qty)} SUI`,
      g
        ? `Orders Yeti saw here: ${g.open} active (${formatQty(g.openQty)} SUI still open)`
        : 'No individual active orders tracked at this price',
      `Tracked liquidity coverage: ${seen}%`
    ];

    if (g && g.filled > 0) {
      lines.push(
        `Executed: ${formatQty(g.filled)} SUI`
      );
    }

    if (g && g.cxNoFill > 0) {
      lines.push(
        `Cancelled without a fill: ${formatQty(g.cxNoFill)} SUI`
      );
    }

    if (g && g.cxPartial > 0) {
      lines.push(
        `Cancelled after partial fills: ${formatQty(g.cxPartial)} SUI`
      );
    }

    if (g && g.open > 0 && Number.isFinite(g.openFirst)) {
      lines.push(
        `Longest active order: ${formatDurationSince(g.openFirst)} open`
      );
    }

    addCard(
      l.side === 'asks' ? 'Sell wall' : 'Buy wall',
      'Open',
      'wall-active',
      lines
    );
  });

  // 2. HISTORICAL WALL OUTCOMES

  outcomes.forEach(g => {
    const cancelled = g.cxNoFill + g.cxPartial;

    let label;
    let cls;

    if (g.openQty > 0 && cancelled > 0) {
      label = 'Part cancelled, rest open';
      cls = 'wall-mixed';

    } else if (
      g.openQty === 0 &&
      g.filled > 0 &&
      cancelled > 0
    ) {
      label = 'Part filled, rest cancelled';
      cls = 'wall-mixed';

    } else if (
      g.openQty === 0 &&
      g.filled === 0 &&
      g.cxNoFill > 0
    ) {
      label = 'Cancelled, no fill';
      cls = 'wall-suspected';

    } else if (
      g.openQty === 0 &&
      g.filled > 0 &&
      cancelled === 0
    ) {
      label = 'Fully executed';
      cls = 'wall-filled';

    } else if (
      g.openQty > 0 &&
      g.filled > 0
    ) {
      label = 'Partly filled, rest open';
      cls = 'wall-mixed';

    } else {
      label = 'Historical activity';
      cls = 'wall-active';
    }

    const lines = [
      `Price: ${formatPrice(g.price)}`,
      `Orders observed: ${g.n}`,
      `Total order quantity: ${formatQty(g.orig)} SUI`,
      `Executed: ${formatQty(g.filled)} SUI`
    ];

    if (g.cxNoFill > 0) {
      lines.push(
        `Cancelled without a fill: ${formatQty(g.cxNoFill)} SUI`
      );
    }

    if (g.cxPartial > 0) {
      lines.push(
        `Cancelled after partial fills: ${formatQty(g.cxPartial)} SUI`
      );
    }

    if (g.openQty > 0) {
      lines.push(
        `Still open: ${formatQty(g.openQty)} SUI`
      );
    }

    if (g.open > 0 && Number.isFinite(g.openFirst)) {
      lines.push(
        `Longest active order: ${formatDurationSince(g.openFirst)} open`
      );
    }

    lines.push(
      `Last change: ${formatAge(g.last)} ago`
    );

    addCard(
      g.side === 'asks'
        ? 'Sell wall · History'
        : 'Buy wall · History',
      label,
      cls,
      lines
    );
  });

  // 3. EMPTY STATE

  if (!levels.length && !outcomes.length) {
    const p = document.createElement('p');
    p.className = 'book-loading';

    p.textContent = storageReady
      ? 'Watching for large price levels...'
      : 'Starting local order tracker...';

    elements.wallList.appendChild(p);

  } else {
    // No extra status paragraph when wall cards are present.
  }

  // 4. CANCELLED WITHOUT FILL METRIC

  if (elements.trustScore) {
    if (!lifecyclePolls) {
      elements.trustScore.textContent = '--';
    } else if (latestLifecycleIncomplete) {
      elements.trustScore.textContent = 'Incomplete';
    } else {
      const total = [...groups.values()]
        .reduce((s, g) => s + g.cxNoFill, 0);

      elements.trustScore.textContent = `${compact(total)} SUI`;
    }
  }
}

// ---------- ORDER BOOK DISPLAY ----------

function renderSide(container, rows, side) {
  if (!container) return;

  const max = Math.max(
    ...rows.map(r => r.quantity),
    1
  );

  container.innerHTML = '';

  for (const r of rows) {
    const row = document.createElement('div');

    row.className =
      `book-row ${side === 'asks' ? 'ask' : 'bid'}`;

    const big = r.quantity >= WALL_MIN[side];

    if (big) {
      row.classList.add('wall');
      row.title = 'This price level is above the wall size.';
    }

    const bar = document.createElement('div');
    bar.className = 'depth-bar';
    bar.style.width = `${(r.quantity / max) * 100}%`;

    const p = document.createElement('span');
    p.className = 'order-price';
    p.textContent = formatPrice(r.price);

    const q = document.createElement('span');
    q.className = 'order-quantity';
    q.textContent = formatQty(r.quantity);

    row.append(bar, p, q);

    if (big) {
      const tag = document.createElement('span');
      tag.className = 'wall-tag';
      tag.textContent = 'WALL';
      row.appendChild(tag);
    }

    container.appendChild(row);
  }
}

function renderOrderBook(book) {
  if (!book.asks.length || !book.bids.length) return;

  const bestAsk = book.asks[0].price;
  const bestBid = book.bids[0].price;

  if (elements.price) {
    elements.price.textContent = formatPrice(
      (bestAsk + bestBid) / 2
    );
  }

  if (elements.spread) {
    elements.spread.textContent = formatPrice(
      bestAsk - bestBid
    );
  }

  // Asks: lowest price first.
  renderSide(
    elements.asks,
    [...book.asks]
      .sort((a, b) => a.price - b.price)
      .slice(0, DEPTH),
    'asks'
  );

  // Bids: highest price first.
  renderSide(
    elements.bids,
    [...book.bids]
      .sort((a, b) => b.price - a.price)
      .slice(0, DEPTH),
    'bids'
  );
}

// ---------- POLLING ----------

async function fetchMarketData() {
  if (marketBusy) return;

  marketBusy = true;

  try {
    latestBook = await fetchMarketBook();
    renderOrderBook(latestBook);

  } catch (e) {
    console.error(
      'Yeti Watch market update failed:',
      e
    );

  } finally {
    marketBusy = false;
  }
}

async function fetchLifecycleData() {
  if (lifecycleBusy || !storageReady) return;

  lifecycleBusy = true;

  try {
    const r = await fetchAndProcessLifecycle(
      Math.floor(Date.now() / 1000)
    );

    latestLifecycleComplete = r.complete;
    latestLifecycleIncomplete = !r.complete || r.saturated > 0;

    lifecyclePolls++;

    renderWallMonitor();

    console.log('Yeti Watch tracking update', {
      openOrders: [...trackedOrders.values()]
        .filter(o => o.status === 'Active').length,

      trackedOrders: trackedOrders.size,
      newOrderEvents: r.newEvents,
      newTrades: r.newTrades,

      scanComplete: r.complete,
      saturatedRanges: r.saturated
    });

    if (db && lifecyclePolls % 20 === 0) {
      // Do not delete active orders from local tracking.
      const oldOrders = [...trackedOrders.values()]
        .filter(o =>
          o.status !== 'Active' &&
          o.lastUpdatedAt < Date.now() - HISTORY_MS
        );

      // Keep pruning limited to old completed orders.
      if (trackedOrders.size > MAX_TRACKED_ORDERS) {
        const excess = trackedOrders.size - MAX_TRACKED_ORDERS;

        oldOrders
          .sort((a, b) => a.lastUpdatedAt - b.lastUpdatedAt)
          .slice(0, excess)
          .forEach(o => {
            trackedOrders.delete(String(o.orderId));
          });
      }

      await pruneStore(
        'orderEvents',
        MAX_ORDER_EVENTS,
        'eventKey',
        'timestamp'
      );

      await pruneStore(
        'trades',
        MAX_SAVED_TRADES,
        'tradeId',
        'timestamp'
      );
    }

  } catch (e) {
    latestLifecycleComplete = false;
    latestLifecycleIncomplete = true;
    console.error(
      'Yeti Watch lifecycle update failed:',
      e
    );

  } finally {
    lifecycleBusy = false;
  }
}

// ---------- START YETI WATCH ----------

function startYetiWatch() {
  fetchMarketData();

  setInterval(
    fetchMarketData,
    MARKET_POLL_MS
  );

  setInterval(
    renderWallMonitor,
    1000
  );

  initializeStorage().finally(() => {
    renderWallMonitor();

    fetchLifecycleData();

    setInterval(
      fetchLifecycleData,
      LIFECYCLE_POLL_MS
    );
  });
}

startYetiWatch();

function rebuildWallEpisodes() {
  const cutoff = Date.now() - HISTORY_MS;
  const eligible = [...trackedOrders.values()].filter(o =>
    o.status === 'Active' || normalizeTimestampMs(o.lastUpdatedAt) >= cutoff
  ).sort((a, b) => normalizeTimestampMs(a.firstSeen) - normalizeTimestampMs(b.firstSeen));

  const next = new Map();

  for (const o of eligible) {
    const base = `${o.side}|${Number(o.price).toFixed(8)}`;
    const candidates = [...next.values()].filter(e =>
      e.side === o.side &&
      Number(e.price).toFixed(8) === Number(o.price).toFixed(8)
    );

    let episode = candidates
      .filter(e => {
        const gap = normalizeTimestampMs(o.firstSeen) - normalizeTimestampMs(e.last);
        return gap >= -EPISODE_GAP_MS && gap <= EPISODE_GAP_MS;
      })
      .sort((a, b) => b.last - a.last)[0];

    if (!episode) {
      const first = normalizeTimestampMs(o.firstSeen);
      episode = {
        episodeId: `${base}|${first}|${o.orderId}`,
        side: o.side,
        price: o.price,
        n: 0,
        open: 0,
        openQty: 0,
        orig: 0,
        filled: 0,
        cxNoFill: 0,
        cxPartial: 0,
        openFirst: Infinity,
        last: first
      };
      next.set(episode.episodeId, episode);
    }

    episode.n++;
    episode.orig += num(o.originalQuantity);
    episode.filled += num(o.filledQuantity);
    episode.last = Math.max(episode.last, normalizeTimestampMs(o.lastUpdatedAt));

    if (o.status === 'Active') {
      episode.open++;
      episode.openQty += num(o.remainingQuantity);
      episode.openFirst = Math.min(
        episode.openFirst,
        normalizeTimestampMs(o.firstSeen, normalizeTimestampMs(o.lastUpdatedAt))
      );

    } else if (o.status === 'Canceled') {
      if (num(o.filledQuantity) > 0) {
        episode.cxPartial += num(o.cancelledQuantity);
      } else {
        episode.cxNoFill += num(o.cancelledQuantity);
      }
    }
  }

  wallEpisodes.clear();
  next.forEach((episode, id) => wallEpisodes.set(id, episode));

  if (db) {
    dbPutMany('wallEpisodes', [...wallEpisodes.values()]).catch(e =>
      console.warn('Yeti Watch could not persist wall episodes:', e)
    );
  }

  return wallEpisodes;
}
