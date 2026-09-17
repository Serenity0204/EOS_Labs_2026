/*
 * Overbug playable demo for the RTES913 course site.
 *
 * This is a browser port of the course's own programs:
 *   - Lab2/server.c        -> game rules, station behaviour, order scoring
 *   - Lab2/overbug_world.h -> the 16-facility map (coordinates copied verbatim)
 *   - Lab2/display.py      -> every colour and glyph drawn below
 *   - Lab3/player.py       -> the keyboard bindings for players 1-4
 *
 * It implements the LAB 4 target rules, not the Lab 2 starter: the round counts
 * down, a welder needs 2000 ms of held Solder, and a verifier takes 4000 ms on
 * its own. The simulation advances in fixed 50 ms steps exactly as Lab 4
 * requires, so on-screen motion is 20 Hz just like the real server.
 */
(function () {
  "use strict";

  /* ------------------------------------------------------------------ *
   * Constants (server.c)
   * ------------------------------------------------------------------ */
  var W = 1280;
  var H = 720;
  var MAP_X = 70, MAP_Y = 96, MAP_W = 1140, MAP_H = 540;

  var PLAYER_RADIUS = 18.0;
  var PLAYER_SPEED = 185.0;
  var INTERACT_DISTANCE = 54.0;

  var ROUND_MS = 180000;
  var SOLDER_MS = 2000;
  var INSPECTION_MS = 4000;
  var TICK_MS = 50;
  var ORDER_COUNT = 3;

  var BTN_UP = 0x01, BTN_DOWN = 0x02, BTN_LEFT = 0x04,
      BTN_RIGHT = 0x08, BTN_ACTION = 0x10, BTN_SOLDER = 0x20;

  var COMPONENTS = ["resistor", "capacitor", "inductor"];

  /* overbug_world.h, OB_FACILITY_LAYOUT -- coordinates copied verbatim.
     `type` uses display.py's spelling so the renderer matches too. */
  var FACILITIES = [
    { id: "bin_resistor",  type: "material_bin",          x: 92,   y: 160, w: 92,  h: 62, component: "resistor" },
    { id: "bin_capacitor", type: "material_bin",          x: 92,   y: 246, w: 92,  h: 62, component: "capacitor" },
    { id: "bin_inductor",  type: "material_bin",          x: 92,   y: 332, w: 92,  h: 62, component: "inductor" },
    { id: "trash",         type: "trash",                 x: 92,   y: 542, w: 112, h: 68 },
    { id: "intake",        type: "intake",                x: 1058, y: 542, w: 112, h: 68 },
    { id: "shipping",      type: "shipping",              x: 1092, y: 286, w: 92,  h: 84 },
    { id: "welder_1",      type: "welder",                x: 304,  y: 542, w: 132, h: 68 },
    { id: "welder_2",      type: "welder",                x: 474,  y: 542, w: 132, h: 68 },
    { id: "welder_3",      type: "welder",                x: 574,  y: 118, w: 132, h: 68 },
    { id: "verifier_1",    type: "verification_computer", x: 786,  y: 118, w: 136, h: 68 },
    { id: "verifier_2",    type: "verification_computer", x: 954,  y: 118, w: 136, h: 68 },
    { id: "table_1",       type: "table",                 x: 230,  y: 118, w: 100, h: 60 },
    { id: "table_2",       type: "table",                 x: 354,  y: 118, w: 100, h: 60 },
    { id: "table_3",       type: "table",                 x: 646,  y: 542, w: 100, h: 68 },
    { id: "table_4",       type: "table",                 x: 776,  y: 542, w: 100, h: 68 },
    { id: "table_5",       type: "table",                 x: 906,  y: 542, w: 100, h: 68 }
  ];

  /* Lab 2 spawns player 1 at (560, 370). The extra spawns sit on the same
     open strip of floor, clear of every facility rectangle. */
  var SPAWNS = [
    { x: 560, y: 370 }, { x: 620, y: 370 },
    { x: 500, y: 370 }, { x: 680, y: 370 }
  ];

  /* display.py COLORS */
  var C = {
    bg: "rgb(238,243,249)", floor: "rgb(225,235,244)", tile: "rgb(210,224,237)",
    counter: "rgb(248,250,252)", line: "rgb(131,150,169)", ink: "rgb(34,49,64)",
    muted: "rgb(96,112,128)", red: "rgb(224,86,86)", green: "rgb(75,176,112)",
    blue: "rgb(72,134,220)", purple: "rgb(139,103,206)", gold: "rgb(246,193,84)",
    accent: "rgb(38,166,154)"
  };

  var STATION_FILL = {
    material_bin: "rgb(233,247,243)",
    welder: "rgb(255,247,224)",
    verification_computer: "rgb(232,242,255)",
    shipping: "rgb(230,248,234)",
    trash: "rgb(252,233,233)",
    intake: "rgb(238,236,252)",
    table: C.counter
  };

  var PLAYER_COLORS = [
    "rgb(230,89,82)", "rgb(74,144,226)", "rgb(72,174,112)", "rgb(143,105,210)"
  ];

  /* ------------------------------------------------------------------ *
   * glibc rand(), so srand(7) yields the same orders as the C server.
   * Verified byte-for-byte against gcc output for the first 24 draws.
   * ------------------------------------------------------------------ */
  function GlibcRandom(seed) {
    var r = new Array(344);
    var word = seed | 0;
    if (word === 0) word = 1;
    r[0] = word;
    for (var i = 1; i < 31; i++) {
      var hi = Math.trunc(word / 127773);
      var lo = word % 127773;
      word = 16807 * lo - 2836 * hi;
      if (word < 0) word += 2147483647;
      r[i] = word;
    }
    for (i = 31; i < 34; i++) r[i] = r[i - 31];
    for (i = 34; i < 344; i++) r[i] = (r[i - 31] + r[i - 3]) | 0;
    var n = 344;
    this.next = function () {
      var v = (r[n - 31] + r[n - 3]) | 0;
      r[n] = v;
      n++;
      return v >>> 1;
    };
  }

  /* ------------------------------------------------------------------ *
   * Items (server.c: struct item / struct board)
   * ------------------------------------------------------------------ */
  function makeMaterial(component) {
    return { kind: "material", component: component };
  }

  function isBoard(item) { return !!item && item.kind === "board"; }

  function boardCanEnterWelder(state) {
    return state === "raw" || state === "soldering" || state === "ready_to_test";
  }

  /* ------------------------------------------------------------------ *
   * Geometry (server.c)
   * ------------------------------------------------------------------ */
  function clampf(v, lo, hi) { return v < lo ? lo : (v > hi ? hi : v); }

  function distanceToRect(px, py, st) {
    var cx = clampf(px, st.x, st.x + st.w);
    var cy = clampf(py, st.y, st.y + st.h);
    var dx = px - cx, dy = py - cy;
    return Math.sqrt(dx * dx + dy * dy);
  }

  /* ------------------------------------------------------------------ *
   * Game
   * ------------------------------------------------------------------ */
  function Game(playerCount) {
    this.rng = new GlibcRandom(7);          /* server.c: srand(7) */
    this.nextOrderId = 1;
    this.nextBoardId = 1;
    this.score = 0;
    this.completed = 0;
    this.recycled = 0;
    this.remainingMs = ROUND_MS;
    this.gameOver = false;

    this.stations = FACILITIES.map(function (f) {
      return {
        id: f.id, type: f.type, x: f.x, y: f.y, w: f.w, h: f.h,
        component: f.component || null,
        item: null,               /* table + verifier */
        board: null,              /* welder */
        pendingMaterial: null,    /* welder */
        remainingMs: 0
      };
    });

    this.players = [];
    for (var i = 0; i < playerCount; i++) {
      this.players.push({
        id: i + 1,
        x: SPAWNS[i].x, y: SPAWNS[i].y,
        inputMask: 0, prevInputMask: 0,
        held: null
      });
    }

    this.orders = [];
    for (i = 0; i < ORDER_COUNT; i++) this.orders.push(this.generateOrder());
  }

  Game.prototype.generateOrder = function () {
    var req, total;
    do {
      req = [this.rng.next() % 3, this.rng.next() % 3, this.rng.next() % 3];
      total = req[0] + req[1] + req[2];
    } while (total < 1 || total > 4);
    return { id: this.nextOrderId++, req: req, lockedBoardId: 0 };
  };

  Game.prototype.makeBoard = function () {
    return {
      kind: "board", boardId: this.nextBoardId++, state: "raw",
      counts: [0, 0, 0], lockedOrderId: 0
    };
  };

  Game.prototype.nearestStation = function (p) {
    var best = null, bestD = INTERACT_DISTANCE;
    for (var i = 0; i < this.stations.length; i++) {
      var d = distanceToRect(p.x, p.y, this.stations[i]);
      if (d < bestD) { bestD = d; best = this.stations[i]; }
    }
    return best;
  };

  Game.prototype.playerHitsStation = function (p) {
    for (var i = 0; i < this.stations.length; i++) {
      if (distanceToRect(p.x, p.y, this.stations[i]) < PLAYER_RADIUS) return true;
    }
    return false;
  };

  Game.prototype.pickFromStation = function (st) {
    var picked;
    switch (st.type) {
      case "material_bin":
        return makeMaterial(st.component);
      case "intake":
        return this.makeBoard();
      case "table":
        picked = st.item; st.item = null; return picked;
      case "welder":
        if (!st.pendingMaterial && isBoard(st.board)) {
          picked = st.board; st.board = null; st.remainingMs = SOLDER_MS;
          return picked;
        }
        break;
      case "verification_computer":
        if (isBoard(st.item) && (st.item.state === "passed" || st.item.state === "failed")) {
          picked = st.item; st.item = null; st.remainingMs = INSPECTION_MS;
          return picked;
        }
        break;
      default:
        break;
    }
    return null;
  };

  Game.prototype.findMatchingOrder = function (board) {
    for (var i = 0; i < this.orders.length; i++) {
      var o = this.orders[i];
      if (o.lockedBoardId !== 0) continue;
      if (o.req[0] === board.counts[0] &&
          o.req[1] === board.counts[1] &&
          o.req[2] === board.counts[2]) return i;
    }
    return -1;
  };

  Game.prototype.findOrderById = function (orderId) {
    for (var i = 0; i < this.orders.length; i++) {
      if (this.orders[i].id === orderId) return i;
    }
    return -1;
  };

  Game.prototype.dropToWelder = function (st, item) {
    if (item.kind === "board") {
      if (!st.board && boardCanEnterWelder(item.state)) {
        item.state = "soldering";
        st.board = item;
        st.remainingMs = SOLDER_MS;
        return true;
      }
      return false;
    }
    if (item.kind === "material") {
      if (isBoard(st.board) && !st.pendingMaterial) {
        st.pendingMaterial = item;
        st.remainingMs = SOLDER_MS;
        return true;
      }
    }
    return false;
  };

  /* Lab 4 change: the verifier stores the board and starts a 4000 ms timer.
     The pass/fail decision happens in finishVerify(), not here. */
  Game.prototype.dropToVerifier = function (st, item) {
    if (item.kind !== "board" || st.item) return false;
    if (!boardCanEnterWelder(item.state)) return false;
    st.item = item;
    st.remainingMs = INSPECTION_MS;
    return true;
  };

  Game.prototype.shipItem = function (item) {
    if (item.kind !== "board" || item.state !== "passed" || item.lockedOrderId === 0) {
      return false;
    }
    var index = this.findOrderById(item.lockedOrderId);
    if (index < 0) return false;
    if (this.orders[index].lockedBoardId !== item.boardId) return false;

    var o = this.orders[index];
    this.score += 10 + (o.req[0] + o.req[1] + o.req[2]) * 5;
    this.completed += 1;
    this.orders[index] = this.generateOrder();
    return true;
  };

  Game.prototype.dropToStation = function (st, item) {
    switch (st.type) {
      case "table":
        if (!st.item) { st.item = item; return true; }
        return false;
      case "welder":
        return this.dropToWelder(st, item);
      case "verification_computer":
        return this.dropToVerifier(st, item);
      case "shipping":
        return this.shipItem(item);
      case "trash":
        if (item.kind === "board" && item.lockedOrderId !== 0) return false;
        this.recycled += 1;
        return true;
      default:
        return false;
    }
  };

  Game.prototype.interact = function (p) {
    var st = this.nearestStation(p);
    if (!st) return;
    if (!p.held) {
      p.held = this.pickFromStation(st);
    } else if (this.dropToStation(st, p.held)) {
      p.held = null;
    }
  };

  Game.prototype.movePlayer = function (p, dt) {
    var oldX = p.x, oldY = p.y, dx = 0, dy = 0;

    if (p.inputMask & BTN_LEFT)  dx -= 1;
    if (p.inputMask & BTN_RIGHT) dx += 1;
    if (p.inputMask & BTN_UP)    dy -= 1;
    if (p.inputMask & BTN_DOWN)  dy += 1;

    var len = Math.sqrt(dx * dx + dy * dy);
    if (len > 0) { dx /= len; dy /= len; }

    p.x += dx * PLAYER_SPEED * dt;
    p.y += dy * PLAYER_SPEED * dt;
    p.x = clampf(p.x, MAP_X + PLAYER_RADIUS, MAP_X + MAP_W - PLAYER_RADIUS);
    p.y = clampf(p.y, MAP_Y + PLAYER_RADIUS, MAP_Y + MAP_H - PLAYER_RADIUS);

    if (this.playerHitsStation(p)) { p.x = oldX; p.y = oldY; }
  };

  Game.prototype.finishWeld = function (st) {
    var idx = COMPONENTS.indexOf(st.pendingMaterial.component);
    if (idx >= 0) st.board.counts[idx] += 1;
    st.board.state = "ready_to_test";
    st.pendingMaterial = null;
    st.remainingMs = SOLDER_MS;
  };

  Game.prototype.finishVerify = function (st) {
    var index = this.findMatchingOrder(st.item);
    if (index >= 0) {
      st.item.state = "passed";
      st.item.lockedOrderId = this.orders[index].id;
      this.orders[index].lockedBoardId = st.item.boardId;
    } else {
      st.item.state = "failed";
    }
    st.remainingMs = INSPECTION_MS;
  };

  /* One fixed 50 ms game step (Lab 4 timing design). */
  Game.prototype.step = function () {
    var i, p, st;

    if (this.gameOver) {
      /* "End the game and stop all movement and machine work, but keep
         sending game updates." Input edges are still consumed so a held
         button does not fire the instant a new round starts. */
      for (i = 0; i < this.players.length; i++) {
        this.players[i].prevInputMask = this.players[i].inputMask;
      }
      return;
    }

    var dt = TICK_MS / 1000;

    for (i = 0; i < this.players.length; i++) {
      p = this.players[i];
      this.movePlayer(p, dt);

      var actionNow = (p.inputMask & BTN_ACTION) !== 0;
      var actionBefore = (p.prevInputMask & BTN_ACTION) !== 0;
      if (actionNow && !actionBefore) this.interact(p);

      p.prevInputMask = p.inputMask;
    }

    /* Welders: count down only while a player who is holding Solder has this
       welder as their nearest station -- the same selection rule as
       solder_nearest_welder() in server.c. */
    for (i = 0; i < this.stations.length; i++) {
      st = this.stations[i];
      if (st.type !== "welder") continue;
      if (!isBoard(st.board) || !st.pendingMaterial) { st.remainingMs = SOLDER_MS; continue; }

      var soldering = false;
      for (var j = 0; j < this.players.length; j++) {
        var pl = this.players[j];
        if ((pl.inputMask & BTN_SOLDER) && this.nearestStation(pl) === st) {
          soldering = true;
          break;
        }
      }
      if (soldering) {
        st.remainingMs -= TICK_MS;
        if (st.remainingMs <= 0) this.finishWeld(st);
      }
    }

    /* Verifiers count down on their own. */
    for (i = 0; i < this.stations.length; i++) {
      st = this.stations[i];
      if (st.type !== "verification_computer") continue;
      if (!isBoard(st.item) || !boardCanEnterWelder(st.item.state)) continue;
      st.remainingMs -= TICK_MS;
      if (st.remainingMs <= 0) this.finishVerify(st);
    }

    this.remainingMs -= TICK_MS;
    if (this.remainingMs <= 0) {
      this.remainingMs = 0;
      this.gameOver = true;
    }
  };

  Game.prototype.weldProgress = function (st) {
    if (!isBoard(st.board) || !st.pendingMaterial) return 0;
    return clampf(1 - st.remainingMs / SOLDER_MS, 0, 1);
  };

  Game.prototype.verifyProgress = function (st) {
    if (!isBoard(st.item) || !boardCanEnterWelder(st.item.state)) return 0;
    return clampf(1 - st.remainingMs / INSPECTION_MS, 0, 1);
  };

  /* ------------------------------------------------------------------ *
   * Renderer (display.py)
   * ------------------------------------------------------------------ */
  var FONT_STACK = '"Segoe UI", Inter, system-ui, -apple-system, sans-serif';
  var F_SMALL = '15px ' + FONT_STACK;
  var F_BODY = '20px ' + FONT_STACK;
  var F_MID = 'bold 26px ' + FONT_STACK;
  var F_BIG = 'bold 42px ' + FONT_STACK;
  var LH_SMALL = 20, LH_MID = 35, LH_BIG = 56;

  function Renderer(ctx, solderIcon) {
    this.ctx = ctx;
    this.solderIcon = solderIcon;
  }

  Renderer.prototype.roundRect = function (x, y, w, h, r) {
    var ctx = this.ctx;
    r = Math.max(0, Math.min(r, Math.min(w, h) / 2));
    ctx.beginPath();
    if (ctx.roundRect) { ctx.roundRect(x, y, w, h, r); return; }
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  };

  Renderer.prototype.fillRR = function (x, y, w, h, r, color) {
    this.roundRect(x, y, w, h, r);
    this.ctx.fillStyle = color;
    this.ctx.fill();
  };

  /* pygame strokes inside the rect, so inset by half the line width. */
  Renderer.prototype.strokeRR = function (x, y, w, h, r, color, lw) {
    var o = lw / 2;
    this.roundRect(x + o, y + o, w - lw, h - lw, Math.max(0, r - o));
    this.ctx.strokeStyle = color;
    this.ctx.lineWidth = lw;
    this.ctx.stroke();
  };

  Renderer.prototype.line = function (x1, y1, x2, y2, color, lw, cap) {
    var ctx = this.ctx;
    ctx.beginPath();
    ctx.moveTo(x1, y1);
    ctx.lineTo(x2, y2);
    ctx.strokeStyle = color;
    ctx.lineWidth = lw;
    ctx.lineCap = cap || "butt";
    ctx.stroke();
    ctx.lineCap = "butt";
  };

  Renderer.prototype.circle = function (x, y, r, color) {
    var ctx = this.ctx;
    ctx.beginPath();
    ctx.arc(x, y, r, 0, Math.PI * 2);
    ctx.fillStyle = color;
    ctx.fill();
  };

  Renderer.prototype.textAt = function (text, x, y, font, color) {
    var ctx = this.ctx;
    ctx.font = font;
    ctx.fillStyle = color;
    ctx.textAlign = "left";
    ctx.textBaseline = "top";
    ctx.fillText(text, x, y);
  };

  Renderer.prototype.textCentered = function (text, x, y, font, color) {
    var ctx = this.ctx;
    ctx.font = font;
    ctx.fillStyle = color;
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.fillText(text, x, y);
    ctx.textAlign = "left";
    ctx.textBaseline = "top";
  };

  Renderer.prototype.badge = function (text, x, y) {
    var ctx = this.ctx;
    ctx.font = F_SMALL;
    var tw = ctx.measureText(text).width;
    var w = tw + 12, h = LH_SMALL + 6;
    var rx = Math.round(x - w / 2), ry = Math.round(y - h / 2);
    this.fillRR(rx, ry, w, h, 6, "rgb(255,255,255)");
    this.strokeRR(rx, ry, w, h, 6, C.line, 1);
    this.textCentered(text, rx + w / 2, ry + h / 2, F_SMALL, C.ink);
  };

  Renderer.prototype.progress = function (x, y, w, value) {
    value = clampf(value, 0, 1);
    this.fillRR(x, y, w, 8, 4, "rgb(221,228,236)");
    if (value > 0) this.fillRR(x, y, Math.round(w * value), 8, 4, C.accent);
  };

  Renderer.prototype.drawMap = function () {
    var ctx = this.ctx;
    this.fillRR(MAP_X, MAP_Y, MAP_W, MAP_H, 18, C.floor);
    this.strokeRR(MAP_X, MAP_Y, MAP_W, MAP_H, 18, "rgb(182,198,214)", 4);
    ctx.save();
    this.roundRect(MAP_X, MAP_Y, MAP_W, MAP_H, 18);
    ctx.clip();
    ctx.strokeStyle = C.tile;
    ctx.lineWidth = 1;
    ctx.beginPath();
    for (var x = MAP_X; x < MAP_X + MAP_W; x += 40) {
      ctx.moveTo(x + 0.5, MAP_Y); ctx.lineTo(x + 0.5, MAP_Y + MAP_H);
    }
    for (var y = MAP_Y; y < MAP_Y + MAP_H; y += 40) {
      ctx.moveTo(MAP_X, y + 0.5); ctx.lineTo(MAP_X + MAP_W, y + 0.5);
    }
    ctx.stroke();
    ctx.restore();
  };

  Renderer.prototype.drawComponent = function (component, x, y, scale) {
    var ctx = this.ctx, s = scale === undefined ? 1 : scale;
    var color = component === "resistor" ? C.red
              : component === "capacitor" ? C.blue
              : component === "inductor" ? C.purple : C.muted;
    x = Math.round(x); y = Math.round(y);

    if (component === "resistor") {
      var pts = [
        [x - 18 * s, y], [x - 10 * s, y - 8 * s], [x - 2 * s, y + 8 * s],
        [x + 6 * s, y - 8 * s], [x + 14 * s, y + 8 * s], [x + 20 * s, y]
      ];
      ctx.beginPath();
      ctx.moveTo(pts[0][0], pts[0][1]);
      for (var i = 1; i < pts.length; i++) ctx.lineTo(pts[i][0], pts[i][1]);
      ctx.strokeStyle = color;
      ctx.lineWidth = Math.max(2, Math.round(4 * s));
      ctx.lineJoin = "round";
      ctx.lineCap = "round";
      ctx.stroke();
      ctx.lineJoin = "miter";
      ctx.lineCap = "butt";
    } else if (component === "capacitor") {
      var lw3 = Math.max(2, Math.round(3 * s));
      var lw4 = Math.max(2, Math.round(4 * s));
      this.line(x - 17 * s, y, x - 5 * s, y, color, lw3);
      this.line(x + 5 * s, y, x + 17 * s, y, color, lw3);
      this.line(x - 5 * s, y - 14 * s, x - 5 * s, y + 14 * s, color, lw4);
      this.line(x + 5 * s, y - 14 * s, x + 5 * s, y + 14 * s, color, lw4);
    } else {
      var lw = Math.max(2, Math.round(3 * s));
      this.line(x - 22 * s, y, x - 13 * s, y, color, lw);
      var offsets = [-9, 0, 9];
      for (var k = 0; k < offsets.length; k++) {
        /* pygame.draw.arc(rect(x+(o-5)s, y-10s, 11s, 20s), pi, 0) -> lower half */
        var cx = x + (offsets[k] + 0.5) * s;
        ctx.beginPath();
        ctx.ellipse(cx, y, 5.5 * s, 10 * s, 0, Math.PI, 0, true);
        ctx.strokeStyle = color;
        ctx.lineWidth = lw;
        ctx.stroke();
      }
      this.line(x + 18 * s, y, x + 24 * s, y, color, lw);
    }
  };

  Renderer.prototype.drawBoard = function (x, y, counts, broken, scale) {
    var s = scale === undefined ? 1 : scale;
    var w = Math.round(48 * s), h = Math.round(34 * s);
    var rx = x - Math.floor(w / 2), ry = y - Math.floor(h / 2);
    var r = Math.max(4, Math.round(6 * s));

    this.fillRR(rx, ry, w, h, r, "rgb(77,176,105)");
    this.strokeRR(rx, ry, w, h, r, "rgb(39,112,70)", 2);
    this.fillRR(rx + 16 * s, ry + 9 * s, 17 * s, 14 * s, 2, "rgb(42,56,66)");

    if (broken) {
      this.line(rx + 7, ry + 7, rx + w - 7, ry + h - 7, C.red, 4);
      this.line(rx + w - 7, ry + 7, rx + 7, ry + h - 7, C.red, 4);
    }
    var total = counts[0] + counts[1] + counts[2];
    if (total > 0) {
      var names = ["R", "C", "L"], parts = [];
      for (var i = 0; i < 3; i++) if (counts[i]) parts.push(names[i] + counts[i]);
      this.badge(parts.join(" "), x, y + Math.round(24 * s));
    }
  };

  Renderer.prototype.drawItem = function (item, x, y, scale) {
    if (!item) return;
    var s = scale === undefined ? 1 : scale;
    if (item.kind === "material") {
      this.drawComponent(item.component, x + 22 * s, y + 22 * s, s);
    } else if (item.kind === "board") {
      this.drawBoard(Math.round(x + 24 * s), Math.round(y + 20 * s),
                     item.counts, item.state === "failed", s);
    }
  };

  Renderer.prototype.drawComputer = function (x, y) {
    var sx = x - 27, sy = y - 20;
    this.fillRR(sx, sy, 54, 34, 5, "rgb(50,72,96)");
    this.fillRR(sx + 4, sy + 4, 46, 26, 4, "rgb(149,217,232)");
    this.line(x - 10, y - 3, x - 2, y + 6, C.green, 3);
    this.line(x - 2, y + 6, x + 14, y - 9, C.green, 3);
    this.fillRR(x - 18, y + 18, 36, 6, 3, "rgb(50,72,96)");
  };

  Renderer.prototype.drawShipping = function (x, y) {
    var ctx = this.ctx;
    this.fillRR(x - 28, y - 16, 38, 28, 6, C.green);
    ctx.beginPath();
    ctx.moveTo(x + 6, y - 24);
    ctx.lineTo(x + 34, y);
    ctx.lineTo(x + 6, y + 24);
    ctx.closePath();
    ctx.fillStyle = C.green;
    ctx.fill();
  };

  Renderer.prototype.drawTrash = function (x, y) {
    this.fillRR(x - 18, y - 14, 36, 34, 5, C.red);
    this.fillRR(x - 24, y - 22, 48, 8, 4, "rgb(165,62,62)");
    this.line(x - 8, y - 5, x + 8, y + 11, "rgb(255,245,245)", 3);
    this.line(x + 8, y - 5, x - 8, y + 11, "rgb(255,245,245)", 3);
  };

  Renderer.prototype.drawStation = function (game, st) {
    var ctx = this.ctx;
    var fill = STATION_FILL[st.type] || C.counter;
    var cx = st.x + st.w / 2, cy = st.y + st.h / 2;
    var bottom = st.y + st.h, right = st.x + st.w;

    this.fillRR(st.x, st.y + 5, st.w, st.h, 10, "rgb(181,195,208)");
    this.fillRR(st.x, st.y, st.w, st.h, 10, fill);
    this.strokeRR(st.x, st.y, st.w, st.h, 10, C.line, 2);

    if (st.type === "material_bin") {
      this.drawComponent(st.component, cx, cy + 4, 1);
      this.badge(st.component.charAt(0).toUpperCase(), cx, bottom + 12);
    } else if (st.type === "welder") {
      if (this.solderIcon) {
        ctx.drawImage(this.solderIcon, Math.round(cx - 23), Math.round(cy - 8 - 23), 46, 46);
      } else {
        this.textCentered("WELD", cx, cy - 8, F_BODY, C.ink);
      }
      this.progress(st.x + 10, bottom - 18, st.w - 20, game.weldProgress(st));
      this.drawItem(st.board, st.x + 16, st.y + 4, 0.7);
      this.drawItem(st.pendingMaterial, right - 42, st.y + 16, 0.62);
      this.badge("2s", cx, bottom + 12);
    } else if (st.type === "verification_computer") {
      this.drawComputer(cx, cy - 8);
      this.progress(st.x + 10, bottom - 18, st.w - 20, game.verifyProgress(st));
      this.drawItem(st.item, st.x + 12, st.y + 12, 0.68);
      this.badge("4s", cx, bottom + 12);
    } else if (st.type === "intake") {
      this.drawBoard(Math.round(cx), Math.round(cy - 4), [0, 0, 0], true, 0.85);
      this.badge("IN", cx, bottom + 12);
    } else if (st.type === "shipping") {
      this.drawShipping(cx, cy - 6);
      this.badge("OUT", cx, bottom + 12);
    } else if (st.type === "trash") {
      this.drawTrash(cx, cy - 4);
      this.badge("RECYCLE", cx, bottom + 12);
    } else if (st.type === "table") {
      this.drawItem(st.item, cx - 18, cy - 18, 0.75);
    }
  };

  Renderer.prototype.drawPlayer = function (p) {
    var x = Math.round(p.x), y = Math.round(p.y);
    var color = PLAYER_COLORS[(p.id - 1) % 4];
    this.circle(x, y + 5, 18, "rgb(120,132,145)");
    this.circle(x, y, 18, color);
    this.circle(x, y - 8, 9, "rgb(255,238,207)");
    this.circle(x - 3, y - 10, 2, C.ink);
    this.circle(x + 4, y - 10, 2, C.ink);
    this.textAt("P" + p.id, x - 9, y + 1, F_SMALL, "rgb(255,255,255)");
    this.drawItem(p.held, x - 14, y - 46, 0.75);
  };

  Renderer.prototype.drawOrders = function (game) {
    this.textAt("OVERBUG", 28, 22, F_BIG, C.ink);
    for (var i = 0; i < game.orders.length; i++) {
      var o = game.orders[i];
      var x = 292 + i * 206;
      var fill = o.lockedBoardId ? "rgb(232,248,234)" : "rgb(255,255,255)";
      this.fillRR(x, 18, 184, 64, 10, fill);
      this.strokeRR(x, 18, 184, 64, 10, C.line, 2);
      this.textCentered("Order " + o.id, x + 48, 34, F_SMALL, C.ink);
      var cx = x + 28;
      for (var k = 0; k < 3; k++) {
        this.drawComponent(COMPONENTS[k], cx, 58, 0.58);
        this.textAt("x" + o.req[k], cx + 16, 48, F_SMALL, C.ink);
        cx += 52;
      }
    }
  };

  Renderer.prototype.drawHud = function (game) {
    var rects = [[24, 660, 250, 46], [1060, 660, 190, 46]];
    for (var i = 0; i < rects.length; i++) {
      var r = rects[i];
      this.fillRR(r[0], r[1], r[2], r[3], 12, "rgb(255,255,255)");
      this.strokeRR(r[0], r[1], r[2], r[3], 12, C.line, 2);
    }
    this.textAt("Score " + game.score, 24 + 18, 660 + 8, F_MID, C.ink);
    var secs = Math.floor(game.remainingMs / 1000);
    var mm = String(Math.floor(secs / 60)).padStart(2, "0");
    var ss = String(secs % 60).padStart(2, "0");
    this.textAt(mm + ":" + ss, 1060 + 45, 660 + 8, F_MID, C.ink);
  };

  Renderer.prototype.drawGameOver = function (game) {
    var ctx = this.ctx;
    ctx.fillStyle = "rgba(24,34,44,0.588)";
    ctx.fillRect(0, 0, W, H);
    this.fillRR(390, 210, 500, 270, 18, "rgb(255,255,255)");
    this.strokeRR(390, 210, 500, 270, 18, C.line, 3);
    var cx = 390 + 250;
    this.textCentered("Time!", cx, 210 + 58, F_BIG, C.ink);
    var lines = [
      "Final score: " + game.score,
      "Boards shipped: " + game.completed,
      "Recycled items: " + game.recycled,
      "Press R to play again"
    ];
    for (var i = 0; i < lines.length; i++) {
      this.textCentered(lines[i], cx, 210 + 104 + i * 38, F_MID,
                        i < 3 ? C.ink : C.muted);
    }
  };

  Renderer.prototype.draw = function (game) {
    var ctx = this.ctx;
    ctx.fillStyle = C.bg;
    ctx.fillRect(0, 0, W, H);
    this.drawMap();
    for (var i = 0; i < game.stations.length; i++) {
      this.drawStation(game, game.stations[i]);
    }
    for (i = 0; i < game.players.length; i++) this.drawPlayer(game.players[i]);
    this.drawOrders(game);
    this.drawHud(game);
    if (game.gameOver) this.drawGameOver(game);
  };

  /* ------------------------------------------------------------------ *
   * Input -- bindings copied from Lab3/player.py CONTROLS
   * ------------------------------------------------------------------ */
  var BINDINGS = [
    { label: "P1", up: ["KeyW"], down: ["KeyS"], left: ["KeyA"], right: ["KeyD"],
      action: ["Space"], solder: ["ShiftLeft"],
      text: "W A S D  ·  Space  ·  Left Shift" },
    { label: "P2", up: ["ArrowUp"], down: ["ArrowDown"], left: ["ArrowLeft"], right: ["ArrowRight"],
      action: ["ControlRight"], solder: ["ShiftRight"],
      text: "Arrow keys  ·  Right Ctrl  ·  Right Shift" },
    { label: "P3", up: ["KeyI"], down: ["KeyK"], left: ["KeyJ"], right: ["KeyL"],
      action: ["KeyO"], solder: ["KeyP"],
      text: "I J K L  ·  O  ·  P" },
    { label: "P4", up: ["Digit8", "Numpad8"], down: ["Digit5", "Numpad5"],
      left: ["Digit4", "Numpad4"], right: ["Digit6", "Numpad6"],
      action: ["Digit0", "Numpad0"], solder: ["Digit7", "Numpad7"],
      text: "8 4 5 6  ·  0  ·  7" }
  ];

  function maskFor(index, down) {
    var b = BINDINGS[index], mask = 0;
    function any(codes) {
      for (var i = 0; i < codes.length; i++) if (down[codes[i]]) return true;
      return false;
    }
    if (any(b.up)) mask |= BTN_UP;
    if (any(b.down)) mask |= BTN_DOWN;
    if (any(b.left)) mask |= BTN_LEFT;
    if (any(b.right)) mask |= BTN_RIGHT;
    if (any(b.action)) mask |= BTN_ACTION;
    if (any(b.solder)) mask |= BTN_SOLDER;
    return mask;
  }

  function collectCodes(count) {
    var set = Object.create(null);
    for (var i = 0; i < count; i++) {
      var b = BINDINGS[i];
      ["up", "down", "left", "right", "action", "solder"].forEach(function (k) {
        b[k].forEach(function (code) { set[code] = true; });
      });
    }
    return set;
  }

  /* ------------------------------------------------------------------ *
   * Page wiring
   * ------------------------------------------------------------------ */
  function boot() {
    var canvas = document.getElementById("overbug-canvas");
    if (!canvas) return;

    var stage = document.getElementById("overbug-stage");
    var overlay = document.getElementById("overbug-overlay");
    var overlayTitle = document.getElementById("overbug-overlay-title");
    var overlayHint = document.getElementById("overbug-overlay-hint");
    var playButton = document.getElementById("overbug-play");
    var playersSelect = document.getElementById("overbug-players");
    var restartButton = document.getElementById("overbug-restart");
    var keysList = document.getElementById("overbug-keys");

    var ctx = canvas.getContext("2d");
    var solderIcon = new Image();
    var iconReady = false;
    solderIcon.onload = function () { iconReady = true; };
    solderIcon.src = "assets/soldering_iron_reference.png";

    var renderer = new Renderer(ctx, null);
    var playerCount = parseInt(playersSelect ? playersSelect.value : "1", 10) || 1;
    var game = new Game(playerCount);
    var running = false;
    var down = Object.create(null);
    var watched = collectCodes(playerCount);
    var accumulator = 0;
    var lastTime = 0;
    var loopId = 0;

    function resize() {
      var dpr = Math.min(window.devicePixelRatio || 1, 2);
      canvas.width = Math.round(W * dpr);
      canvas.height = Math.round(H * dpr);
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    }
    resize();
    window.addEventListener("resize", function () { resize(); render(); });

    function renderKeys() {
      if (!keysList) return;
      var html = "";
      for (var i = 0; i < playerCount; i++) {
        html += '<li><span class="game-key-tag" style="background:' +
          PLAYER_COLORS[i] + '">' + BINDINGS[i].label + "</span>" +
          "<span>" + BINDINGS[i].text + "</span></li>";
      }
      keysList.innerHTML = html;
    }

    function reset() {
      playerCount = parseInt(playersSelect ? playersSelect.value : "1", 10) || 1;
      game = new Game(playerCount);
      watched = collectCodes(playerCount);
      down = Object.create(null);
      accumulator = 0;
      renderKeys();
      render();
    }

    function showOverlay(title, hint) {
      if (!overlay) return;
      if (overlayTitle) overlayTitle.textContent = title;
      if (overlayHint) overlayHint.textContent = hint;
      overlay.hidden = false;
      if (stage) stage.classList.remove("is-playing");
    }

    function hideOverlay() {
      if (overlay) overlay.hidden = true;
      if (stage) stage.classList.add("is-playing");
    }

    function start() {
      if (running) return;
      running = true;
      hideOverlay();
      canvas.focus();
      lastTime = 0;
      accumulator = 0;
      loopId++;
      schedule(loopId);
    }

    function schedule(id) {
      requestAnimationFrame(function (now) { frame(now, id); });
    }

    function pause(reason) {
      running = false;
      down = Object.create(null);
      for (var i = 0; i < game.players.length; i++) game.players[i].inputMask = 0;
      showOverlay(reason, "Click the board to carry on.");
      render();
    }

    function render() {
      renderer.solderIcon = iconReady ? solderIcon : null;
      renderer.draw(game);
    }

    function frame(now, id) {
      /* A frame queued before the last pause must not resurrect itself when
         play resumes -- that would leave two render loops running at once, and
         one more would leak on every pause/resume. The generation token retires
         every loop but the newest. */
      if (!running || id !== loopId) return;
      if (lastTime === 0) lastTime = now;
      var elapsed = now - lastTime;
      lastTime = now;

      /* A hidden tab should not fast-forward the round. */
      if (elapsed > 1000) elapsed = TICK_MS;
      accumulator += elapsed;

      var steps = 0;
      while (accumulator >= TICK_MS && steps < 20) {
        for (var i = 0; i < game.players.length; i++) {
          game.players[i].inputMask = maskFor(i, down);
        }
        game.step();
        accumulator -= TICK_MS;
        steps++;
      }
      if (accumulator > TICK_MS * 20) accumulator = 0;

      render();
      schedule(id);
    }

    canvas.addEventListener("keydown", function (e) {
      if (e.repeat) {
        if (watched[e.code]) e.preventDefault();
        return;
      }
      if (e.code === "KeyR" && game.gameOver) {
        e.preventDefault();
        reset();
        return;
      }
      if (e.code === "Escape") { pause("Paused"); return; }
      if (watched[e.code]) {
        e.preventDefault();
        down[e.code] = true;
      }
    });

    canvas.addEventListener("keyup", function (e) {
      if (watched[e.code]) {
        e.preventDefault();
        down[e.code] = false;
      }
    });

    canvas.addEventListener("blur", function () {
      if (running) pause("Paused");
    });

    canvas.addEventListener("mousedown", function (e) {
      e.preventDefault();
      canvas.focus();
      if (!running) start();
    });

    if (playButton) {
      playButton.addEventListener("click", function () { start(); });
    }
    if (restartButton) {
      restartButton.addEventListener("click", function () {
        reset();
        canvas.focus();
        if (!running) start();
      });
    }
    if (playersSelect) {
      playersSelect.addEventListener("change", function () {
        reset();
        if (running) canvas.focus();
      });
    }

    document.addEventListener("visibilitychange", function () {
      if (document.hidden && running) pause("Paused");
    });

    solderIcon.onload = function () { iconReady = true; render(); };

    renderKeys();
    render();

    /* No touch controls: on a phone or tablet the board still draws, but there
       is nothing to drive it. Say so instead of starting a game that cannot be
       played. Play is still allowed, so an iPad with a keyboard works. */
    var coarse = window.matchMedia &&
      window.matchMedia("(hover: none) and (pointer: coarse)").matches;
    showOverlay("Play Overbug", coarse
      ? "Keyboard required - this demo has no touch controls."
      : "Lab 4 rules, running in your browser.");
  }

  /* Exported so the rules can be unit-tested outside a browser. */
  if (typeof module !== "undefined" && module.exports) {
    module.exports = {
      Game: Game, GlibcRandom: GlibcRandom, distanceToRect: distanceToRect,
      FACILITIES: FACILITIES,
      BTN: { UP: BTN_UP, DOWN: BTN_DOWN, LEFT: BTN_LEFT, RIGHT: BTN_RIGHT,
             ACTION: BTN_ACTION, SOLDER: BTN_SOLDER },
      TICK_MS: TICK_MS, ROUND_MS: ROUND_MS
    };
  }

  if (typeof document !== "undefined") {
    if (document.readyState === "loading") {
      document.addEventListener("DOMContentLoaded", boot);
    } else {
      boot();
    }
  }
})();
