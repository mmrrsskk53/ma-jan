/* ============================================================
 *  麻雀エンジン  (mahjong engine)
 *  UI非依存・将来のネット対戦でもサーバ側でそのまま使える純ロジック
 *  牌表現: 数値 0..33
 *    0-8   : 1m-9m (萬子)
 *    9-17  : 1p-9p (筒子)
 *    18-26 : 1s-9s (索子)
 *    27-30 : 東南西北 (風牌 E S W N)
 *    31-33 : 白發中 (三元牌 P G R)  (白=31 發=32 中=33)
 *  赤ドラは別フラグ(redFives)で管理し、牌IDとしては5扱い
 * ============================================================ */
(function (global) {
  'use strict';

  const M = {}; // module exports

  // ---- 定数 ----
  const MAN = 0, PIN = 9, SOU = 18, HONOR = 27;
  M.MAN = MAN; M.PIN = PIN; M.SOU = SOU; M.HONOR = HONOR;
  M.E = 27; M.S = 28; M.W = 29; M.N = 30;
  M.HAKU = 31; M.HATSU = 32; M.CHUN = 33;

  M.TILE_NAMES = (() => {
    const a = [];
    for (let i = 1; i <= 9; i++) a.push(i + 'm');
    for (let i = 1; i <= 9; i++) a.push(i + 'p');
    for (let i = 1; i <= 9; i++) a.push(i + 's');
    a.push('東', '南', '西', '北', '白', '發', '中');
    return a;
  })();

  M.isHonor = t => t >= HONOR;
  M.isTerminal = t => !M.isHonor(t) && (t % 9 === 0 || t % 9 === 8);
  M.isYaochu = t => M.isHonor(t) || M.isTerminal(t);
  M.suitOf = t => t < PIN ? 'm' : t < SOU ? 'p' : t < HONOR ? 's' : 'z';
  M.numOf = t => M.isHonor(t) ? 0 : (t % 9) + 1;

  // ---- 牌山生成 ----
  M.buildWall = function () {
    const wall = [];
    for (let t = 0; t < 34; t++) for (let k = 0; k < 4; k++) wall.push(t);
    // シャッフル (Fisher-Yates)
    for (let i = wall.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [wall[i], wall[j]] = [wall[j], wall[i]];
    }
    return wall;
  };

  // 手牌を34配列(各牌の枚数)に変換
  M.toCounts = function (tiles) {
    const c = new Array(34).fill(0);
    for (const t of tiles) c[t]++;
    return c;
  };

  // ============================================================
  //  シャンテン数計算
  // ============================================================
  // 通常形シャンテン (面子手)
  //  melds = 確定面子数(鳴き)。 必要総面子 = 4
  //  シャンテン = (4 - sets)*2 - max(partials+pairs, ...) 系を全探索で最小化
  function shantenNormal(counts, melds) {
    let min = 8;
    const needSets = 4;
    // sets:完成面子, partials:塔子+対子(雀頭以外), hasPair:雀頭確保フラグ
    const rec = (idx, sets, partials, hasPair) => {
      while (idx < 34 && counts[idx] === 0) idx++;
      if (idx >= 34) {
        const s = sets + melds;
        // ブロック数(面子+塔子)は最大4まで有効、+雀頭1
        let useP = partials;
        if (s + useP > needSets) useP = needSets - s;
        if (useP < 0) useP = 0;
        let st = (needSets - s) * 2 - useP - (hasPair ? 1 : 0);
        if (st < min) min = st;
        return;
      }
      const s = sets + melds;
      const blocks = s + partials + (hasPair ? 1 : 0);

      // 刻子
      if (counts[idx] >= 3) {
        counts[idx] -= 3;
        rec(idx, sets + 1, partials, hasPair);
        counts[idx] += 3;
      }
      // 順子
      if (idx < HONOR && (idx % 9) <= 6 && counts[idx + 1] > 0 && counts[idx + 2] > 0) {
        counts[idx]--; counts[idx + 1]--; counts[idx + 2]--;
        rec(idx, sets + 1, partials, hasPair);
        counts[idx]++; counts[idx + 1]++; counts[idx + 2]++;
      }
      // 雀頭(対子を雀頭として確保)
      if (!hasPair && counts[idx] >= 2) {
        counts[idx] -= 2;
        rec(idx, sets, partials, true);
        counts[idx] += 2;
      }
      // 対子を塔子(刻子の種)として使う
      if (counts[idx] >= 2 && blocks < 5) {
        counts[idx] -= 2;
        rec(idx, sets, partials + 1, hasPair);
        counts[idx] += 2;
      }
      // 塔子(隣接)
      if (idx < HONOR && (idx % 9) <= 7 && counts[idx + 1] > 0 && blocks < 5) {
        counts[idx]--; counts[idx + 1]--;
        rec(idx, sets, partials + 1, hasPair);
        counts[idx]++; counts[idx + 1]++;
      }
      // 塔子(嵌張)
      if (idx < HONOR && (idx % 9) <= 6 && counts[idx + 2] > 0 && blocks < 5) {
        counts[idx]--; counts[idx + 2]--;
        rec(idx, sets, partials + 1, hasPair);
        counts[idx]++; counts[idx + 2]++;
      }
      // 孤立牌として1枚捨てる
      counts[idx]--;
      rec(idx, sets, partials, hasPair);
      counts[idx]++;
    };
    rec(0, 0, 0, false);
    return min;
  }

  // 七対子シャンテン
  function shantenChiitoi(counts) {
    let pairs = 0, kinds = 0;
    for (let i = 0; i < 34; i++) {
      if (counts[i] >= 2) pairs++;
      if (counts[i] >= 1) kinds++;
    }
    let st = 6 - pairs + Math.max(0, 7 - kinds);
    return st;
  }

  // 国士無双シャンテン
  function shantenKokushi(counts) {
    let kinds = 0, hasPair = 0;
    for (let i = 0; i < 34; i++) {
      if (M.isYaochu(i)) {
        if (counts[i] >= 1) kinds++;
        if (counts[i] >= 2) hasPair = 1;
      }
    }
    return 13 - kinds - hasPair;
  }

  // 総合シャンテン(鳴き無し前提でtiles=手牌全部, melds=鳴き面子数)
  const _shantenCache = new Map();
  M.shantenFromCounts = function (counts, melds = 0) {
    // キー生成(34桁)
    let key = melds;
    for (let i = 0; i < 34; i++) key = key * 5 + counts[i];
    const cached = _shantenCache.get(key);
    if (cached !== undefined) return cached;
    let s = shantenNormal(counts.slice(), melds);
    if (melds === 0) s = Math.min(s, shantenChiitoi(counts), shantenKokushi(counts));
    if (_shantenCache.size > 200000) _shantenCache.clear();
    _shantenCache.set(key, s);
    return s;
  };
  M.shanten = function (tiles, melds = 0) {
    return M.shantenFromCounts(M.toCounts(tiles), melds);
  };

  // 完成形判定: tilesは「鳴きを除いた手牌(和了牌含む)」, melds=鳴き面子数
  //  必要面子数 needSets = 4 - melds, それに雀頭1
  function isComplete(counts, needSets) {
    // 標準形
    if (canFormStandard(counts.slice(), needSets)) return true;
    return false;
  }
  function canFormStandard(counts, needSets) {
    // 雀頭を選んで残りを面子分解
    const rec = (idx, sets, pairUsed) => {
      while (idx < 34 && counts[idx] === 0) idx++;
      if (idx >= 34) return sets === needSets && pairUsed;
      // 雀頭
      if (!pairUsed && counts[idx] >= 2) {
        counts[idx] -= 2;
        if (rec(idx, sets, true)) { counts[idx] += 2; return true; }
        counts[idx] += 2;
      }
      // 刻子
      if (counts[idx] >= 3) {
        counts[idx] -= 3;
        if (rec(idx, sets + 1, pairUsed)) { counts[idx] += 3; return true; }
        counts[idx] += 3;
      }
      // 順子
      if (idx < HONOR && (idx % 9) <= 6 && counts[idx + 1] > 0 && counts[idx + 2] > 0) {
        counts[idx]--; counts[idx + 1]--; counts[idx + 2]--;
        if (rec(idx, sets + 1, pairUsed)) { counts[idx]++; counts[idx + 1]++; counts[idx + 2]++; return true; }
        counts[idx]++; counts[idx + 1]++; counts[idx + 2]++;
      }
      return false;
    };
    return rec(0, 0, false);
  }

  // 和了判定
  M.isAgari = function (tiles, melds = 0) {
    const counts = M.toCounts(tiles);
    // メモ化済みシャンテンで高速枝刈り(和了は必ず-1)
    if (M.shantenFromCounts(counts, melds) !== -1) return false;
    const needSets = 4 - melds;
    if (canFormStandard(counts.slice(), needSets)) return true;
    if (melds === 0) {
      let pairs = 0, ok = true;
      for (let i = 0; i < 34; i++) {
        if (counts[i] === 0) continue;
        if (counts[i] === 2) pairs++; else { ok = false; break; }
      }
      if (ok && pairs === 7) return true;
      if (shantenKokushi(counts) === -1) return true;
    }
    return false;
  };

  // テンパイ判定 + 待ち牌列挙 (tilesは3n+1枚, 鳴きを除く手牌)
  M.waits = function (tiles, melds = 0) {
    const w = [];
    const counts = M.toCounts(tiles);
    for (let t = 0; t < 34; t++) {
      if (counts[t] >= 4) continue;
      tiles.push(t);
      if (M.isAgari(tiles, melds)) w.push(t);
      tiles.pop();
    }
    return w;
  };
  // テンパイ判定
  M.isTenpai = function (tiles, melds = 0) {
    return M.waits(tiles, melds).length > 0;
  };

  // ============================================================
  //  面子分解 (役判定・符計算用に手牌を面子へ分解)
  //  返り値: { sets:[{type:'shun'|'kou', tiles:[...], open:bool}], pair:t }
  //  鳴き面子(openMelds)は別途与える
  // ============================================================
  function decomposeStandard(counts) {
    const results = [];
    const rec = (idx, pair, sets) => {
      while (idx < 34 && counts[idx] === 0) idx++;
      if (idx >= 34) {
        if (pair !== -1) results.push({ pair, sets: sets.map(s => ({ ...s })) });
        return;
      }
      // 雀頭
      if (pair === -1 && counts[idx] >= 2) {
        counts[idx] -= 2;
        rec(idx, idx, sets);
        counts[idx] += 2;
      }
      // 刻子
      if (counts[idx] >= 3) {
        counts[idx] -= 3;
        sets.push({ type: 'kou', t: idx });
        rec(idx, pair, sets);
        sets.pop();
        counts[idx] += 3;
      }
      // 順子
      if (idx < HONOR && (idx % 9) <= 6 && counts[idx + 1] > 0 && counts[idx + 2] > 0) {
        counts[idx]--; counts[idx + 1]--; counts[idx + 2]--;
        sets.push({ type: 'shun', t: idx });
        rec(idx, pair, sets);
        sets.pop();
        counts[idx]++; counts[idx + 1]++; counts[idx + 2]++;
      }
    };
    rec(0, -1, []);
    return results;
  }

  // ============================================================
  //  役判定 + 点数計算
  //  ctx: {
  //    hand: [手牌(和了牌含まない13枚 or 鳴き除く部分)],
  //    winTile: 和了牌,
  //    melds: [{type:'chi'|'pon'|'kan'|'ankan', tiles:[...]}],
  //    tsumo: bool,
  //    riichi: bool, doubleRiichi: bool, ippatsu: bool,
  //    seatWind: 27..30, roundWind: 27..30,
  //    dora: [表ドラ牌...], uraDora:[...], aka: 赤5の枚数,
  //    haitei: bool, houtei: bool, rinshan: bool, chankan: bool,
  //    isParent: bool (親),
  //    tenhou/chiihou は省略
  //  }
  // ============================================================
  M.score = function (ctx) {
    const allTiles = ctx.hand.concat([ctx.winTile]);
    const melds = ctx.melds || [];
    const isMenzen = melds.every(m => m.type === 'ankan'); // 暗槓のみなら門前維持
    const concealed = melds.length === 0 || isMenzen;

    // 全牌count (鳴き含む全14枚相当)
    const allCounts = new Array(34).fill(0);
    for (const t of allTiles) allCounts[t]++;
    for (const m of melds) for (const t of m.tiles) allCounts[t]++;

    let best = null;

    // --- 国士無双 ---
    {
      const k = shantenKokushi(M.toCounts(allTiles));
      if (melds.length === 0 && k === -1) {
        // 13面待ちか
        const c = M.toCounts(ctx.hand);
        let pairTile = -1;
        for (let i = 0; i < 34; i++) if (M.isYaochu(i) && c[i] >= 1) { if (c[i] >= 2) pairTile = i; }
        const thirteen = ctx.hand.filter(t => M.isYaochu(t)).length === 13 &&
          new Set(ctx.hand).size === 13;
        const yaku = thirteen
          ? [{ name: '国士無双十三面', han: 26 }]
          : [{ name: '国士無双', han: 13 }];
        return finalize(ctx, yaku, 20, true);
      }
    }

    // --- 七対子 ---
    {
      const c = M.toCounts(allTiles);
      let pairs = 0, ok = true;
      for (let i = 0; i < 34; i++) {
        if (c[i] === 0) continue;
        if (c[i] === 2) pairs++; else { ok = false; break; }
      }
      if (melds.length === 0 && ok && pairs === 7) {
        const yaku = buildYaku(ctx, {
          chiitoi: true, concealed: true,
          pairs: Array.from({ length: 34 }, (_, i) => i).filter(i => c[i] === 2),
          sets: [], pair: -1, allCounts, melds, isMenzen: true
        });
        const cand = finalize(ctx, yaku, 25, false, { chiitoi: true });
        if (!best || cand.total > best.total) best = cand;
      }
    }

    // --- 通常形 ---
    {
      // 鳴き牌を除いた手牌部分を分解
      const handCounts = M.toCounts(allTiles);
      // 鳴き面子分は既に確定しているので分解対象から除外しない(allTilesは鳴き除く想定)
      const decomps = decomposeStandard(handCounts);
      for (const d of decomps) {
        const sets = [];
        for (const s of d.sets) {
          sets.push({ type: s.type, t: s.t, open: false });
        }
        for (const m of melds) {
          if (m.type === 'chi') sets.push({ type: 'shun', t: Math.min(...m.tiles), open: true, kan: false });
          else if (m.type === 'pon') sets.push({ type: 'kou', t: m.tiles[0], open: true, kan: false });
          else if (m.type === 'kan') sets.push({ type: 'kou', t: m.tiles[0], open: true, kan: true });
          else if (m.type === 'ankan') sets.push({ type: 'kou', t: m.tiles[0], open: false, kan: true });
        }
        const yaku = buildYaku(ctx, {
          chiitoi: false, concealed,
          sets, pair: d.pair, allCounts, melds, isMenzen,
          handDecomp: d
        });
        if (yaku.length === 0 && !hasYakuman(yaku)) {
          // 役なし → 和了不可(ドラのみは役なし)
          // ただしドラがあっても役がなければ無効。ここではスキップ
          continue;
        }
        const fu = M.calcFu(ctx, { sets, pair: d.pair, concealed, isMenzen });
        const cand = finalize(ctx, yaku, fu, hasYakuman(yaku));
        if (!best || cand.total > best.total) best = cand;
      }
    }

    return best; // null なら役なし(和了不可)
  };

  function hasYakuman(yaku) {
    return yaku.some(y => y.han >= 13);
  }

  // ドラ枚数を数える
  function countDora(ctx, allCounts) {
    let n = 0;
    for (const d of (ctx.dora || [])) {
      const target = nextDora(d);
      n += allCounts[target];
    }
    if (ctx.riichi || ctx.doubleRiichi) {
      for (const d of (ctx.uraDora || [])) {
        const target = nextDora(d);
        n += allCounts[target];
      }
    }
    n += (ctx.aka || 0);
    return n;
  }
  function nextDora(indicator) {
    // 数牌
    if (indicator < HONOR) {
      const base = Math.floor(indicator / 9) * 9;
      const num = indicator % 9;
      return base + ((num + 1) % 9);
    }
    // 風牌 東南西北 27-30 ループ
    if (indicator <= 30) return 27 + ((indicator - 27 + 1) % 4);
    // 三元牌 白發中 31-33 ループ
    return 31 + ((indicator - 31 + 1) % 3);
  }
  M.nextDora = nextDora;

  // ============================================================
  //  役の構築
  // ============================================================
  function buildYaku(ctx, info) {
    const Y = [];
    const { concealed, isMenzen } = info;
    const seat = ctx.seatWind, round = ctx.roundWind;

    // ----- 状況役 -----
    if (ctx.riichi && !ctx.doubleRiichi) Y.push({ name: 'リーチ', han: 1 });
    if (ctx.doubleRiichi) Y.push({ name: 'ダブルリーチ', han: 2 });
    if (ctx.ippatsu) Y.push({ name: '一発', han: 1 });
    if (ctx.tsumo && isMenzen) Y.push({ name: '門前清自摸和', han: 1 });
    if (ctx.haitei && ctx.tsumo) Y.push({ name: '海底摸月', han: 1 });
    if (ctx.houtei && !ctx.tsumo) Y.push({ name: '河底撈魚', han: 1 });
    if (ctx.rinshan) Y.push({ name: '嶺上開花', han: 1 });
    if (ctx.chankan) Y.push({ name: '槍槓', han: 1 });

    // ----- 七対子 -----
    if (info.chiitoi) {
      Y.push({ name: '七対子', han: 2 });
      addSuitYaku(Y, ctx, info, true);
      addTanyao(Y, ctx, info, true);
      addHonroChiitoi(Y, info);
      return Y;
    }

    const sets = info.sets, pair = info.pair;

    // ----- ピンフ -----
    if (isMenzen && isPinfu(ctx, sets, pair)) Y.push({ name: '平和', han: 1 });

    // ----- タンヤオ -----
    addTanyao(Y, ctx, info, false);

    // ----- 役牌 -----
    for (const s of sets) {
      if (s.type === 'kou') {
        if (s.t === M.HAKU) Y.push({ name: '役牌 白', han: 1 });
        else if (s.t === M.HATSU) Y.push({ name: '役牌 發', han: 1 });
        else if (s.t === M.CHUN) Y.push({ name: '役牌 中', han: 1 });
        else if (s.t === round && s.t >= 27 && s.t <= 30) Y.push({ name: '場風', han: 1 });
        if (s.t === seat && s.t >= 27 && s.t <= 30 && s.t !== round) Y.push({ name: '自風', han: 1 });
        else if (s.t === seat && s.t === round && s.t >= 27 && s.t <= 30) Y.push({ name: '自風', han: 1 });
      }
    }

    // ----- 一盃口 / 二盃口 -----
    const shunPairs = countIdenticalShun(sets);
    if (isMenzen) {
      if (shunPairs >= 2) Y.push({ name: '二盃口', han: 3 });
      else if (shunPairs === 1) Y.push({ name: '一盃口', han: 1 });
    }

    // ----- 三色同順 -----
    if (hasSanshokuShun(sets)) Y.push({ name: '三色同順', han: concealed ? 2 : 1 });
    // ----- 三色同刻 -----
    if (hasSanshokuKou(sets)) Y.push({ name: '三色同刻', han: 2 });
    // ----- 一気通貫 -----
    if (hasIttsu(sets)) Y.push({ name: '一気通貫', han: concealed ? 2 : 1 });
    // ----- チャンタ / 純チャン -----
    const chanta = chantaType(sets, pair);
    if (chanta === 'junchan') Y.push({ name: '純全帯幺九', han: concealed ? 3 : 2 });
    else if (chanta === 'chanta') Y.push({ name: '混全帯幺九', han: concealed ? 2 : 1 });
    // ----- 対々和 -----
    const kouCount = sets.filter(s => s.type === 'kou').length;
    if (kouCount === 4) Y.push({ name: '対々和', han: 2 });
    // ----- 三暗刻 -----
    const ankou = countAnkou(ctx, sets, pair);
    if (ankou === 3) Y.push({ name: '三暗刻', han: 2 });
    // ----- 三槓子 -----
    const kanCount = sets.filter(s => s.kan).length;
    if (kanCount === 3) Y.push({ name: '三槓子', han: 2 });
    // ----- 小三元 -----
    if (isShousangen(sets, pair)) Y.push({ name: '小三元', han: 2 });

    // ----- 混一色 / 清一色 -----
    addSuitYaku(Y, ctx, info, false);
    // ----- 混老頭 -----
    if (isHonroutou(sets, pair)) Y.push({ name: '混老頭', han: 2 });

    // ===== 役満 =====
    const ym = [];
    if (kouCount === 4 && ankou === 4) ym.push({ name: '四暗刻', han: 13 });
    if (isDaisangen(sets)) ym.push({ name: '大三元', han: 13 });
    const windKou = sets.filter(s => s.type === 'kou' && s.t >= 27 && s.t <= 30).length;
    if (windKou === 4) ym.push({ name: '大四喜', han: 26 });
    else if (windKou === 3 && pair >= 27 && pair <= 30) ym.push({ name: '小四喜', han: 13 });
    if (isTsuuiisou(sets, pair)) ym.push({ name: '字一色', han: 13 });
    if (isChinroutou(sets, pair)) ym.push({ name: '清老頭', han: 13 });
    if (isRyuuiisou(sets, pair)) ym.push({ name: '緑一色', han: 13 });
    if (kanCount === 4) ym.push({ name: '四槓子', han: 13 });
    const chuuren = isChuuren(ctx, info);
    if (chuuren) ym.push({ name: chuuren, han: chuuren.includes('純正') ? 26 : 13 });

    if (ym.length > 0) {
      // 役満成立時は通常役を破棄
      // ただし状況役満(天和等)は省略
      return ym;
    }

    return Y;
  }

  // ----- 各役判定ヘルパ -----
  function addTanyao(Y, ctx, info, chiitoi) {
    let allSimple = true;
    if (chiitoi) {
      for (const p of info.pairs) if (M.isYaochu(p)) allSimple = false;
    } else {
      for (const s of info.sets) {
        if (s.type === 'kou' && M.isYaochu(s.t)) allSimple = false;
        if (s.type === 'shun' && (M.isTerminal(s.t) || M.isTerminal(s.t + 2))) allSimple = false;
        if (s.type === 'shun' && (s.t % 9 === 0 && false)) { }
      }
      if (M.isYaochu(info.pair)) allSimple = false;
    }
    if (allSimple) Y.push({ name: '断幺九', han: 1 });
  }

  function isPinfu(ctx, sets, pair) {
    if (sets.some(s => s.type === 'kou')) return false;
    // 雀頭が役牌でない
    if (pair === M.HAKU || pair === M.HATSU || pair === M.CHUN) return false;
    if (pair === ctx.seatWind || pair === ctx.roundWind) {
      if (pair >= 27 && pair <= 30) return false;
    }
    // 両面待ち判定: 和了牌が順子の端(両面)であること
    let ryanmen = false;
    for (const s of sets) {
      if (s.type !== 'shun') continue;
      // s.t, s.t+1, s.t+2
      // 和了牌がs.t または s.t+2 で、嵌張/辺張でない両面
      if (ctx.winTile === s.t && (s.t % 9) !== 6) ryanmen = true; // 下端待ち(待ちはs.t … 1-2待ち3 等)
      if (ctx.winTile === s.t + 2 && (s.t % 9) !== 0) ryanmen = true;
    }
    return ryanmen;
  }

  function countIdenticalShun(sets) {
    const m = {};
    for (const s of sets) if (s.type === 'shun' && !s.open) m[s.t] = (m[s.t] || 0) + 1;
    let pairs = 0;
    for (const k in m) pairs += Math.floor(m[k] / 2);
    return pairs;
  }

  function hasSanshokuShun(sets) {
    const shuns = sets.filter(s => s.type === 'shun').map(s => s.t);
    for (const t of shuns) {
      if (t < PIN) {
        const n = t % 9;
        if (shuns.includes(PIN + n) && shuns.includes(SOU + n)) return true;
      }
    }
    return false;
  }
  function hasSanshokuKou(sets) {
    const kous = sets.filter(s => s.type === 'kou' && s.t < HONOR).map(s => s.t);
    for (const t of kous) {
      const n = t % 9, base = Math.floor(t / 9) * 9;
      const m = MAN + n, p = PIN + n, so = SOU + n;
      if (kous.includes(m) && kous.includes(p) && kous.includes(so)) return true;
    }
    return false;
  }
  function hasIttsu(sets) {
    const shuns = sets.filter(s => s.type === 'shun').map(s => s.t);
    for (const base of [MAN, PIN, SOU]) {
      if (shuns.includes(base) && shuns.includes(base + 3) && shuns.includes(base + 6)) return true;
    }
    return false;
  }
  function chantaType(sets, pair) {
    let allHaveTerminal = true, hasHonor = false, hasShun = false;
    const check = t => { if (M.isHonor(t)) hasHonor = true; };
    for (const s of sets) {
      if (s.type === 'kou') {
        if (!M.isYaochu(s.t)) { allHaveTerminal = false; break; }
        check(s.t);
      } else {
        hasShun = true;
        // 順子は1-2-3 または 7-8-9 のみ幺九含む
        const n = s.t % 9;
        if (n !== 0 && n !== 6) { allHaveTerminal = false; break; }
      }
    }
    if (allHaveTerminal) {
      if (!M.isYaochu(pair)) allHaveTerminal = false;
      else check(pair);
    }
    if (!allHaveTerminal) return null;
    if (!hasShun) return null; // 順子無しはチャンタ系扱いしない(混老頭/清老頭へ)
    return hasHonor ? 'chanta' : 'junchan';
  }
  function countAnkou(ctx, sets, pair) {
    let n = 0;
    for (const s of sets) {
      if (s.type === 'kou' && !s.open) {
        // ロン和了で完成した刻子は明刻扱い
        if (!ctx.tsumo && ctx.winTile === s.t && !s.kan) {
          // この刻子が和了牌で完成したものなら明刻
          // 簡易: 手牌内に元々2枚あった→ロンで明刻。暗槓は常に暗刻
          continue;
        }
        n++;
      }
    }
    return n;
  }
  function isShousangen(sets, pair) {
    const dragons = [M.HAKU, M.HATSU, M.CHUN];
    let kou = 0, pairIsDragon = dragons.includes(pair);
    for (const s of sets) if (s.type === 'kou' && dragons.includes(s.t)) kou++;
    return kou === 2 && pairIsDragon;
  }
  function addSuitYaku(Y, ctx, info, chiitoi) {
    const counts = info.allCounts;
    let suits = new Set(), hasHonor = false;
    for (let i = 0; i < 34; i++) {
      if (counts[i] === 0) continue;
      if (M.isHonor(i)) hasHonor = true;
      else suits.add(Math.floor(i / 9));
    }
    if (suits.size === 1) {
      if (hasHonor) Y.push({ name: '混一色', han: info.isMenzen ? 3 : 2 });
      else Y.push({ name: '清一色', han: info.isMenzen ? 6 : 5 });
    }
  }
  function addHonroChiitoi(Y, info) {
    // 七対子で全て幺九 → 混老頭(字一色は別途)
    let allYao = info.pairs.every(p => M.isYaochu(p));
    if (allYao) {
      const allHonor = info.pairs.every(p => M.isHonor(p));
      if (!allHonor) Y.push({ name: '混老頭', han: 2 });
    }
  }
  function isHonroutou(sets, pair) {
    if (sets.some(s => s.type === 'shun')) return false;
    if (!M.isYaochu(pair)) return false;
    for (const s of sets) if (!M.isYaochu(s.t)) return false;
    // 字牌のみは字一色なので混老頭からは除外(役満優先)
    return true;
  }
  function isDaisangen(sets) {
    const dragons = [M.HAKU, M.HATSU, M.CHUN];
    let kou = 0;
    for (const s of sets) if (s.type === 'kou' && dragons.includes(s.t)) kou++;
    return kou === 3;
  }
  function isTsuuiisou(sets, pair) {
    if (!M.isHonor(pair)) return false;
    for (const s of sets) if (!M.isHonor(s.t)) return false;
    return true;
  }
  function isChinroutou(sets, pair) {
    if (sets.some(s => s.type === 'shun')) return false;
    if (!M.isTerminal(pair)) return false;
    for (const s of sets) if (!M.isTerminal(s.t)) return false;
    return true;
  }
  function isRyuuiisou(sets, pair) {
    const green = new Set([SOU + 1, SOU + 2, SOU + 3, SOU + 5, SOU + 7, M.HATSU]); // 2,3,4,6,8s,發
    const ok = t => green.has(t);
    if (!ok(pair)) return false;
    for (const s of sets) {
      if (s.type === 'shun') {
        // 2-3-4s のみ
        if (s.t !== SOU + 1) return false;
      } else {
        if (!ok(s.t)) return false;
      }
    }
    return true;
  }
  function isChuuren(ctx, info) {
    const counts = info.allCounts;
    let suit = -1;
    for (let s = 0; s < 3; s++) {
      let cnt = 0;
      for (let i = 0; i < 9; i++) cnt += counts[s * 9 + i];
      if (cnt === 14) suit = s;
    }
    if (suit < 0) return null;
    // honor無し確認
    for (let i = HONOR; i < 34; i++) if (counts[i]) return null;
    const base = suit * 9;
    // 1112345678999 + 1枚
    const need = [3, 1, 1, 1, 1, 1, 1, 1, 3];
    const extra = [];
    for (let i = 0; i < 9; i++) {
      const diff = counts[base + i] - need[i];
      if (diff < 0) return null;
      for (let k = 0; k < diff; k++) extra.push(i);
    }
    if (extra.length !== 1) return null;
    // 純正九蓮: 和了牌を抜くと 1112345678999 になる(=待ちが9面)
    const winNum = ctx.winTile - base;
    const tmp = counts.slice(base, base + 9);
    tmp[winNum]--;
    let pure = true;
    for (let i = 0; i < 9; i++) if (tmp[i] !== need[i]) pure = false;
    return pure ? '純正九蓮宝燈' : '九蓮宝燈';
  }

  // ============================================================
  //  符計算
  // ============================================================
  M.calcFu = function (ctx, info) {
    const { sets, pair, concealed, isMenzen } = info;
    // 平和ツモ = 20符固定
    const isPinfuHand = isMenzen && isPinfu(ctx, sets, pair);
    if (isPinfuHand && ctx.tsumo) return 20;
    if (isPinfuHand && !ctx.tsumo) return 30; // 平和ロン
    let fu = 20;
    // 面子符
    for (const s of sets) {
      if (s.type === 'kou') {
        let base = M.isYaochu(s.t) ? 8 : 4; // 暗刻基準
        const isAnkou = !s.open && !(!ctx.tsumo && ctx.winTile === s.t && !s.kan);
        if (s.kan) {
          base = M.isYaochu(s.t) ? 32 : 16; // 槓
          if (s.open) base /= 2; // 明槓
        } else {
          if (!isAnkou) base /= 2; // 明刻
        }
        fu += base;
      }
    }
    // 雀頭符(役牌)
    if (pair === M.HAKU || pair === M.HATSU || pair === M.CHUN) fu += 2;
    if (pair === ctx.seatWind && pair >= 27) fu += 2;
    if (pair === ctx.roundWind && pair >= 27) fu += 2;
    // 待ち符
    fu += waitFu(ctx, sets, pair);
    // ツモ符
    if (ctx.tsumo) fu += 2;
    // 門前ロン
    if (isMenzen && !ctx.tsumo) fu += 10;
    // 切り上げ
    fu = Math.ceil(fu / 10) * 10;
    if (fu < 20) fu = 20;
    return fu;
  };
  function waitFu(ctx, sets, pair) {
    const w = ctx.winTile;
    // 単騎
    if (w === pair) return 2;
    for (const s of sets) {
      if (s.type === 'shun') {
        const n = s.t % 9;
        // 嵌張: 真ん中
        if (w === s.t + 1) return 2;
        // 辺張: 123の3待ち or 789の7待ち
        if (n === 0 && w === s.t + 2) return 2;
        if (n === 6 && w === s.t) return 2;
      }
    }
    return 0; // 両面/双碰は0
  }

  // ============================================================
  //  最終点数計算
  // ============================================================
  function finalize(ctx, yaku, fu, isYakuman, opt = {}) {
    let han = yaku.reduce((a, y) => a + y.han, 0);
    const yakumanCount = yaku.filter(y => y.han >= 13).length;
    let dora = 0;
    if (!isYakuman) {
      dora = countDora(ctx, ctx._allCounts || allCountsOf(ctx));
      han += dora;
    }
    let total, label;
    const parent = ctx.isParent;

    if (isYakuman) {
      const multi = yaku.reduce((a, y) => a + Math.floor(y.han / 13), 0);
      const base = 8000 * multi;
      total = parent ? base * 1.5 * (ctx.tsumo ? 1 : 1) : base;
      // 役満は固定
      if (parent) total = 48000 * multi; else total = 32000 * multi;
      label = multi >= 2 ? `${multi}倍役満` : '役満';
      return packResult(ctx, yaku, fu, han, dora, total, label, true);
    }

    // 通常
    let basePoints = fu * Math.pow(2, 2 + han);
    let limitLabel = '';
    if (han >= 13) { basePoints = 8000; limitLabel = '数え役満'; }
    else if (han >= 11) { basePoints = 6000; limitLabel = '三倍満'; }
    else if (han >= 8) { basePoints = 4000; limitLabel = '倍満'; }
    else if (han >= 6) { basePoints = 3000; limitLabel = '跳満'; }
    else if (basePoints >= 2000) { basePoints = 2000; limitLabel = '満貫'; }

    let payments;
    if (ctx.tsumo) {
      if (parent) {
        const each = Math.ceil(basePoints * 2 / 100) * 100;
        total = each * 3;
        payments = { all: each };
      } else {
        const parentPay = Math.ceil(basePoints * 2 / 100) * 100;
        const childPay = Math.ceil(basePoints / 100) * 100;
        total = parentPay + childPay * 2;
        payments = { parent: parentPay, child: childPay };
      }
    } else {
      const mult = parent ? 6 : 4;
      total = Math.ceil(basePoints * mult / 100) * 100;
      payments = { ron: total };
    }
    label = limitLabel;
    return packResult(ctx, yaku, fu, han, dora, total, label, false, payments);
  }

  function allCountsOf(ctx) {
    const c = new Array(34).fill(0);
    for (const t of ctx.hand) c[t]++;
    c[ctx.winTile]++;
    for (const m of (ctx.melds || [])) for (const t of m.tiles) c[t]++;
    return c;
  }

  function packResult(ctx, yaku, fu, han, dora, total, label, yakuman, payments) {
    return {
      yaku: yaku.filter(y => y.han > 0 || yakuman),
      fu, han, dora, total, label, yakuman,
      payments: payments || {},
      tsumo: ctx.tsumo
    };
  }

  // ドラ用 allCounts を事前計算してctxに載せる
  M.prepareScore = function (ctx) {
    ctx._allCounts = allCountsOf(ctx);
    return M.score(ctx);
  };

  if (typeof module !== 'undefined' && module.exports) module.exports = M;
  global.MJ = M;
})(typeof window !== 'undefined' ? window : globalThis);
