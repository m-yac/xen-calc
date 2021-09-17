(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}g.microtonal_utils = f()}})(function(){var define,module,exports;return (function(){function r(e,n,t){function o(i,f){if(!n[i]){if(!e[i]){var c="function"==typeof require&&require;if(!f&&c)return c(i,!0);if(u)return u(i,!0);var a=new Error("Cannot find module '"+i+"'");throw a.code="MODULE_NOT_FOUND",a}var p=n[i]={exports:{}};e[i][0].call(p.exports,function(r){var n=e[i][1][r];return o(n||r)},p,p.exports,r,e,n,t)}return n[i].exports}for(var u="function"==typeof require&&require,i=0;i<t.length;i++)o(t[i]);return o}return r})()({1:[function(require,module,exports){
/**
 * Best rational and EDO approximations of intervals
 * @copyright 2021 Matthew Yacavone (matthew [at] yacavone [dot] net)
 * @module approx
 **/

const {fractionalPart, cachedLog2} = require('./utils.js');
const pf = require('primes-and-factors');
const Fraction = require('fraction.js');
const Interval = require('./interval.js');
const {edoApprox, edoApproxConsistentWithErr} = require('./edo.js');
const {ratioPermsByNo2sHeight, ratioPermsByHeight, ratiosWithDenom, ratiosInOddLimit} = require('./sets.js');

// The epsilon to use when comparing approximate distances
const epsilon = 1e-5;

/**
  * Determines the iteration size of `bestRationalApproxsByNo2sHeight` using
  * heuristics based on the primeLimit given.
  *
  * @param {integer} [primeLimit]
  * @returns {integer}
  */
function bestRationalApproxsByNo2sHeightIterationSize(primeLimit) {
  if (primeLimit) {
    // for large prime limits, this iteration size is approximately half the
    // prime limit itself, but for small prime limits (roughly less than 47)
    // this is larger, to account for the fact that valid intervals are sparser
    return Math.ceil(2000/primeLimit + (primeLimit+1)/2);
  }
  return 100;
}

/**
  * Finds best rational approximations of the given interval, sorted by the
  * Tenney height (or equivalently, Tenney harmonic distance) of the interval
  * with all factors of 2 removed. Returns a pair whose first element is true
  * iff an exact approximaion has been be found.
  *
  * @param {Interval} i
  * @param {Object} [opts]
  * @param {integer} [opts.cutoff] defaults to 50 cents
  * @param {integer} [opts.primeLimit]
  * @param {integer} [opts.oddLimit]
  * @param {integer} [opts.startIteration] defaults to 0
  * @param {integer} [opts.numIterations] defaults to 1
  * @param {boolean} [opts.useExactDiffs] defaults to false, controls the type
  *                                       of each 'diff' property
  * @param {boolean} [opts.debug] defaults to false
  * @returns {Pair.<boolean, Array.<{ratio: Fraction, diff: (number|Interval)}>>}
  */
function bestRationalApproxsByNo2sHeight(a,b, opts) {
  // if only two arguments are given, the second one may be `opts`!
  if (!opts) {
    if (typeof b == 'object' && b != null) {
      opts = b;
      b = undefined;
    } else {
      opts = {};
    }
  }
  const intv = Interval(a,b);
  const intv_logval = intv.valueOf_log();
  let {cutoff, primeLimit, oddLimit, startIteration, numIterations, useExactDiffs, debug} = opts;
  if (debug) { console.time("bestRationalApproxsByNo2sHeight"); }

  // some heuristics for the iteration size, i.e. the number of odd numbers
  // to check in a given iteration
  const iterationSize = bestRationalApproxsByNo2sHeightIterationSize(primeLimit);

  // a prime limit of 2 means we also have an odd limit of 1!
  if (primeLimit && primeLimit <= 2) { oddLimit = 1; }

  if (cutoff == undefined) { cutoff = Interval(2).pow(1,12).sqrt(); }
  if (startIteration == undefined) { startIteration = 0; }
  if (numIterations == undefined) { numIterations = 1; }
  const startOdd = 2 * startIteration * iterationSize + 1;
  const endOdd = 2 * (startIteration + numIterations) * iterationSize + 1;

  let [foundExact, ret] = [false, []];
  let [dist_bound, approx_dist_bound] = [cutoff, cutoff.valueOf_log() + epsilon];
  for (const [i, perms] of ratioPermsByNo2sHeight(startOdd, endOdd, {primeLimit: primeLimit})) {
    let to_add = [];
    let [new_dist_bound, new_approx_dist_bound] = [dist_bound, approx_dist_bound];
    for (const [j_no2s, j_no2s_logval] of perms) {
      const j_approx_dist = Math.abs(fractionalPart(j_no2s_logval - intv_logval));
      if (j_approx_dist < approx_dist_bound) {
        const j_diff = j_no2s.div(intv).reb();
        const j = j_diff.mul(intv);
        if (!oddLimit || j.inOddLimit(oddLimit)) {
          const j_dist = j_diff.distance();
          if (j_dist.compare(dist_bound) <= 0) {
            new_dist_bound = j_dist;
            new_approx_dist_bound = j_approx_dist + epsilon;
            to_add.push([j, j_diff, j_dist]);
          }
        }
      }
    }
    to_add.sort(function([a, a_diff, a_dist], [b, b_diff, b_dist]) {
      if (b_dist.equals(a_dist)) { return a_diff.compare(b_diff); }
      return b_dist.compare(a_dist);
    });
    for (const [j, j_diff, j_dist] of to_add) {
      ret.push({ ratio: j.toFrac(), diff: useExactDiffs ? j_diff : j_diff.toCents() });
    }
    [dist_bound, approx_dist_bound] = [new_dist_bound, new_approx_dist_bound];
    if (dist_bound.equals(1)) { foundExact = true; break; };
  }
  if (debug) {
    console.timeEnd("bestRationalApproxsByNo2sHeight");
    if (foundExact) {
      console.log("bestRationalApproxsByNo2sHeight: exhausted")
    }
  }
  return [foundExact, ret];
}

/**
  * Determines the iteration size of `bestRationalApproxsByHeight` using
  * heuristics based on the primeLimit given.
  *
  * @param {integer} [primeLimit]
  * @returns {integer}
  */
function bestRationalApproxsByHeightIterationSize(primeLimit) {
  return 16*bestRationalApproxsByNo2sHeightIterationSize(primeLimit);
}

/**
  * Finds best rational approximations of the given interval, sorted by Tenney
  * height, or equivalently, Tenney harmonic distance. Returns a pair whose
  * first element is true iff an exact approximaion has been be found.
  *
  * @param {Interval} i
  * @param {Object} [opts]
  * @param {integer} [opts.cutoff] defaults to 50 cents
  * @param {integer} [opts.primeLimit]
  * @param {integer} [opts.oddLimit]
  * @param {integer} [opts.startIteration] defaults to 0
  * @param {integer} [opts.numIterations] defaults to 1
  * @param {boolean} [opts.useExactDiffs] defaults to false, controls the type
  *                                       of each 'diff' property
  * @param {boolean} [opts.debug] defaults to false
  * @returns {Pair.<boolean, Array.<{ratio: Fraction, diff: (number|Interval)}>>}
  */
function bestRationalApproxsByHeight(a,b, opts) {
  // if only two arguments are given, the second one may be `opts`!
  if (!opts) {
    if (typeof b == 'object' && b != null) {
      opts = b;
      b = undefined;
    } else {
      opts = {};
    }
  }
  const intv = Interval(a,b);
  const intv_logval = intv.valueOf_log();
  let {cutoff, primeLimit, oddLimit, startIteration, numIterations, useExactDiffs, debug} = opts;
  if (debug) { console.time("bestRationalApproxsByHeight"); }

  // some heuristics for the iteration size
  const iterationSize = bestRationalApproxsByHeightIterationSize(primeLimit);

  // a prime limit of 2 means we also have an odd limit of 1!
  if (primeLimit && primeLimit <= 2) { oddLimit = 1; }

  if (cutoff == undefined) { cutoff = Interval(2).pow(1,12).sqrt(); }
  if (startIteration == undefined) { startIteration = 0; }
  if (numIterations == undefined) { numIterations = 1; }
  const start = startIteration * iterationSize + 1
  const end = (startIteration + numIterations) * iterationSize + 1;

  let [foundExact, ret] = [false, []];
  let [dist_bound, approx_dist_bound] = [cutoff, cutoff.valueOf_log() + epsilon];
  for (const [i, perms] of ratioPermsByHeight(start, end, {primeLimit: primeLimit, oddLimit: oddLimit})) {
    let to_add = [];
    let [new_dist_bound, new_approx_dist_bound] = [dist_bound, approx_dist_bound];
    for (const [j, j_logval] of perms) {
      const j_approx_dist = Math.abs(j_logval - intv_logval);
      if (j_approx_dist < approx_dist_bound) {
        const j_diff = j.div(intv);
        const j_dist = j_diff.distance();
        if (j_dist.compare(dist_bound) <= 0) {
          new_dist_bound = j_dist;
          new_approx_dist_bound = j_approx_dist + epsilon;
          to_add.push([j, j_diff, j_dist]);
        }
      }
    }
    to_add.sort(function([a, a_diff, a_dist], [b, b_diff, b_dist]) {
      if (b_dist.equals(a_dist)) { return a_diff.compare(b_diff); }
      return b_dist.compare(a_dist);
    });
    for (const [j, j_diff, j_dist] of to_add) {
      ret.push({ ratio: j.toFrac(), diff: useExactDiffs ? j_diff : j_diff.toCents() });
    }
    [dist_bound, approx_dist_bound] = [new_dist_bound, new_approx_dist_bound];
    if (dist_bound.equals(1)) { foundExact = true; break; };
  }
  if (debug) {
    console.timeEnd("bestRationalApproxsByHeight");
    if (foundExact) {
      console.log("bestRationalApproxsByHeight: exhausted")
    }
  }
  return [foundExact, ret];
}

/**
  * Finds best rational approximations of the given interval, sorted by
  * denominator. Returns a pair whose first element is true iff no better
  * approximaions can be found - i.e. if an exact approximation is found.
  *
  * @param {Interval} i
  * @param {Object} [opts]
  * @param {integer} [opts.cutoff] defaults to 50 cents
  * @param {integer} [opts.primeLimit]
  * @param {integer} [opts.oddLimit]
  * @param {integer} [opts.startIteration] defaults to 0
  * @param {integer} [opts.numIterations] defaults to 1
  * @param {integer} [opts.iterationSize] defaults to 100
  * @param {boolean} [opts.useExactDiffs] defaults to false, controls the type
  *                                       of each 'diff' property
  * @param {boolean} [opts.debug] defaults to false
  * @returns {Pair.<boolean, Array.<{ratio: Fraction, diff: (number|Interval)}>>}
  */
function bestRationalApproxsByDenom(a,b, opts) {
  // if only two arguments are given, the second one may be `opts`!
  if (!opts) {
    if (typeof b == 'object' && b != null) {
      opts = b;
      b = undefined;
    } else {
      opts = {};
    }
  }
  const intv = Interval(a,b);
  const intv_logval = intv.valueOf_log();
  let {cutoff, primeLimit, oddLimit, startIteration, numIterations, iterationSize, useExactDiffs, debug} = opts;
  if (debug) { console.time("bestRationalApproxsByDenom"); }

  if (cutoff == undefined) { cutoff = Interval(2).pow(1,12).sqrt(); }
  if (startIteration == undefined) { startIteration = 0; }
  if (numIterations == undefined) { numIterations = 1; }
  if (iterationSize == undefined) { iterationSize = 100; }
  let d_max = (startIteration + numIterations) * iterationSize + 1;

  let [foundExact, ret] = [false, []];
  let dist_bound = cutoff;
  for (let d = startIteration * iterationSize + 1; !foundExact && d < d_max; d++) {
    const ropts = {lo: intv.div(dist_bound), hi: intv.mul(dist_bound),
                   primeLimit: primeLimit, oddLimit: oddLimit};
    for (const r of ratiosWithDenom(d, ropts)) {
      const i = Interval(r);
      const diff = i.div(intv);
      const dist = diff.distance();
      if (dist.compare(dist_bound) <= 0) {
        dist_bound = dist;
        ret.push({ ratio: r, diff: useExactDiffs ? diff : diff.toCents() });
        if (dist_bound.equals(1)) { foundExact = true; break; };
      }
    }
  }
  if (debug) { console.timeEnd("bestRationalApproxsByDenom"); }
  return [foundExact, ret];
}

/**
  * Finds best rational approximations in the given odd limit of the given
  * interval, sorted by error.
  *
  * @param {Interval} i
  * @param {Object} opts
  * @param {integer} [opts.primeLimit]
  * @param {integer} opts.oddLimit
  * @param {boolean} [opts.useExactDiffs] defaults to false, controls the type
  *                                       of each 'diff' property
  * @param {boolean} [opts.debug] defaults to false
  * @returns {Array.<{ratio: Fraction, diff: (number|Interval)}>}
  */
function bestRationalApproxsByDiff(a,b, opts) {
  // if only two arguments are given, the second one may be `opts`!
  if (!opts) {
    if (typeof b == 'object' && b != null) {
      opts = b;
      b = undefined;
    } else {
      opts = {};
    }
  }
  const intv = Interval(a,b);
  let {cutoff, primeLimit, oddLimit, useExactDiffs, debug} = opts;
  if (!isFinite(oddLimit) || oddLimit <= 0) {
    throw new Error("no valid odd limit given to bestRationalApproxsByDiff!");
  }
  if (debug) { console.time("bestRationalApproxsByDiff"); }

  if (cutoff == undefined) { cutoff = Interval(2).pow(1,12).sqrt(); }
  const ropts = {lo: intv.div(cutoff), hi: intv.mul(cutoff), primeLimit: primeLimit};

  let ret = [];
  for (const r of ratiosInOddLimit(oddLimit, ropts)) {
    const j = Interval(r);
    const diff = j.div(intv);
    const dist = diff.distance();
    const approx_dist = dist.valueOf_log();
    const to_add = { ratio: r, diff: diff, dist: dist, dist_bound: approx_dist + epsilon };
    let added = false;
    for (let i = 0; !added && i < ret.length; i++) {
      if (approx_dist < ret[i].dist_bound
          && ((dist.equals(ret[i].dist) && diff.compare(ret[i].diff) < 0)
              || dist.compare(ret[i].dist) < 0)) {
        ret.splice(i, 0, to_add);
        added = true;
      }
    }
    if (!added) {
      ret.push(to_add);
    }
  }

  if (debug) { console.timeEnd("bestRationalApproxsByDiff"); }
  return ret.map(x => ({ ratio: x.ratio, diff: useExactDiffs ? x.diff : x.diff.toCents() }));
}

/**
  * Finds best rational approximations of each of the intervals in an octave of
  * the given EDO.
  *
  * @param {integer} edo
  * @param {Object} [opts]
  * @param {integer} [opts.relCutoff] defaults to 2/3
  * @param {integer} [opts.primeRelErrCutoff] defaults to 2/3
  * @param {boolean} [opts.ensureSameDeg] defaults to false
  * @param {integer} [opts.primeLimit]
  * @param {integer} [opts.oddLimit]
  * @param {integer} [opts.startIteration] defaults to 0
  * @param {integer} [opts.numIterations] defaults to 1
  * @param {integer} [opts.iterationSizeMultiplier] defaults to 4
  * @param {boolean} [opts.useExactDiffs] defaults to false, controls the type
  *                                       of each 'diff' property
  * @param {boolean} [opts.debug] defaults to false
  * @returns {Array.<Array.<{ratio: Fraction, diff: (number|Interval)}>>}
  */
function bestRationalApproxsOfEDOByStep(edo, opts) {
  let {relCutoff, primeRelErrCutoff, ensureSameDeg, primeLimit, oddLimit, startIteration, numIterations, iterationSizeMultiplier, useExactDiffs, debug} = opts || {};
  if (debug) { console.time("bestRationalApproxsOfEDOByStep"); }

  if (relCutoff == undefined) { relCutoff = 2/3; }
  if (primeRelErrCutoff == undefined) { primeRelErrCutoff = 2/3; }
  const cutoff = relCutoff / (2 * edo);
  const primeErrCutoff = primeRelErrCutoff / (2 * edo);

  // a prime limit of 2 means we also have an odd limit of 1!
  if (primeLimit && primeLimit <= 2) { oddLimit = 1; }

  if (startIteration == undefined) { startIteration = 0; }
  if (numIterations == undefined) { numIterations = 1; }
  if (iterationSizeMultiplier == undefined) { iterationSizeMultiplier = 4; }
  const iterationSize = iterationSizeMultiplier * edo;
  const startOdd = 2 * startIteration * iterationSize + 1;
  const endOdd = 2 * (startIteration + numIterations) * iterationSize + 1;

  let ret = [];
  for (let i = 0; i < edo; i++) {
    ret.push([]);
  }
  for (const [i, perms] of ratioPermsByNo2sHeight(1, endOdd, {primeLimit: primeLimit})) {
    for (const [j_no2s, j_no2s_logval] of perms) {

      let {n, max_prime_err} = edoApproxConsistentWithErr(edo, j_no2s);
      if (n != edoApprox(edo, j_no2s)) { continue; }
      if (max_prime_err > primeErrCutoff) { continue; }

      const e2 = - Math.floor(n / edo);
      const j = j_no2s.mul(Interval(2).pow(e2));

      if (oddLimit && !j.inOddLimit(oddLimit)) { continue; }
      if (ensureSameDeg) {
        const d = colorZDegree(j);
        if (updnsSymbCache(edo)[n].every(([uds,pyi]) => pyZDegree(pyi) != d)) {
          continue;
        }
      }

      const j_logval = j_no2s_logval + e2;
      n += edo * e2;
      const approx_dist = Math.abs(j_logval - n / edo);

      if (approx_dist < cutoff + epsilon) {
        const diff = j.div(Interval(2).pow(n,edo));
        const dist = diff.distance();
        const to_add = { ratio: j.toFrac(), diff: diff, dist: dist, dist_bound: approx_dist + epsilon };
        let added = false;
        for (let i = 0; !added && i < ret[n].length; i++) {
          if (approx_dist < ret[n][i].dist_bound
              && ((dist.equals(ret[n][i].dist) && diff.compare(ret[n][i].diff) < 0)
                  || dist.compare(ret[n][i].dist) < 0)) {
            ret[n].splice(i, 0, to_add);
            added = true;
          }
        }
        if (!added) {
          ret[n].push(to_add);
        }
      }
    }
  }
  if (debug) { console.timeEnd("bestRationalApproxsOfEDOByStep"); }
  return ret.map(xs => xs.map(x => ({ ratio: x.ratio, diff: useExactDiffs ? x.diff : x.diff.toCents() })));
}

/**
  * Finds best rational approximations in the given odd limit in the given EDO,
  * sorted by error
  *
  * @param {integer} edo
  * @param {Object} opts
  * @param {integer} [opts.primeRelErrCutoff] defaults to 2/3
  * @param {integer} [opts.primeLimit]
  * @param {integer} opts.oddLimit
  * @param {boolean} [opts.useExactDiffs] defaults to false, controls the type
  *                                       of each 'diff' property
  * @param {boolean} [opts.debug] defaults to false
  * @returns {Array.<{ratios:Array.<Fraction>, dist: (number|Interval)}>}
  */
function bestRationalApproxsOfEDOByDist(edo, opts) {
  let {primeRelErrCutoff, primeLimit, oddLimit, useExactDiffs, debug} = opts;
  if (!isFinite(oddLimit) || oddLimit <= 0) {
    throw new Error("no valid odd limit given to bestRationalApproxsOfEDOByDist!");
  }
  if (debug) { console.time("bestRationalApproxsOfEDOByDist"); }

  if (primeRelErrCutoff == undefined) { primeRelErrCutoff = 2/3; }
  const primeErrCutoff = primeRelErrCutoff / (2 * edo);

  const ropts = { lo: Interval(1), hi: Interval(2).sqrt(), primeLimit: primeLimit };

  let ret = [];
  for (const r of ratiosInOddLimit(oddLimit, ropts)) {
    const j = Interval(r);
    if (j.inPrimeLimit(2)) { continue; }
    const m = edoApprox(edo, j);
    const dist = j.div(Interval(2).pow(m,edo)).distance();
    const approx_dist = dist.valueOf_log();
    let to_add = { ratios: [r, r.inverse().mul(2)], dist: dist, dist_bound: approx_dist + epsilon };
    const {n, max_prime_err} = edoApproxConsistentWithErr(edo, j);
    if (n != m) { to_add.inconsistent = true; }
    if (max_prime_err > primeErrCutoff) { to_add.overErr = true; }
    let added = false;
    for (let i = 0; !added && i < ret.length; i++) {
      if (approx_dist < ret[i].dist_bound && dist.compare(ret[i].dist) < 0) {
        ret.splice(i, 0, to_add);
        added = true;
      }
    }
    if (!added) {
      ret.push(to_add);
    }
  }

  if (debug) { console.timeEnd("bestRationalApproxsOfEDOByDist"); }
  return ret.map(function (x) {
    let x0 = { ratios: x.ratios, dist: useExactDiffs ? x.dist : x.dist.toCents() };
    if (x.inconsistent) { x0.inconsistent = true; }
    if (x.overErr) { x0.overErr = true; }
    return x0;
  });
}

/**
  * Finds best EDO step approximations of the given interval, sorted by EDO
  * size.
  *
  * @param {Interval} i
  * @param {Object} [opts]
  * @param {integer} [opts.cutoff] defaults to 50 cents
  * @param {integer} [opts.startEDO] defaults to 5
  * @param {integer} [opts.endEDO] defaults to 60
  * @param {boolean} [opts.useExactDiffs] defaults to false, controls the type
  *                                       of each 'diff' property
  * @returns {Array.<{steps: Array, diff: (number|Interval)}>}
  */
function bestEDOApproxsByEDO(a,b, opts) {
  // if only two arguments are given, the second one may be `opts`!
  if (!opts) {
    if (typeof b == 'object' && b != null) {
      opts = b;
      b = undefined;
    } else {
      opts = {};
    }
  }
  const intv = Interval(a,b);
  const intv_logval = intv.valueOf_log();
  if (opts == undefined) { opts = {}; }
  let {cutoff, startEDO, endEDO, useExactDiffs, debug} = opts;
  if (cutoff == undefined) { cutoff = Interval(2).pow(1,12).sqrt(); }
  if (startEDO == undefined) { startEDO = 5; }
  if (endEDO == undefined) { endEDO = 60; }
  if (debug) { console.time("bestEDOApproxsByEDO"); }

  let [foundExact, ret] = [false, []];
  let [dist_bound, approx_dist_bound] = [cutoff, cutoff.valueOf_log() + epsilon];
  for (let edo = startEDO; edo <= endEDO; edo++) {
    const steps = edoApprox(edo, intv);
    const approx_dist = Math.abs(steps/edo - intv_logval);
    if (approx_dist < approx_dist_bound) {
      const diff = Interval(2).pow(steps,edo).div(intv);
      const dist = diff.distance();
      if (dist.equals(dist_bound) && ret.length > 0) {
        ret[ret.length - 1].steps.push([steps, edo]);
      }
      else if (dist.compare(dist_bound) <= 0 && !foundExact) {
        dist_bound = dist;
        approx_dist_bound = approx_dist + epsilon;
        ret.push({ steps: [[steps,edo]], diff: useExactDiffs ? diff : diff.toCents() });
        if (dist_bound.equals(1)) { foundExact = true };
      }
    }
  }

  if (debug) { console.timeEnd("bestEDOApproxsByEDO"); }
  return ret;
}

/**
  * Finds best EDO step approximations of the given interval, sorted by error.
  *
  * @param {Interval} i
  * @param {Object} [opts]
  * @param {integer} [opts.startEDO] defaults to 5
  * @param {integer} [opts.endEDO] defaults to 60
  * @param {boolean} [opts.useExactDiffs] defaults to false, controls the type
  *                                       of each 'diff' property
  * @returns {Array.<{steps: Array, diff: (number|Interval)}>}
  */
function bestEDOApproxsByDiff(a,b, opts) {
  // if only two arguments are given, the second one may be `opts`!
  if (!opts) {
    if (typeof b == 'object' && b != null) {
      opts = b;
      b = undefined;
    } else {
      opts = {};
    }
  }
  const intv = Interval(a,b);
  if (opts == undefined) { opts = {}; }
  let {startEDO, endEDO, useExactDiffs, debug} = opts;
  if (startEDO == undefined) { startEDO = 5; }
  if (endEDO == undefined) { endEDO = 60; }
  if (debug) { console.time("bestEDOApproxsByDiff"); }

  let ret = [];
  for (let edo = startEDO; edo <= endEDO; edo++) {
    const steps = edoApprox(edo, intv);
    const diff = Interval(2).pow(steps,edo).div(intv);
    const dist = diff.distance();
    const approx_dist = dist.valueOf_log();
    const to_add = { steps: [[steps, edo]], diff: diff,
                     dist: dist, dist_bound: approx_dist + epsilon };
    let added = false;
    for (let i = 0; !added && i < ret.length; i++) {
      if (approx_dist < ret[i].dist_bound) {
        if (diff.equals(ret[i].diff)) {
          ret[i].steps.push([steps,edo]);
          added = true;
        }
        else if (dist.compare(ret[i].dist) < 0) {
          ret.splice(i, 0, to_add);
          added = true;
        }
      }
    }
    if (!added) {
      ret.push(to_add);
    }
  }

  if (debug) { console.timeEnd("bestEDOApproxsByDiff"); }
  return ret.map(x => ({ steps: x.steps, diff: useExactDiffs ? x.diff : x.diff.toCents() }));
}

module.exports.bestRationalApproxsByNo2sHeightIterationSize = bestRationalApproxsByNo2sHeightIterationSize;
module.exports.bestRationalApproxsByNo2sHeight = bestRationalApproxsByNo2sHeight;
module.exports.bestRationalApproxsByHeightIterationSize = bestRationalApproxsByHeightIterationSize;
module.exports.bestRationalApproxsByHeight = bestRationalApproxsByHeight;
module.exports.bestRationalApproxsByDenom  = bestRationalApproxsByDenom;
module.exports.bestRationalApproxsByDiff   = bestRationalApproxsByDiff;
module.exports.bestRationalApproxsOfEDOByStep = bestRationalApproxsOfEDOByStep;
module.exports.bestRationalApproxsOfEDOByDist = bestRationalApproxsOfEDOByDist;
module.exports.bestEDOApproxsByEDO  = bestEDOApproxsByEDO;
module.exports.bestEDOApproxsByDiff = bestEDOApproxsByDiff;

},{"./edo.js":3,"./interval.js":7,"./sets.js":12,"./utils.js":13,"fraction.js":16,"primes-and-factors":20}],2:[function(require,module,exports){
/**
 * Color notation for intervals
 * Based on: https://en.xen.wiki/w/Color_notation
 * @copyright 2021 Matthew Yacavone (matthew [at] yacavone [dot] net)
 * @module color
 **/

const {sign1, mod} = require('./utils.js')
const {gcd} = require('mathutils');
const pf = require('primes-and-factors');
const Fraction = require('fraction.js');
const Interval = require('./interval.js');
const {pyDegreeString, pyNote} = require('./pythagorean.js');

/**
  * The regions of the octave used when determining the degree of a prime in
  * color notation
  *
  * @constant {Array.<Interval>}
  */
const colorRegions = [ Interval([Fraction( 1,24)]) /*    0c -  50c */
                     , Interval([Fraction( 5,24)]) /*   50c - 250c */
                     , Interval([Fraction( 9,24)]) /*  250c - 450c */
                     , Interval([Fraction(12,24)]) /*  450c - 600c */
                     , Interval([Fraction(15,24)]) /*  600c - 750c */
                     , Interval([Fraction(19,24)]) /*  750c - 950c */
                     , Interval([Fraction(23,24)]) /*  950c -1150c */
                     , Interval([Fraction(24,24)]) /* 1150c -1200c */ ];

let colorCache_var = {};

/**
  * Returns the "zeroed" degree of the given prime in color notation
  *
  * @param {integer} p a prime
  * @returns {integer}
  */
function colorPrimeZDegree(p) {
  if (colorCache_var[p]) {
    return colorCache_var[p];
  }
  if (!pf.isPrime(p)) {
    throw new Error("colorPrimeZDegree not given a prime");
  }
  const i = Interval(p).red();
  const dNo2 = colorRegions.findIndex(hi => i.compare(hi) < 0);
  const d = dNo2 - 7 * i.div(p).valueOf_log()
  colorCache_var[p] = d;
  return d;
}

/**
  * Returns the "zeroed" degree of a the given interval in color notation
  *
  * @param {Interval} i
  * @returns {integer}
  */
function colorZDegree(a,b) {
  const i = Interval(a,b);
  let zd = 0;
  for (const [p,e] of i.factors()) {
    zd += colorPrimeZDegree(p) * e.valueOf();
  }
  return zd;
}

/**
  * Returns the degree of a the given interval in color notation.
  *
  * @param {Interval} i
  * @returns {integer}
  */
function colorDegree(a,b) {
  const zd = colorZDegree(a,b);
  return zd + sign1(zd);
}

/**
  * Returns the magnitude of a the given interval in color notation
  *
  * @param {Interval} i
  * @returns {integer}
  */
function colorMagnitude(a,b) {
  const i = Interval(a,b);
  let sum = Fraction(0);
  for (const [p,e] of i.factors()) {
    if (p > 2) {
      sum = sum.add(e);
    }
  }
  return Math.round(sum.valueOf() / 7);
}

/**
  * Returns the prefix of the given prime in color notation. If v = "o", return
  * the otonal prefix (e.g. yo). If v = "u", return the utonal prefix (e.g. gu).
  * If v = "e", return the multi prefix (e.g. quin);
  *
  * @param {integer} p a prime
  * @param {string} v either "e", "o", or "u"
  * @param {boolean} [abbreviate=false]
  * @returns {string}
  */
function colorPrimePrefix(p, v, abbreviate) {
  if (v != "e" && v != "o" && v != "u") {
    throw new Error("Invalid vowel passed to colorPrimePrefix");
  }
  if (p == 2) {
    if (v == "e") { return "bi"; }
    return "";
  }
  if (p == 3) {
    if (v == "e") { return "tri"; }
    return "w" + (abbreviate ? "" : "a");
  }
  if (p == 5) {
    if (v == "e") { return "quin"; }
    if (v == "o") { return "y" + (abbreviate ? "" : v); }
    if (v == "u") { return "g" + (abbreviate ? "" : v); }
  }
  if (p == 7) {
    if (v == "e") { return "sep"; }
    if (v == "o") { return "z" + (abbreviate ? "" : v); }
    if (v == "u") { return "r" + (abbreviate ? "" : v); }
  }
  if (abbreviate && v != "e") {
    if (p == 11) { return "1" + v; }
    if (p == 13) { return "3" + v; }
    return p + v;
  }
  else {
    if (p == 11) { return "l" + v; }
    if (p > 67) {
      throw new Error("Prime larger than 67 passed to colorPrimePrefix");
    }
    const [tens, ones] = [Math.floor(p / 10), p % 10];
    return { 1: "", 2: "twe", 3: "thi", 4: "fo", 5: "fi", 6: "si"}[tens] +
           { 1: "w", 3: "th", 7: "s", 9: "n" }[ones] + v;
  }
}

/**
  * Returns the multi prefix of the positive integer in color notation (e.g.
  * "quinbi" for 10).
  *
  * @param {integer} n
  * @returns {string}
  */
function colorMultiPrefix(n) {
  const fs = pf.getPrimeExponentObject(n);
  let fs_arr = [];
  if (fs[2] % 2) { fs_arr.push([2, fs[2] % 2]); }
  if (fs[3])     { fs_arr.push([3, fs[3]]); }
  if (fs[2] > 1) { fs_arr.push([4, Math.floor(fs[2]/2)]); }
  delete fs[2];
  delete fs[3];
  fs_arr = fs_arr.concat(Object.entries(fs));
  let res = "";
  for (const [p,e] of fs_arr) {
    const prefix = p == 4 ? "quad" : colorPrimePrefix(p, "e");
    res = prefix.repeat(e.valueOf()) + res;
  }
  return res;
}

/**
  * Returns the otonal/utonal prefix of the given prime power in color notation
  *
  * @param {integer} p a prime
  * @param {integer} e the prime exponent
  * @param {Object=} opts
  * @param {integer=} opts.verbosity verbosity can be the default 0
  *                                  (e.g. "17ooo"), 1 (e.g. "triso-a"), or 2
  *                                  (the same as 1 for this function)
  * @param {boolean=} opts.useExps defaults to false
  * @param {boolean=} opts.useHTMLExps defaults to false
  * @returns {string}
  */
function colorFactorPrefix(p, e, opts) {
  if (e == 0) { return ""; }
  if (opts == undefined) { opts = {}; }
  let {verbosity, useExps, useHTMLExps} = opts;
  if (verbosity == undefined) { verbosity = 0; }

  const base = colorPrimePrefix(p, e > 0 ? "o" : "u", verbosity == 0);
  const eAbs = Math.abs(e);
  if (verbosity == 0) {
    if (eAbs == 1) { return base; }
    if (eAbs == 2) { return base + base[base.length-1]; }
    if (useHTMLExps) { return base + "<sup>" + eAbs + "</sup>"; }
    if (useExps) {
      if ((''+eAbs).length == 1) { return base + "^" + eAbs; }
      else { return base + "^(" + eAbs + ")"; }
    }
    return base + base[base.length-1].repeat(eAbs-1);
  }
  else {
    if (eAbs == 1) { return base; }
    if (eAbs == 2) { return base + base; }
    return colorMultiPrefix(eAbs) + base + "-a";
  }
}

// An algorithm to find all the groupings possible in a color prefix

// Classes to represent the way a color prefix may be grouped
// e.g. [ Group { d: 2,
//                gs: [ End { p: 11, e: Fraction(1) },
//                      Group { d: 3,
//                              gs: [ End { p: 7, e: Fraction(-1) } ] } ] },
//        Group { d: 3,
//                gs: [ End { p: 5, e: Fraction(1) } ] } ]
//      corresponds to bilotriru-atriyo
class End {
  constructor(p,e) {
    this.p = p;
    this.e = e;
  }
}
class Group {
  constructor(d, gs) {
    this.d = d;
    this.gs = gs;
  }
}

// Checks whether two class representations of color prefixes are the same
function eqPrefixes(p1, p2) {
  if (p1.length != p2.length) { return false; }
  for (let i = 0; i < p1.length; i++) {
    if (p1[i].constructor != p2[i].constructor) { return false; }
    if (p1[i] instanceof End) {
      return p1[i].p == p2[i].p && p1[i].e.equals(p2[i].e);
    }
    if (p1[i] instanceof Group) {
      return p1[i].d == p2[i].d && eqPrefixes(p1[i].gs, p2[i].gs);
    }
  }
}

// Converts a class representation of a color prefix to a string
function groupingToString(gs, opts) {
  if (opts.verbosity <= 0) { opts = Object.assign({}, opts, {verbosity: 1}); }
  let ret = "";
  for (const g of gs) {
    if (g instanceof End) {
      ret += colorFactorPrefix(g.p, g.e, opts);
    }
    if (g instanceof Group) {
      ret += colorMultiPrefix(g.d) + groupingToString(g.gs, opts) + "-a";
    }
  }
  return ret;
}

// Finds all possible groupings for a prime prefix using precomputed GCD values
// (see allGroupings for an example)
function allGroupings_withGCDs(xs, gcds) {
  let ret = [ xs.map(([p,e]) => e.n <= 2 && (p <= 19 || e.n == 1)
                                  ? new End(p,e)
                                  : new Group(e.n, [new End(p,e.div(e.n))])) ];
  if (xs.length == 1) {
    return ret;
  }
  const d = gcds[0][xs.length-1];
  let fn = (xs => xs);
  if (d > 1 && xs[0][1].n/d <= 2 && (xs[0][0] <= 19 || xs[0][1].n/d == 1)) {
    fn = (xs => [new Group(d, xs)]);
    xs = xs.map(([p,e]) => [p, e.div(d)]);
    gcds = gcds.map(ds => ds.map(x => x/d));
  }
  for (let i = 1; i < xs.length; i++) {
    const ls = allGroupings_withGCDs(xs.slice(0,i), gcds);
    const rs = allGroupings_withGCDs(xs.slice(i), gcds.slice(i));
    for (let j = 0; j < ls.length; j++) {
      for (let k = 0; k < rs.length; k++) {
        const new_gs = fn(ls[j].concat(rs[k]));
        if (ret.some(gs => eqPrefixes(gs, new_gs))) { continue; }
        ret.push(new_gs);
      }
    }
  }
  return ret;
}

// Precomputes the GCD values for allGroupings_withGCDs
function allAdjGCDs(xs) {
  let ret = xs.map(([p,e]) => [e.n]);
  for (let len = 1; len < xs.length; len++) {
    for (let i = 0; i < xs.length - len; i++) {
      const [a,b] = [ret[i], ret[i+1]];
      ret[i].push(gcd(a[a.length-1], b[b.length-1]));
    }
  }
  return ret;
}

// Finds all possible groupings for a prime prefix
// e.g. allGroupings(Interval([0,0,3,-6,2]).factors())
// [
//   [
//     End { p: 11, e: Fraction(2) },
//     Group { d: 6,
//             gs: [ End { p: 7, e: Fraction(-1) } ] },
//     Group { d: 3,
//             gs: [ End { p: 5, e: Fraction(1) } ] }
//   ],
//   [
//     End { p: 11, e: Fraction(2) },
//     Group { d: 3,
//             gs: [ End { p: 7, e: Fraction(-2) },
//                   End { p: 5, e: Fraction(1) } ] }
//   ],
//   [
//     Group { d: 2,
//             gs: [ End { p: 11, e: Fraction(1) },
//                   Group { d: 3,
//                           gs: [ End { p: 7, e: Fraction(-1) } ] } ] },
//     Group { d: 3,
//             gs: [ End { p: 5, e: Fraction(1) } ] }
//   ]
// ]
function allGroupings(factors) {
  const xs = factors.slice().reverse();
  const gcds = allAdjGCDs(xs);
  return allGroupings_withGCDs(xs, gcds);
}

// Counts the number of hyphens which will be in the resulting color prefix
function groupingHyphens(gs) {
  let hyphs = 0;
  for (let i = 0; i < gs.length; i++) {
    if (gs[i] instanceof Group) {
      hyphs += groupingHyphens(gs[i].gs);
      if (i < gs.length - 1) { hyphs++; }
    }
  }
  return hyphs;
}

// Checks all possible ways to group the factors of the color prefix, and
//  returns a string with the minimum number of hyphens, and among those
//  strings with the same number of hyphens, the maximum number of groupings.
//  If there are multiple strings which satisfy the above, strings which group
//  on the left are preferred.
function minColorPrefixStr(factors, opts) {
  const gss = allGroupings(factors);
  let [minHyphs, idxOfMin] = [Infinity, 0];
  for (let i = 0; i < gss.length; i++) {
    const hyphs = groupingHyphens(gss[i]);
    if (hyphs <= minHyphs) {
      [minHyphs, idxOfMin] = [hyphs, i];
    }
  }
  return groupingToString(gss[idxOfMin], opts);
}

/**
  * Returns the magnitude + color prefix of the given interval in color notation
  *
  * @param {Interval} i
  * @param {Object=} opts
  * @param {integer=} opts.verbosity verbosity can be the default 0
  *                                  (e.g. "17og"), 1 (e.g. "sogu"), or 2
  *                                  (the same as 1 for this function)
  * @param {boolean=} opts.addCosAfterDeg defaults to 13, if set to `Infinity`,
  *                                       a "co" prefix is never added
  * @param {boolean=} opts.hideMagnitude defaults to false
  * @param {boolean=} opts.useFullMagnitude defaults to false
  * @param {boolean=} opts.keepTrailingHyphen defaults to false
  * @param {boolean=} opts.useExps defaults to false
  * @param {boolean=} opts.useHTMLExps defaults to false
  * @returns {string}
  */
function colorPrefix(a,b, opts) {
  // if only two arguments are given, the second one may be `opts`!
  if (!opts && typeof b == 'object' && b != null) {
    opts = b;
    b = undefined;
  }
  let { verbosity, addCosAfterDeg, hideMagnitude,
        useFullMagnitude, keepTrailingHyphen, useExps, useHTMLExps} = opts || {};
  if (verbosity == undefined) { verbosity = 0; }
  if (addCosAfterDeg == undefined) { addCosAfterDeg = 13; }

  let i = Interval(a,b);
  if (!i.isFrac()) {
    throw new Error("Non-ratio has no color name");
  }

  // the cos string
  let [cos, coStr] = [0, ""];
  const [i_logval, d] = [i.valueOf_log(), colorDegree(i)];
  if (i_logval >= 1 && (d > addCosAfterDeg || d < -addCosAfterDeg)) {
    cos = Math.floor(i_logval);
    i = i.div(Interval(2).pow(cos));
  }
  if (verbosity == 0) {
    if (cos == 0) { coStr = "" }
    else if (cos == 1) { coStr = "c"; }
    else if (cos == 2) { coStr = "cc"; }
    else if (useHTMLExps) { coStr = "c<sup>" + cos + "</sup>"; }
    else if (useExps) {
      if ((''+cos).length == 1) { coStr = "c^" + cos; }
      else { coStr = "c^(" + cos + ")"; }
    }
    else { coStr = "c".repeat(cos); }
  }
  else {
    if (cos == 1) { coStr = "co"; }
    if (cos == 2) { coStr = "coco"; }
    if (cos >= 3) { coStr = colorMultiPrefix(cos) + "co"; }
  }

  let iNo23 = i.factorOut(2)[1].factorOut(3)[1];
  let factors = iNo23.factors();

  // the magnitude string
  let [mAbs, mStr] = [0, ""];
  const m = colorMagnitude(i);
  if (m != 0 && !hideMagnitude) {
    mAbs = Math.abs(m);
    if (verbosity == 0) {
      const c = m > 0 ? "L" : "s";
      if (mAbs == 0) { mStr = ""; }
      else if (mAbs == 1) { mStr = c; }
      else if (mAbs == 2) { mStr = c + c; }
      else if (useHTMLExps) { mStr = c + "<sup>" + mAbs + "</sup>"; }
      else if (useExps) {
        if ((''+mAbs).length == 1) { mStr = c + "^" + mAbs; }
        else { mStr = c + "^(" + mAbs + ")"; }
      }
      else { mStr = c.repeat(mAbs); }
    }
    else if (!useFullMagnitude) {
      mStr = m > 0 ? "la" : "sa";
      if (mAbs == 2) { mStr = mStr + mStr; }
      if (mAbs >= 3) { mStr = colorMultiPrefix(mAbs) + mStr; }
    }
    else {
      mStr = m > 0 ? "large " : "small ";
      if (mAbs > 1) { mStr = mAbs + "-" + mStr; }
    }
  }

  // the prefix string
  let pStr = "";
  // the wa case
  if (factors.length == 0) {
    pStr = colorFactorPrefix(3, 1, opts);
  }
  // if verbosity != 0, pull out groups of exponents
  else if (verbosity != 0) {
    pStr = minColorPrefixStr(factors, opts);
  }
  else {
    for (const [p,e] of factors) {
      pStr = colorFactorPrefix(p, e.valueOf(), opts) + pStr;
    }
  }
  // get rid of a trailing "-a"
  if (!keepTrailingHyphen) {
    pStr = pStr.replace(/-a$/, "");
  }

  let [hy1, hy2] = ["", ""];
  if (verbosity != 0) {
    let coNoHyphen = cos <= 1; // when coStr is empty or a single syllable
    let mNoHyphen = mAbs <= 1; // when mStr is empty or a single syllable
    let pNoHyphen = factors.length == 0 ||
                    (factors.length == 1 && Math.abs(factors[0][1]) == 1);
                    // ^ when pStr is a single syllable
    // we add a hyphen between sections in all but the cases in which we would
    //  have a single syllable on either the left or right side
    if (mAbs == 0) {
      if (!(coNoHyphen || pNoHyphen)) { hy2 = "-"; }
    }
    else {
      if (!(coNoHyphen || mNoHyphen)) { hy1 = "-"; }
      if (!( mNoHyphen || pNoHyphen)) { hy2 = "-"; }
    }
  }

  // put the final string together
  let res = coStr + hy1 + mStr + hy2 + pStr;

  if (res == "lo") { return "ilo"; }
  if (res == "so") { return "iso"; }
  if (res == "no") { return "ino"; }
  if (res == "nu") { return "inu"; }
  return res;
}

/**
  * Returns the symbol of given interval in color notation
  *
  * @param {Interval} i
  * @param {Object=} opts
  * @param {integer=} opts.verbosity verbosity can be the default 0
  *                                  (e.g. "17og3"), 1 (e.g. "sogu 3rd"), or
  *                                  2 (e.g. "sogu third")
  * @param {boolean=} opts.addCosAfterDeg defaults to 13, if set to `Infinity`,
  *                                       a "co" prefix is never added
  * @param {boolean=} opts.useFullMagnitude defaults to false
  * @param {boolean=} opts.useWordNegative defaults to false
  * @param {boolean=} opts.useExps defaults to false
  * @param {boolean=} opts.useHTMLExps defaults to false
  * @returns {string}
  */
function colorSymb(a,b, opts) {
  // if only two arguments are given, the second one may be `opts`!
  if (!opts && typeof b == 'object' && b != null) {
    opts = b;
    b = undefined;
  }
  let {verbosity, addCosAfterDeg, useFullMagnitude, useWordNegative, useExps, useHTMLExps} = opts || {};
  if (verbosity == undefined) { verbosity = 0; }
  if (addCosAfterDeg == undefined) { addCosAfterDeg = 13; }
  const optsToPass = { verbosity: verbosity
                     , addCosAfterDeg: addCosAfterDeg
                     , useFullMagnitude: useFullMagnitude
                     , useExps: useExps
                     , useHTMLExps: useHTMLExps };

  const i = Interval(a,b);
  const i_logval = i.valueOf_log();
  if (i.compare(1) < 0) {
    return (verbosity == 0 ? "desc. " : "descending ")
           + colorSymb(i.recip(), opts);
  }

  let d = colorDegree(i);
  if (i_logval >= 1 && (d > addCosAfterDeg || d < -addCosAfterDeg)) {
    const cos = Math.floor(i_logval);
    d = colorDegree(i.div(Interval(2).pow(cos)));
  }

  const spacer_str = verbosity > 0 ? " " : "";
  const d_str = pyDegreeString(d, {verbosity: verbosity, useWordNegative: useWordNegative});
  return colorPrefix(i, optsToPass) + spacer_str + d_str;
}

/**
  * Given a number of "co"s, a magnitude, an interval made up of only primes
  * > 3, and a degree, returns the corresponding interval in color notation
  *
  * @param {integer} m the number of "co"s
  * @param {integer} m the magnitude
  * @param {Interval} iNo23 cannot contain factors of 2 or 3
  * @param {integer} d the degree
  * @param {boolean} [logCorrections] defaults to false
  * @returns {Interval}
  */
function colorFromSymb(cos, m, iNo23, d, logCorrections) {
  iNo23 = Interval(iNo23);
  if (iNo23.hasExp(2) || iNo23.hasExp(3)) {
    throw new Error("Second argument to colorFromSymb has a factor of 2 or 3")
  }
  const zd = d - Math.sign(d); // AKA: S, or "stepspan" (here zd stands for "zeroed degree")
  const zdNo23 = colorZDegree(iNo23); // AKA: X
  const zd_diff = zd - zdNo23;
  const mNo2 = colorMagnitude(iNo23.mul(Interval(3).pow(2*zd_diff))); // AKA: Y

  // By the definition of degree we have:
  // (1) zd = 7*e2 + 11*e3 + zdNo23
  //  => zd_diff = 7*e2 + 11*e3

  // All solutions to the linear diophantine equation above have the form:
  //  e2 = -3*zd_diff - 11*k,
  //  e3 =  2*zd_diff +  7*k  for some k
  // (Source: https://en.wikipedia.org/wiki/Diophantine_equation#One_equation)

  // By the definition of magnitude we have:
  // (2) m = round((e3 + e5 + e7 + ...) / 7)
  //  => m = round((2*zd_diff + 7*k + e5 + e7 + ...) / 7)
  //  => m = round((2*zd_diff + e5 + e7 + ...) / 7) + k
  //  => m = mNo2 + k
  //  => k = m - mNo2

  const k = m - mNo2;
  const e2 = -3*zd_diff - 11*k;
  const e3 = 2*zd_diff + 7*k;

  if (logCorrections) {
    // The above is sometimes different from what's given on:
    // https://en.xen.wiki/w/Color_notation
    const e3_xenWiki = mod(2*zd - 2*zdNo23 + 3, 7) + 7*m - 3;
    const e2_xenWiki = (zd - zdNo23 - 11*e3_xenWiki) / 7;
    if (e2 != e2_xenWiki || e3 != e3_xenWiki) {
      const ab1 = "a=" + e2_xenWiki + ",b=" + e3_xenWiki;
      const ab2 = "a=" + e2 + ",b=" + e3;
      console.log("Corrected ratio-from-color formula: " + ab1 + " ~> " + ab2);
    }
  }

  return iNo23.mul(Interval([cos+e2,e3]));
}

/**
  * Returns the note name of the given interval in color notation. The returned
  * string uses ASCII instead of uniode wherever possible iff the `useASCII`
  * field of `opts` is given and is true
  *
  * @param {Interval} intvToA4
  * @param {Object=} opts
  * @param {integer=} opts.verbosity verbosity can be the default 0
  *                                  (e.g. "17ogC5"), 1 (e.g. "sogu C5"), or 2
  *                                  (the same as 1 for this function)
  * @param {boolean=} opts.ignoreOctave defaults to false
  * @param {boolean=} opts.useASCII defaults to false
  * @param {boolean=} opts.useExps defaults to false
  * @param {boolean=} opts.useHTMLExps defaults to false
  * @returns {string}
  */
function colorNote(a,b, opts) {
  // if only two arguments are given, the second one may be `opts`!
  if (!opts && typeof b == 'object' && b != null) {
    opts = b;
    b = undefined;
  }
  let {verbosity, useASCII, useExps, useHTMLExps} = opts || {};
  if (verbosity == undefined) { verbosity = 0; }
  const optsToPass = { verbosity: verbosity
                     , addCosAfterDeg: Infinity
                     , hideMagnitude: true
                     , useExps: useExps
                     , useHTMLExps: useHTMLExps };

  const i = Interval(a,b);
  let [e2,iNo2] = i.factorOut(2);
  let [e3,iNo23] = iNo2.factorOut(3);
  if (iNo23.equals(1)) {
    return pyNote(i, opts);
  }
  for (const [p,e] of iNo23.factors()) {
    const j = colorFromSymb(0, 0, Interval(p), 1).pow(e);
    e2 = e2.sub(j.expOf(2));
    e3 = e3.sub(j.expOf(3));
  }
  const pyi = Interval([e2,e3]);
  return colorPrefix(iNo23, optsToPass)
         + (verbosity > 0 ? " " : "")
         + pyNote(pyi, opts);
}

/**
  * Given an interval made up of only primes > 3 and a pythagorean interval to
  * A4, returns the corresponding interval to A4 in color notation
  *
  * @param {Interval} iNo23 cannot contain factors of 2 or 3
  * @param {Interval} pyi the base Pythagorean note
  * @returns {Interval}
  */
function colorFromNote(iNo23, pyi) {
  let [e2,e3] = [pyi.expOf(2), pyi.expOf(3)];
  for (const [p,e] of iNo23.factors()) {
    const j = colorFromSymb(0, 0, Interval(p), 1).pow(e);
    e2 = e2.add(j.expOf(2));
    e3 = e3.add(j.expOf(3));
  }
  return Interval([e2,e3]).mul(iNo23);
}

/**
  * Return the temperament name associated with the given comma, based on:
  * https://en.xen.wiki/w/Color_notation/Temperament_Names
  *
  * @param {Interval} i
  * @returns {string}
  */
function colorTemperament(a,b) {
  const i = Interval(a,b);
  if (i.compare(1) < 0) {
    throw new Error("Comma passed to `colorTempermentName` must be > 1");
  }

  const iRed = i.red();
  const [m, zd] = [colorMagnitude(iRed), colorZDegree(iRed)]
  const iNo23 = i.factorOut(2)[1].factorOut(3)[1];
  let segOffset = 1;
  let last_diff = iRed.distance();
  let curr_diff = colorFromSymb(0, m, iNo23, (zd-1)+sign1(zd-1)).red().distance();
  while (curr_diff.compare(last_diff) < 0) {
    segOffset++;
    last_diff = curr_diff;
    curr_diff = colorFromSymb(0, m, iNo23, (zd-segOffset)+sign1(zd-segOffset)).red().distance();
  }
  const segOffsetStr = colorMultiPrefix(segOffset);

  const colorStr = colorPrefix(i, { verbosity: 1
                                  , addCosAfterDeg: 0 // i.e. always
                                  , useFullMagnitude: false });
  return colorStr + segOffsetStr;
}

module['exports'].colorPrimeZDegree = colorPrimeZDegree;
module['exports'].colorZDegree = colorZDegree;
module['exports'].colorDegree = colorDegree;
module['exports'].colorMagnitude = colorMagnitude;
module['exports'].colorPrimePrefix = colorPrimePrefix;
module['exports'].colorMultiPrefix = colorMultiPrefix;
module['exports'].colorFactorPrefix = colorFactorPrefix;
module['exports'].colorPrefix = colorPrefix;
module['exports'].colorSymb = colorSymb;
module['exports'].colorFromSymb = colorFromSymb;
module['exports'].colorNote = colorNote;
module['exports'].colorFromNote = colorFromNote;
module['exports'].colorTemperament = colorTemperament;

},{"./interval.js":7,"./pythagorean.js":11,"./utils.js":13,"fraction.js":16,"mathutils":17,"primes-and-factors":20}],3:[function(require,module,exports){
/**
 * Functions for working with intervals in an EDO
 * @copyright 2021 Matthew Yacavone (matthew [at] yacavone [dot] net)
 * @module edo
 **/

const {mod} = require('./utils.js');
const {gcd, egcd} = require('mathutils');
const pf = require('primes-and-factors');
const Fraction = require('fraction.js');
const Interval = require('./interval.js');
const py = require('./pythagorean.js');

/**
  * Returns the EDO step closest to the given interval
  *
  * @param {integer} edo
  * @param {Interval} i
  * @returns {integer}
  */
function edoApprox(edo,a,b) {
  return Math.round(edo * Interval(a,b).valueOf_log());
}


let edoPrimeApprox_var = {};

/**
  * Returns the EDO step closest to the given prime interval, and its error
  *
  * @param {integer} edo
  * @param {integer} p
  * @returns {Pair.<integer,Interval>}
  */
function edoPrimeApprox(edo, p) {
  if (edoPrimeApprox_var[[edo,p]]) {
    return edoPrimeApprox_var[[edo,p]];
  }
  if (!pf.isPrime(p)) {
    throw new Error("Input to edoPrimeApprox is not a prime");
  }

  const n = edoApprox(edo, p);
  const diff = Interval(2).pow(n,edo).div(p);

  if (!edoPrimeApprox_var[edo]) { edoPrimeApprox_var[edo] = {}; }
  edoPrimeApprox_var[edo][p] = [n,diff];
  return [n,diff];
}

/**
  * Returns the EDO step which corresponds to the given interval using the EDO's
  * prime mappings (`edoPrimeApprox`) as well as the log values of the total
  * prime error and max prime error
  *
  * @param {integer} edo
  * @param {Interval} i
  * @returns {{n: integer, err: number, max_prime_err: number}}
  */
function edoApproxConsistentWithErr(edo,a,b) {
  const i = Interval(a,b);
  let ret = { n: 0, err: 0, max_prime_err: 0 };
  for (const [p,e] of i.factors()) {
    const [p_n, p_err] = edoPrimeApprox(edo, p);
    ret.n += e.s * e.n * p_n;
    const prime_err = e.n * Math.abs(p_err.valueOf_log());
    ret.err += prime_err;
    ret.max_prime_err = Math.max(prime_err, ret.max_prime_err);
  }
  return ret;
}

/**
  * Returns the EDO step which corresponds to the given interval using the EDO's
  * prime mappings (`edoPrimeApprox`)
  *
  * @param {integer} edo
  * @param {Interval} i
  * @returns {integer}
  */
function edoApproxConsistent(edo,a,b) {
  return edoApproxConsistentWithErr(edo,a,b).n;
}

/**
  * Returns true iff the given intervals is inconsistent in the given EDO, i.e.
  * if `edoApprox` and `edoApproxConsistent` give different values
  *
  * @param {integer} edo
  * @param {Interval} i
  * @returns {integer}
  */
function edoIntvIsConsistent(edo,a,b) {
  const i = Interval(a,b);
  return edoApprox(edo,i) == edoApproxConsistent(edo,i);
}

/**
  * Returns the EDO step which corresponds to the given pythagorean interval,
  * where a P5 corresponds to `edoApprox(edo,Interval(3,2))`
  *
  * @param {integer} edo
  * @param {Interval} i
  * @returns {integer}
  */
function edoPy(edo,a,b) {
  const i = Interval(a,b);
  const g = Fraction(py.pyGenerator(i) * edoApprox(edo,3,2), 4);
  const p = py.pyOctaves(i);
  if (g.d != 1) {
    throw new Error(edo + "-EDO has no " + py.pySymb(i,{verbosity:1}) + " interval");
  }
  return g.s*g.n + p * edo;
}

/**
  * Returns the pythagorean interval with the smallest generator which
  * corresponds to the given EDO step, i.e. for which `edoPy` returns the given
  * EDO step. Note that there may be no such interval, in which case this
  * function returns `undefined`.
  *
  * All other intervals for which `edoPy` returns the given EDO step are
  * the result of this function times some power of `edoPyComma`.
  *
  * In summary, for every pythagorean interval i there exists some integer k
  * such that `edoPyInv(edo, edoPy(edo, i)) == i.mul(edoPyComma(edo).pow(k))`,
  * and for all integers n and k, either `edoPyInv(edo, n)` is undefined or
  * `edoPy(edo, edoPyInv(edo, n).mul(edoPyComma(edo).pow(k))) == n`.
  *
  * @param {integer} edo
  * @param {integer} n
  * @returns {Interval}
  */
function edoPyInv(edo,n) {
  const p5 = edoApprox(edo,3,2);
  // d == x * p5 + 4 * y * edo
  const [d, x, y] = egcd(p5, 4 * edo);
  if ((4 * n) % d == 0) {
    // n == (g / 4) * p5 + o * edo
    const [g, o] = [x * (4*n/d), y * (4*n/d)];
    // n == (g_bal / 4) * p5 + o_bal * edo && -(edo/d)/2 < g_bal/4 <= (edo/d)/2
    const edo_2d = Math.floor((4*edo/d - 1) / 2);
    const g_bal = mod(g + edo_2d, 4*edo/d) - edo_2d;
    const o_bal = o - p5 * ((g_bal - g) / (4 * edo));
    return Interval(3,2).pow(g_bal,4).mul(Interval(2).pow(o_bal));
  }
}

/**
  * The smallest pythagorean interval tempered out in the given edo (I believe
  * this is the correct description...)
  *
  * @param {integer} edo
  * @returns {Interval}
  */
function edoPyComma(edo) {
  const p5 = edoApprox(edo,3,2);
  const d = gcd(p5, 4 * edo);
  return Interval(3,2).pow(-4 * edo / d, 4).mul(Interval(2).pow(p5 / d));
}

/**
  * Checks whether neutral pythagorean intervals are realized in the given EDO,
  * i.e. if `edoApprox(edo,Interval(3,2))` is divisible by 2
  *
  * @param {integer} edo
  * @returns {boolean}
  */
function edoHasNeutrals(edo) {
  return edoApprox(edo,3,2) % 2 == 0;
}

/**
  * Checks whether semi-neutral pythagorean intervals are realized in the given
  * EDO, i.e. if `edoApprox(edo,Interval(3,2))` is divisible by 4
  *
  * @param {integer} edo
  * @returns {boolean}
  */
function edoHasSemiNeutrals(edo) {
  return edoApprox(edo,3,2) % 4 == 0;
}

// used in `updnsSymb` and `updnsNote`
function fillGens(edo, g, lo, hi) {
  let steps = [];
  for (let i = 0; i < edo; i++) { steps.push(Array(0)); }
  if (lo <= 0 && 0 <= hi) {
    steps[0].push([0,0]);
  }
  for (let k = 1; k <= Math.max(Math.abs(lo), Math.abs(hi)); k++) {
    if (lo <=  k &&  k <= hi) { steps[mod( k*g,edo)].push([0, k]); }
    if (lo <= -k && -k <= hi) { steps[mod(-k*g,edo)].push([0,-k]); }
  }
  return steps;
}

// The input to this function is an array of only the basic intervals,
//  usually only those with no ups or downs, but in the case of odd-EDOs,
//  up-mid and down-mid intervals as well. This function fills in the rest of
//  the steps with intervals with ups and downs added appropriately
// (Used in `updnsSymb` and `updnsNote`)
function addUpdns(edo, steps) {
  let new_steps = steps.map((_,i) => [...steps[i]]);
  let [last_below, last_above] = [0,edo];
  for (let i = 0; i < edo; i++) {
    // if the current step is empty or an up-mid or down-mid interval, add
    //  everything from last_below (with the appropriate number of ups)
    if (steps[i].length == 0 || (steps[i].length == 1 && steps[i][0][0] != 0)) {
      for (const [n,k] of steps[last_below]) {
        const diff = i - last_below;
        // only add if n is zero or the sign of n and diff match, this prevents
        //  up-mid and down-mid intervals from turning into mid intervals
        if (n * diff >= 0) {
          new_steps[i].push([n + diff, k]);
        }
      }
    }
    if (steps[i].length != 0) {
      last_below = i;
    }
    const j = (edo-1)-i;
    // if the current step is empty or an up-mid or down-mid interval, add
    //  everything from last_above (with the appropriate number of downs)
    if (steps[j].length == 0 || (steps[j].length == 1 && steps[j][0][0] != 0)) {
      for (const [n,k] of steps[mod(last_above,edo)]) {
        const diff = j - last_above;
        // only add if n is zero or the sign of n and diff match, this prevents
        //  up-mid and down-mid intervals from turning into mid intervals
        if (n * diff >= 0) {
          new_steps[j].push([n + diff, k]);
        }
      }
    }
    if (steps[j].length != 0) {
      last_above = j;
    }
  }
  for (let i = 0; i < edo; i++) {
    let [minUpdns, minUpdnsIsNeutral] = [edo, false];
    for (const [uds, k] of new_steps[i]) {
      const abs_uds = Math.abs(uds);
      if (abs_uds < minUpdns) {
        minUpdns = abs_uds;
        minUpdnsIsNeutral = !Number.isInteger(k);
      }
      if (abs_uds == minUpdns) {
        minUpdnsIsNeutral &= !Number.isInteger(k);
      }
    }
    new_steps[i] = new_steps[i].filter(udsk => Math.abs(udsk[0]) <= minUpdns
                                               && (minUpdnsIsNeutral || Number.isInteger(udsk[1])))
                               .sort((a,b) => a[0] == b[0] ? Math.abs(a[1]) - Math.abs(b[1])
                                                           : b[0] - a[0]);
  }
  return new_steps;
}

// used in `updnsSymb` and `updnsNote`
function cvtGensToPy(edo, steps) {
  for (let i = 0; i < edo; i++) {
    for (let j = 0; j < steps[i].length; j++) {
      let v = Interval(steps[i][j][1] == 0 && steps[i][j][0] < 0 ? 2 : 1);
      steps[i][j][1] = Interval(3,2).pow(steps[i][j][1]).red().mul(v);
    }
  }
  return steps;
}

let upsdnsSymbCache_var = {};

function updnsSymbCache(edo) {
  if (upsdnsSymbCache_var[edo]) {
    return upsdnsSymbCache_var[edo];
  }
  if (edo <= 0) { return [] }
  // We treat 1, 2, 3, 4, 6, and 8-EDO as subsets of 24-EDO
  if ([1,2,3,4,6,8].includes(edo)) {
    const [cache, factor] = [updnsSymbCache(24), 24/edo];
    const steps = [...Array(edo).keys()].map(i => cache[i*factor]);
    upsdnsSymbCache_var[edo] = steps;
    return steps;
  }
  let fifth = edoApprox(edo,3,2);
  // We use the second-best fifth for 13-EDO and 18-EDO
  if (edo == 13 || edo == 18) { fifth--; }
  let [lo, hi] = [-6, 6]; // d5 m2 m6 m3 m7 P4 | P1 | P5 M2 M6 M3 M7 A4
  // Special case for perfect EDOs
  if (fifth/edo == 4/7) {
    [lo, hi] = [-1.5, 1.5]; // (~2) P4 (~6) | P1 | (~3) P5 (~7)
  }
  // Special case for pentatonic EDOs
  if (fifth/edo == 3/5) {
    [lo, hi] = [-4, 4]; // m6 m3 m7 P4 | P1 | P5 M2 M6 M3
  }
  let steps;
  if (fifth % 2 != 0) {
    steps = fillGens(edo, fifth, lo, hi);
    for (const k of [1/2, -1/2, 3/2, -3/2, 5/2, -5/2]) {
      const i = mod(Math.floor(k*fifth), edo);
      if (steps[i].length == 0) { steps[i].push([-1,k]); }
      const j = mod(Math.ceil(k*fifth), edo);
      if (steps[j].length == 0) { steps[j].push([1,k]); }
    }
  } else {
    steps = fillGens(edo, fifth/2, 2*lo, 2*hi);
    for (let i = 0; i < edo; i++) {
      steps[i] = steps[i].filter(([n,k]) => k % 2 == 0 || Math.abs(k) <= 6)
                         .map(([n,k]) => [n,k/2]);
    }
  }
  steps = cvtGensToPy(edo, addUpdns(edo, steps));
  upsdnsSymbCache_var[edo] = steps;
  return steps;
}

function fmtUpdnsSymb(uds, pyi, opts) {
  let {verbosity, maxTupleWord, usePerfEDONotation, useExps, useHTMLExps} = opts || {};
  if (verbosity == undefined) { verbosity = 0; }
  if (maxTupleWord == undefined) { maxTupleWord = 3; }
  const uds_abs = Math.abs(uds);
  let [uds_str, py_str] = ["", py.pySymb(pyi, {verbosity: verbosity})];
  if (verbosity == 0) {
    if (!useExps || uds_abs < 4) {
      uds_str = (uds > 0 ? '^' : 'v').repeat(uds_abs);
    }
    else if (useHTMLExps) {
      uds_str = (uds > 0 ? '^' : 'v') + "<sup>" + uds_abs + "</sup>";
    }
    else if (uds_abs < 10) {
      uds_str = (uds > 0 ? '(^)^' : '(v)^') + uds_abs;
    }
    else {
      uds_str = (uds > 0 ? '(^)^(' : '(v)^(') + uds_abs + ')';      
    }
    if (usePerfEDONotation) { py_str = py_str.replace("n", "P"); }
    if (uds_abs > 0) { py_str = py_str.replace("P", ""); }
    py_str = py_str.replace("n", "~").replace("sA", "~").replace("sd", "~");
  }
  else {
    const uds_suffix = uds > 0 ? "up" : "down";
    if (uds_abs == 0) {
      uds_str = "";
    }
    else if (uds_abs == 1) {
      uds_str = uds_suffix;
    }
    else if (uds_abs <= Math.min(maxTupleWord, 12)) {
      uds_str = ["double", "triple", "quadruple", "quintuple", "sextuple",
                 "septuple", "octuple", "nonuple", "decuple", "undecuple",
                 "duodecuple"][uds_abs-2] + "-" + uds_suffix + " ";
    }
    else {
      uds_str = uds_abs + "-" + uds_suffix + " ";
    }
    if (usePerfEDONotation) { py_str = py_str.replace("neutral", "perfect"); }
    if (uds_abs == 1) { py_str = py_str.replace("perfect ", " "); }
    if (uds_abs >= 2) { py_str = py_str.replace("perfect ", ""); }
    py_str = py_str.replace("neutral", "mid");
    if (verbosity == 1) {
      py_str = py_str.replace("semi-aug", "mid")
                     .replace("semi-dim", "mid");
    }
    else {
      py_str = py_str.replace("semi-augmented", "mid")
                     .replace("semi-diminished", "mid");
    }
  }
  return uds_str + py_str;
}

/**
  * Returns the ups-and-downs notation symbol for the given steps in the given
  * EDO
  *
  * @param {integer} edo
  * @param {integer} n
  * @param {Object=} opts
  * @param {integer=} opts.verbosity verbosity can be the default 0
  *                                  (e.g. "^^M3"), 1 (e.g. "3-up major 3rd"),
  *                                  or 2 (e.g. "triple-up major third")
  * @param {integer=} opts.maxTupleWord default is 2, maximum is 12
  * @param {boolean=} opts.useWordNegative defaults to false
  * @param {boolean=} opts.useWordDesc defaults to false
  * @param {boolean=} opts.useNeutNotationForPerfEDOs defaults to false
  * @param {boolean=} opts.useExps defaults to false
  * @param {boolean=} opts.useHTMLExps defaults to false
  * @returns {string}
  */
function updnsSymb(edo,n, opts) {
  let {verbosity, maxTupleWord, useWordDesc, useNeutNotationForPerfEDOs} = opts || {};
  if (verbosity == undefined) { verbosity = 0; }
  if (maxTupleWord == undefined) { maxTupleWord = 2; }
  const usePerfEDONotation = edo % 7 == 0 && !useNeutNotationForPerfEDOs;

  if (useWordDesc && n < 0) {
    pre_str = verbosity == 0 ? "desc. " : "descending ";
    return updnsSymb(edo, -n, opts).map(s => pre_str + s);
  }

  const nr = mod(n,edo);
  const vs = Interval(2).pow(n - nr, edo);
  const cache = updnsSymbCache(edo)[nr];
  const optsToPass = Object.assign({}, opts, {usePerfEDONotation: usePerfEDONotation});
  return cache.map(([uds, pyi_red]) => fmtUpdnsSymb(uds, pyi_red.mul(vs), optsToPass));
}

/**
  * Given the number of ups-and-downs and a Pythagorean interval, returns the
  * corresponding number of steps in ups-and-downs notation
  *
  * @param {integer} edo
  * @param {integer} uds
  * @param {Interval} pyi
  * @returns {integer}
  */
function updnsFromSymb(edo, uds, pyi) {
  // We treat 1, 2, 3, 4, 6, and 8-EDO as subsets of 24-EDO
  if ([1,2,3,4,6,8].includes(edo)) {
    const [n, factor] = [updnsFromSymb(24, uds, pyi), 24/edo];
    if (n % factor != 0) {
      throw new Error(edo + "-EDO has no " + fmtUpdnsSymb(uds, pyi) + " interval");
    }
    return n / factor;
  }
  let fifth = edoApprox(edo,3,2);
  // We use the second-best fifth for 13-EDO and 18-EDO
  if (edo == 13 || edo == 18) { fifth--; }
  const g = Fraction(py.pyGenerator(pyi) * fifth, 4);
  const p = py.pyOctaves(pyi);
  if (g.d == 2 && fifth % 2 != 0) {
    if (uds == 0) {
      throw new Error(edo + "-EDO has no " + fmtUpdnsSymb(uds, pyi) +
                      " interval (but it does have " + fmtUpdnsSymb(1, pyi) +
                      " and " + fmtUpdnsSymb(-1,pyi) + " intervals)");
    }
    return (uds-Math.sign(uds)) +
           (uds < 0 ? Math.floor(g.valueOf()) : Math.ceil(g.valueOf())) +
           p * edo;
  }
  if (g.d != 1) {
    throw new Error(edo + "-EDO has no " + fmtUpdnsSymb(uds, pyi) + " interval");
  }
  return uds + g.s*g.n + p * edo;
}

let upsdnsNoteCache_var = {};

function updnsNoteCache(edo) {
  if (upsdnsNoteCache_var[edo]) {
    return upsdnsNoteCache_var[edo];
  }
  if (edo <= 0) { return [] }
  // We treat 1, 2, 3, 4, 6, and 8-EDO as subsets of 24-EDO
  if ([1,2,3,4,6,8].includes(edo)) {
    const [cache, factor] = [updnsNoteCache(24), 24/edo];
    const steps = [...Array(edo).keys()].map(i => cache[i*factor]);
    upsdnsSymbCache_var[edo] = steps;
    return steps;
  }
  let fifth = edoApprox(edo,3,2);
  // We use the second-best fifth for 13-EDO and 18-EDO
  if (edo == 13 || edo == 18) { fifth--; }
  let [lo, hi] = [-9, 7]; // Gb Db Ab Eb Bb F C G D | A | E B F# C# G# D# A#
  // Special case for perfect EDOs
  if (fifth/edo == 4/7) {
    [lo, hi] = [-4, 2]; // F C G D | A | E B
  }
  // Special case for EDOs between perfect and 12-EDO
  if (fifth/edo > 4/7 && fifth/edo < 7/12) {
    [lo, hi] = [-11, 9]; // Fb Cb Gb ... | A | ... A# E# B#
  }
  const steps = cvtGensToPy(edo, addUpdns(edo, fillGens(edo, fifth, lo, hi)));
  upsdnsNoteCache_var[edo] = steps;
  return steps;
}

/**
  * Returns the ups-and-downs notation note name for the given steps to A4 (or
  * a reference, if given `opts.refIntvToA4`) in the given EDO. The returned
  * string uses ASCII instead of uniode wherever possible iff the third argument
  * is given and is true
  *
  * @param {integer} edo
  * @param {integer} n
  * @param {Object} [opts]
  * @param {Interval} [opts.refIntvToA4] defaults to 1
  * @param {boolean} [opts.ignoreOctave] defaults to false
  * @param {boolean} [opts.useASCII] defaults to false
  * @param {boolean} [opts.useExps] defaults to false
  * @param {boolean} [opts.useHTMLExps] defaults to false
  * @returns {string}
  */
function updnsNote(edo, n, opts) {
  let {refIntvToA4, useExps, useHTMLExps} = opts || {};
  if (refIntvToA4 == undefined) { refIntvToA4 = Interval(1); }
  const nr = mod(n,edo);
  const vs = Interval(2).pow(n - nr, edo);
  const cache = updnsNoteCache(edo)[nr];
  let ret = [];
  for (const [uds, pyi_red] of cache) {
    const uds_abs = Math.abs(uds);
    let updns;
    if (!useExps || uds_abs < 4) {
      updns = (uds > 0 ? '^' : 'v').repeat(uds_abs);
    }
    else if (useHTMLExps) {
      updns = (uds > 0 ? '^' : 'v') + "<sup>" + uds_abs + "</sup>";
    }
    else if (uds_abs < 10) {
      updns = (uds > 0 ? '(^)^' : '(v)^') + uds_abs;
    }
    else {
      updns = (uds > 0 ? '(^)^(' : '(v)^(') + uds_abs + ')';
    }
    const str = updns + py.pyNote(pyi_red.mul(vs).mul(refIntvToA4), opts);
    ret.push(str);
  }
  return ret;
}

module['exports'].edoApprox = edoApprox;
module['exports'].edoPrimeApprox = edoPrimeApprox;
module['exports'].edoApproxConsistentWithErr = edoApproxConsistentWithErr;
module['exports'].edoApproxConsistent = edoApproxConsistent;
module['exports'].edoIntvIsConsistent = edoIntvIsConsistent;
module['exports'].edoPy = edoPy;
module['exports'].edoPyInv = edoPyInv;
module['exports'].edoPyComma = edoPyComma;
module['exports'].edoHasNeutrals = edoHasNeutrals;
module['exports'].edoHasSemiNeutrals = edoHasSemiNeutrals;
module['exports'].updnsSymbCache = updnsSymbCache;
module['exports'].fmtUpdnsSymb = fmtUpdnsSymb;
module['exports'].updnsSymb = updnsSymb;
module['exports'].updnsFromSymb = updnsFromSymb;
module['exports'].updnsNoteCache = updnsNoteCache;
module['exports'].updnsNote = updnsNote;

},{"./interval.js":7,"./pythagorean.js":11,"./utils.js":13,"fraction.js":16,"mathutils":17,"primes-and-factors":20}],4:[function(require,module,exports){
/**
 * English names for intervals based on the Neutral FJS and ups-and-downs
 * notations (very much incomplete!)
 * @copyright 2021 Matthew Yacavone (matthew [at] yacavone [dot] net)
 * @module english
 **/

const pf = require('primes-and-factors');
const ntw = require('number-to-words');
const Fraction = require('fraction.js');
const Interval = require('./interval.js');
const {pyInterval, pySymb, pyGenerator} = require('./pythagorean.js');
const {fjsComma, fjsFifthShift, fjsAccidentals, nfjsSpec} = require('./fjs.js');
const {updnsSymbCache} = require('./edo.js');

const primeNames = { '5':  ["classic", "cls."]
                   , '7':  ["septimal", "sep."]
                   , '11': ["undecimal", "und."]
                   , '13': ["tridecimal", "trid."]
                   , '17': ["septendecimal", "sepd."]
                   , '19': ["undevicesimal", "undv."] };

/**
  * Attempts to give english names to the given interval based on the
  * Neutral FJS and ups-and-downs notations.
  *
  * @param {Interval} i
  * @param {{abbreviate: boolean, prefEDO: integer}=} opts
  * @returns {Array.<string>}
  */
function enNames(a,b, opts) {
  // if only two arguments are given, the second one may be `opts`!
  if (!opts && typeof b == 'object' && b != null) {
      opts = b;
      b = undefined;
  }
  const intv = Interval(a,b);
  const abbreviate = (opts || {}).abbreviate ? 1 : 0;
  const verbosity  = abbreviate ? 1 : 2;
  const prefEDO    = (opts || {}).prefEDO;
  const pySymbOpts = {verbosity: verbosity, useWordDesc: 1, useDescSuffix: 1};

  let nms = [];

  // handle approximate intervals separately
  if (!intv.hasFactors()) {
    const k = Math.floor(intv.valueOf_log());
    if (intv.div(Interval(2).pow(k)).equals(Interval.phi)) {
      const pyi = pyInterval(6,0).mul(Interval(2).pow(k));
      nms.push("phi " + pySymb(pyi, pySymbOpts));
    }
    return nms;
  }

  // special case for the Pythagorean comma
  if (intv.equals(pyInterval(-2,-1.5))) {
    nms.push("Pythagorean comma");
  }
  // special cases for FJS formal commas
  for (const p in primeNames) {
    const comma = fjsComma(p);
    const inv_str = intv.compare(1) < 0 ? " (descending)" : "";
    if (intv.equals(comma) || intv.equals(comma.recip())) {
      nms.push((p == 5 ? "syntonic" : primeNames[p][0]) + " comma" + inv_str);
    }
  }
  // special case for multiple octaves
  if (intv.inPrimeLimit(2) && intv.expOf(2).d == 1 && intv.expOf(2).n > 1
      /* ^ is a non-zero integer power of 2 */) {
    const invStr = intv.expOf(2) < 0 ? " (descending)" : "";
    nms.push(ntw.toWords(intv.expOf(2).n) + " octaves" + invStr);
  }

  // Neutral FJS intervals
  const fjs = fjsAccidentals(a,b, nfjsSpec);
  if (fjs) {
    let pyi_symb = pySymb(fjs.pyi, pySymbOpts);
    const resFact = intv.factors().filter(([p,_]) => p > 3);
    // FJS intervals with no accidentials and a factor of 3 are Pythagorean
    if (resFact.length == 0) {
      if (intv.hasExp(3)) {
        nms.push((abbreviate ? "py. " : "Pythagorean ") + pyi_symb);
      }
      else {
        nms.push(pyi_symb);
      }
    }
    // FJS intervals with a single prime (>3) factor might be able to be named
    else if (resFact.length == 1) {
      const [p,e] = resFact[0];
      // We don't consider cases where the prime doesn't have the name, the FJS
      //  accidental is not an integer, or the pythagorean interval is an
      //  octave
      if (primeNames[p] && e.d == 1 && pyGenerator(fjs.pyi) != 0) {
        const fifthShift = fjsFifthShift(p, nfjsSpec);
        const g = fjs.pyi.expOf(3);
        // Ensure otonality matches (e.g. let through "M3^5" but not "M3_5")
        //  and neutral-ness matches (e.g. let through "M3^5" but not "n3^5")
        if (e.s == fifthShift.s * g.s && g.d == fifthShift.d) {
          // Ensure multiplicity matches, i.e. n-aug/dim have (n+1) primes
          //  (e.g. let through M3^5 and A4^5,5 but not M3^5,5 or A4^5)
          let multiplicityMatches = false;
          // Well, for primes with non-neutral fifth shifts, we do exactly
          //  what's stated above...
          if (fifthShift.d == 1) {
            if (g.n == 6) {
              multiplicityMatches = (e.n == 2);
            }
            else {
              multiplicityMatches = (e.n == 2 + Math.floor((g.n - 6)/7))
            }
          }
          // ...but for primes with neutral fifth shifts, we just handle cases
          //  where the neutral interval is small, since it's not clear to me
          //  what to do in the general case
          if (fifthShift.d == 2) {
            multiplicityMatches = (g.n <= 11 && e.n == 1);
          }
          if (multiplicityMatches) {
            // make sure we don't have "perfect" in the name for a 4th or 5th
            if (Math.abs(pyGenerator(fjs.pyi)) == 4) {
              let typ = intv.compare(fjs.pyi) > 0 ? "super" : "sub";
              if (abbreviate) { pyi_symb = pyi_symb.replace("perfect", typ); }
              else {
                typ = p == 5 ? (typ == "super" ? "acute " : "grave ") : typ + "-";
                pyi_symb = pyi_symb.replace("perfect ", typ);
              }
            }
            nms.push(primeNames[p][abbreviate] + " " + pyi_symb.replace("perfect ", ""));
          }
        }
      }
    }
  }

  // ups-and-downs intervals
  else if (intv.inPrimeLimit(2)) {
    const e2 = intv.expOf(2);
    const edo = prefEDO ? prefEDO : e2.d;
    const edo_str = edo + "-EDO ";
    let intv_strs = [];
    if (e2.mul(edo).d == 1 && (prefEDO || edo <= 60)) {
      const n = e2.s * e2.mul(edo).n;
      const n_mod = ((n % edo) + edo) % edo;
      for (const [uds, pyi_red] of updnsSymbCache(edo)[n_mod]) {
        const pyi = pyi_red.mul(Interval(2).pow((n-n_mod)/edo));
        if (uds == 0) {
          intv_strs.push(pySymb(pyi, pySymbOpts));
        }
      }
      if (intv_strs.length > 0) {
        nms.push(edo_str + intv_strs.join(" / "));        
      }
      if (n == edo / 2) {
        nms.push(edo_str + "tritone");
      }
    }
  }

  // special case for the inverse of the Pythagorean comma
  if (intv.equals(pyInterval(2,-1.5))) {
    nms.push("Pythagorean comma (descending)");
  }
  // special case for harmonics > 1
  if (intv.isFrac()) {
    const {n,d} = intv.toFrac();
    if (d == 1 && n > 1) {
      nms.push(ntw.toOrdinal(n) + " harmonic");
    }
    if (n == 1 && d > 1) {
      nms.push(ntw.toOrdinal(d) + " harmonic (descending)");
    }
  }

  return nms;
}

module.exports.enNames = enNames;

},{"./edo.js":3,"./fjs.js":5,"./interval.js":7,"./pythagorean.js":11,"fraction.js":16,"number-to-words":19,"primes-and-factors":20}],5:[function(require,module,exports){
/**
 * Functions for working with FJS intervals
 * @copyright 2021 Matthew Yacavone (matthew [at] yacavone [dot] net)
 * @module fjs
 **/

const pf = require('primes-and-factors');
const Fraction = require('fraction.js');
const Interval = require('./interval.js');
const py = require('./pythagorean.js');

/**
  * A specficiation of an FJS-like system.
  *
  * @constructor
  * @param {Interval} RoT the radius of tolerance
  * @param {GeneratorFunction.<Fraction>} fifthSeq the fifth sequence
  * @param {boolean} [hasNeutrals=false] whether this FJS permits neutral Pythagorean intervals
  * @param {boolean} [hasSemiNeutrals=false] whether this FJS permits semi-neutral Pythagorean intervals
  */
function FJSLike(RoT, fifthSeq, hasNeutrals, hasSemiNeutrals) {

  if (!(this instanceof FJSLike)) {
    return new FJSLike(RoT, fifthSeq, hasNeutrals, hasSemiNeutrals);
  }

  this.RoT = RoT;
  this.fifthSeq = fifthSeq;
  this.hasNeutrals = !!hasNeutrals;
  this.hasSemiNeutrals = !!hasSemiNeutrals;

}

/**
  * The radius of tolerance of the FJS, the interval `65/63` (about `54.11c`)
  *
  * @constant {Interval}
  */
const fjsRoT = Interval(65,63);

/**
  * The (infinite) fifth sequence of the FJS, `0, 1, -1, 2, -2, 3, -3, ...`
  *
  * @yields {Fraction}
  */
function* fjsFifthSeq() {
  yield Fraction(0);
  for (let g = 1; true; g++) {
    yield Fraction(g);
    yield Fraction(-g);
  }
}

/**
  * The specificaion of the standard FJS, using `fjsRoT`, `fjsFifthSeq`,
  * `hasNeutrals = false`, and `hasSemiNeutrals = false`
  *
  * @constant {FJSLike}
  */
const fjsSpec = FJSLike(fjsRoT, fjsFifthSeq, false, false);

/**
  * The radius of tolerance of the Neutral FJS, a pythagorean
  * semi-diminished second ("sd2", the interval exactly halfway between a
  * pythagorean "d2" and "m2", or about `33.38c`)
  *
  * @constant {Interval}
  */
const nfjsRoT = py.pyInterval(2,-1); // "sd2" ~= 33.38c

/**
  * The (finite) fifth sequence of the Neutral FJS,
  * `0, 1, -1, 2, -2, ..., 6, -6, 1/2, -1/2, 3/2, -3/2, ..., 11/2, -11/2`
  *
  * @yields {Fraction}
  */
function* nfjsFifthSeq() {
  yield Fraction(0);
  for (let g = 1; g <= 6; g++) {
    yield Fraction(g);
    yield Fraction(-g);
  }
  for (let g = 1; g <= 6; g++) {
    yield Fraction(2*g-1, 2);
    yield Fraction(1-2*g, 2);
  }
}

/**
  * The specification of the Neutral FJS, using `nfjsRoT`, `nfjsFifthSeq`,
  * `hasNeutrals = true`, and `hasSemiNeutrals = false`
  *
  * @constant {FJSLike}
  */
const nfjsSpec = FJSLike(nfjsRoT, nfjsFifthSeq, true, false);

/**
  * Divides the octave intro regions based on what fifth shift each interval
  * is assigned.
  *
  * @param {FJSLike} [spec=fjsSpec]
  * @returns {Array.<{lo:Interval, hi:Interval, fifthShift:Fraction, index:integer}>}
  */
function fjsRegions(spec) {
  if (!spec) {
    spec = fjsSpec;
  }
  else if (spec.RoT.compare(Interval(2).sqrt()) >= 0) {
    throw new Error("RoT too big");
  }
  else if (spec.RoT.compare(Interval(1)) <= 0) {
    throw new Error("RoT < 1");
  }

  let index = 0;
  let regions = [{lo: Interval(1), hi: Interval(2), fifthShift: undefined}];
  function addRegion(lo, hi, fifthShift) {
    if (lo.compare(Interval(1)) < 0) {
      addRegion(Interval(1), hi, fifthShift);
      addRegion(lo.mul(2), Interval(2), fifthShift);
    }
    else if (hi.compare(Interval(2)) > 0) {
      addRegion(Interval(1), hi.div(2), fifthShift);
      addRegion(lo, Interval(2), fifthShift);
    }
    else {
      for (const [i,r] of regions.entries()) {
        // for the first undefined region we intersect:
        if (!r.fifthShift && lo.compare(r.hi) < 0 && r.lo.compare(hi) < 0) {
          const lo_vs_rlo = lo.compare(r.lo);
          const hi_vs_rhi = hi.compare(r.hi);
          const maxlo = lo_vs_rlo > 0 ? lo : r.lo;
          const minhi = hi_vs_rhi < 0 ? hi : r.hi;
          // delete the current undefined region
          regions.splice(i, 1);
          // add the upper remainder of the undefined region, if it exists
          if (hi_vs_rhi < 0) {
            regions.splice(i, 0, {lo: minhi, hi: r.hi, fifthShift: undefined });
          }
          // add the new intersection region
          regions.splice(i, 0, {lo: maxlo, hi: minhi, fifthShift: fifthShift, index: index });
          index++;
          // add the lower remainder of the undefined region, if it exists
          if (lo_vs_rlo > 0) {
            regions.splice(i, 0, {lo: r.lo, hi: maxlo, fifthShift: undefined });
          }
          // add the upper remainder of the region we're adding, if it exists
          if (hi_vs_rhi > 0) {
            addRegion(r.hi, hi, fifthShift);
          }
          return;
        }
      }
    }
  }

  for (const g of spec.fifthSeq()) {
    const f = Interval(3,2).pow(g).red();
    addRegion(f.div(spec.RoT), f.mul(spec.RoT), g);
    // if every part of interval space it accounted for, we're done
    if (regions.every(r => r.fifthShift != undefined)) { break; }
  }
  return regions;
}

/**
  * Returns the FJS fifth shift associated to any interval.
  *
  * @param {Interval} i
  * @param {FJSLike} [spec=fjsSpec]
  * @returns {Fraction}
  */
function fjsFifthShift(a,b, spec) {
  // if only two arguments are given, the second one may be `spec`!
  if (!spec) {
    if (typeof b == 'object' && b != null) {
      spec = b;
      b = undefined;
    } else {
      spec = fjsSpec;
    }
  }
  const intv = Interval(a,b);
  for (const g of spec.fifthSeq()) {
    let c = intv.div(Interval(3,2).pow(g)).reb();
    if (c.compare(spec.RoT) < 0 && spec.RoT.recip().compare(c) < 0) {
      return g;
    }
  }
}

/**
  * Returns the FJS comma associated to a prime interval greater than 3
  * (i.e. 5, 7, 11, etc.)
  *
  * @param {integer} p
  * @param {FJSLike} [spec=fjsSpec]
  * @returns {Interval}
  */
function fjsComma(p, spec) {
  if (!spec) { spec = fjsSpec; }
  p = parseInt(p);
  if (!pf.isPrime(p) || p <= 3) {
    throw new Error ("input is not a prime interval greater than 3");
  }
  for (const g of spec.fifthSeq()) {
    let c = Interval(p).div(Interval(3,2).pow(g)).reb();
    if (c.compare(spec.RoT) < 0 && spec.RoT.recip().compare(c) < 0) {
      return c;
    }
  }
}

/**
  * Given an interval, returns the product of the FJS commas associated to each
  * of its prime factors raised to the exponents of those prime factors
  *
  * @param {Interval} k
  * @param {FJSLike} [spec=fjsSpec]
  * @returns {Interval}
  */
function fjsFactor(a,b, spec) {
  // if only two arguments are given, the second one may be `spec`!
  if (!spec) {
    if (typeof b == 'object' && b != null) {
      spec = b;
      b = undefined;
    } else {
      spec = fjsSpec;
    }
  }
  const k = Interval(a,b);
  let ret = Interval(1);
  for (const [p,e] of k.factors()) {
    ret = ret.mul(fjsComma(p,spec).pow(e));
  }
  return ret;
}

/**
  * Returns the string of FJS accidentals for the given interval, as well as
  * the pythagorean interval which when applied to these accidentals
  * results in the given interval.
  *
  * @param {Interval} i
  * @param {FJSLike} [spec=fjsSpec]
  * @returns {{ accStr: string, pyi: Interval }}
  */
function fjsAccidentals(a,b, spec) {
  // if only two arguments are given, the second one may be `spec`!
  if (!spec) {
    if (typeof b == 'object' && b != null) {
      spec = b;
      b = undefined;
    } else {
      spec = fjsSpec;
    }
  }
  const i = Interval(a,b);
  let pyi = i;
  let otos = [];
  let utos = [];
  for (let [p,e] of i.factors()) {
    if (p != 2 && p != 3) {
      pyi = pyi.div(fjsComma(p,spec).pow(e));
      // add otonal accidentals
      while (e >= 1) {
        otos.push(p);
        e = e.sub(1);
      }
      if (e > 0 && e.d == 2) {
        otos.push("sqrt(" + p + ")");
      }
      if (e > 0 && e.d > 2) {
        otos.push("root" + e.d + "(" + p + ")");
      }
      // add utonal accidentals
      while (e <= -1) {
        utos.push(p);
        e = e.add(1);
      }
      if (e < 0 && e.d == 2) {
        utos.push("sqrt(" + p + ")");
      }
      if (e < 0 && e.d > 2) {
        utos.push("root" + e.d + "(" + p + ")");
      }
    }
  }
  const modulus = spec.hasSemiNeutrals ? 1 : spec.hasNeutrals ? 2 : 4;
  if (py.isPythagorean(pyi) && py.pyGenerator(pyi) % modulus == 0) {
    const otoStr = otos.length == 0 ? "" : "^" + otos.join(",");
    const utoStr = utos.length == 0 ? "" : "_" + utos.join(",");
    return { otos: otos, utos: utos, accStr: otoStr + utoStr, pyi: pyi };
  }
}

/**
  * Returns the FJS symbol of the given interval, or undefined if no such symbol
  * exists
  *
  * @param {Interval} i
  * @param {FJSLike} [spec=fjsSpec]
  * @returns {string}
  */
function fjsSymb(a,b, spec) {
  const res = fjsAccidentals(a,b, spec);
  if (res) {
    return py.pySymb(res.pyi) + res.accStr;
  }
}

/**
  * Returns the FJS note name of the given interval to A4, or undefined if no
  * such name exists
  *
  * @param {Interval} i
  * @param {FJSLike} [spec=fjsSpec]
  * @returns {string}
  */
function fjsNote(a,b, spec) {
  const res = fjsAccidentals(a,b, spec);
  if (res) {
    return py.pyNote(res.pyi) + res.accStr;
  }
}

module['exports'].FJSLike = FJSLike;
module['exports'].fjsRoT = fjsRoT;
module['exports'].fjsFifthSeq = fjsFifthSeq;
module['exports'].fjsSpec = fjsSpec;
module['exports'].nfjsRoT = nfjsRoT;
module['exports'].nfjsFifthSeq = nfjsFifthSeq;
module['exports'].nfjsSpec = nfjsSpec;
module['exports'].fjsRegions = fjsRegions;
module['exports'].fjsFifthShift = fjsFifthShift;
module['exports'].fjsComma = fjsComma;
module['exports'].fjsFactor = fjsFactor;
module['exports'].fjsAccidentals = fjsAccidentals;
module['exports'].fjsSymb = fjsSymb;
module['exports'].fjsNote = fjsNote;

},{"./interval.js":7,"./pythagorean.js":11,"fraction.js":16,"primes-and-factors":20}],6:[function(require,module,exports){
// export everything from `lib/` as well as `Fraction` from fraction.js
Object.assign(module['exports'], require('./utils.js'));
module['exports']['Fraction'] = require('fraction.js');
module['exports']['Interval'] = require('./interval.js');
Object.assign(module['exports'], require('./pythagorean.js'));
Object.assign(module['exports'], require('./fjs.js'));
Object.assign(module['exports'], require('./edo.js'));
Object.assign(module['exports'], require('./color.js'));
Object.assign(module['exports'], require('./sets.js'));
Object.assign(module['exports'], require('./approx.js'));
Object.assign(module['exports'], require('./english.js'));
Object.assign(module['exports'], require('./parser/eval.js'));
Object.assign(module['exports'], require('./parser.js'));

},{"./approx.js":1,"./color.js":2,"./edo.js":3,"./english.js":4,"./fjs.js":5,"./interval.js":7,"./parser.js":8,"./parser/eval.js":9,"./pythagorean.js":11,"./sets.js":12,"./utils.js":13,"fraction.js":16}],7:[function(require,module,exports){
/**
 * The interval datatype, based on `Fraction` from `fraction.js` on npm
 * @copyright 2021 Matthew Yacavone (matthew [at] yacavone [dot] net)
 * @module interval
 **/

const {unBigFraction, cachedLog2, maxKey, keys, primes} = require('./utils.js');
const pf = require('primes-and-factors');
const bigInt = require('big-integer');
const Fraction = require('fraction.js');
const BigFraction = require('fraction.js/bigfraction.js');

// helper functions used when constructing `Interval`s in this file

function parse(a,b) {
  // no arguments given
  if (a == undefined) {
    return { _fact: {} };
  }
  // two arguments given
  else if (b != undefined) {
    const [n,d] = [Number(a), Number(b)];
    if (n % 1 != 0 || !isFinite(n) || d % 1 != 0 || !isFinite(d)) {
      throw new Error(`Invalid integer parameters to Interval: ${a}, ${b}`);
    }
    return parseRatio(n,d);
  }
  // a single array argument given
  else if (Array.isArray(a)) {
    return parseMonzo(a);
  }
  // a single BigInt argument given
  else if (typeof a == "bigint") {
    return parseRatio(Number(a), 1);
  }
  else if (typeof a == "object") {
    // a single Fraction/BigFraction-like argument given
    if ("d" in a && "n" in a) {
      const n = Number("s" in a ? a["s"] * a["n"] : a["n"]);
      const d = Number(a["d"]);
      if (n % 1 != 0 || !isFinite(n) || d % 1 != 0 || !isFinite(d)) {
        throw new Error(`Invalid Fraction-like parameter to Interval: ${a}`);
      }
      return parseRatio(n,d);
    }
    // a single Interval-like argument given
    else if ("_fact" in a) {
      return parseFactorization(a._fact, a._isApprox, a._isApprox);
    }
    // otherwise we assume a single object argument is a factorization object
    else {
      return parseFactorization(a, true);
    }
  }
  // a single number argument given
  else if (isFinite(Number(a))) {
    if (!(Number(a) > 0)) {
      throw new Error(`${a} <= 0 cannot be represented as an Interval`);
    }
    return parseNumber(Number(a));
  }
  // a single string argument given (which is not a valid Number string)
  else if (typeof a == "string") {
    const fr = BigFraction(a);
    const [n, d] = [Number(fr.s * fr.n), Number(fr.d)];
    if (n % 1 != 0 || !isFinite(n) || d % 1 != 0 || !isFinite(d)) {
      throw new Error(`Invalid string parameter to Interval: ${a}`);
    }
    return parseRatio(n, d);
  }
  // otherwise we error
  else {
    throw new Error(`Invalid parameter to Interval: ${a}`)
  }
}

function parseRatio(n,d) {
  if (!(n > 0) || !(d > 0)) {
    throw new Error(`${n}/${d} <= 0 cannot be represented as an Interval`);
  }
  const n_fact = pf.getPrimeExponentObject(n);
  const d_fact = pf.getPrimeExponentObject(d);
  let fact = {};
  for (const p of keys(n_fact, d_fact)) {
    fact[p] = BigFraction((n_fact[p] || 0) - (d_fact[p] || 0));
  }
  return { _fact: fact };
}

function parseMonzo(a) {
  let fact = {};
  let ps = primes();
  for (const ai of a) {
    const e = BigFraction(ai);
    const p = ps.next().value;
    if (!e.equals(0)) {
      fact[p] = e;
    }
  }
  return { _fact: fact };
}

function parseFactorization(obj, allowApproxs, knownIsApprox) {
  let [fact, isApprox] = [{}, false];
  for (const i of Object.keys(obj)) {
    const e = BigFraction(obj[i]);
    if (!e.equals(0)) {
      if (pf.isPrime(Number(i))) {
        fact[i] = e;
      }
      else if (allowApproxs && (knownIsApprox || parseNumber(i)._isApprox)) {
        fact[i] = e;
        isApprox = true;
      }
      else {
        throw new Error(`non-prime in factorization parameter to Interval: ${i}`);
      }
    }
  }
  if (isApprox) { return { _isApprox: true, _fact: fact }; }
  else          { return { _fact: fact }; }
}

function parseNumber(x) {
  if (x % 1 == 0) {
    return parseRatio(x, 1);
  }
  try {
    // covers nth roots between 1 and 5
    for (let [xpk, k] = [x, 1]; k <= 5; [xpk, k] = [xpk*x, k+1]) {
      let fact = numberToSmallFact(xpk);
      if (fact) {
        for (const p in fact) {
          fact[p] = fact[p].div(k);
        }
        return { _fact: fact };
      }
    }
    // covers fractional powers of 2, 3, and 5
    for (const base of [2,3,5]) {
      const e = BigFraction(Math.log2(x) / cachedLog2(base));
      if (e.d < 200) {
        return { _fact: { [base]: e } };
      }
    }
  }
  catch (e) {
  }
  // otherwise we return an approximation
  if (x >= 1) {
    return { _isApprox: true, _fact: {[x]: BigFraction(1)} };
  }
  else {
    return { _isApprox: true, _fact: {[1/x]: BigFraction(-1)} };
  }
}

function numberToSmallFact(x) {
  const fr = Fraction(x);
  if (isFinite(fr.n) && isFinite(fr.d)) {
    const fact = parseRatio(fr.n, fr.d)._fact;
    let squared_sum_of_prime_digits = 0;
    for (const p in fact) {
      squared_sum_of_prime_digits += p.toString().length ** 2;
    }
    if (squared_sum_of_prime_digits <= 9) {
      return fact;
    }
  }
}

/**
  * Constructs an `Interval`. Valid argument combinations are two integers
  * (e.g. `Interval(3,2)`), a single number (e.g. `Interval(3/2)`), a
  * factorization (e.g. `Interval({2: -1, 3: 1})`), an array of numbers or
  * `Fraction`s representing a monzo (e.g. `Interval([-1,1])`), a `Fraction`,
  * or an `Interval`.
  *
  * As a convention, all functions which have a JSDoc parameter of type
  * `Interval` should be able to accept any of these argument combinations in
  * place of that parameter. For example, `mul` in this file, or
  * `bestRationalApproxsByHeight` in `approx.js`.
  *
  * If both arguments are omitted, the result is `Interval(1)`.
  *
  * @constructor
  * @param {(number|Fraction|Object)=} a
  * @param {integer=} b
  */
function Interval(a,b) {

  if (!(this instanceof Interval)) {
    return new Interval(a,b);
  }

  const p = parse(a,b);
  if (p._isApprox) { this._isApprox = p._isApprox; }
  this._fact = p._fact;
}

Interval.prototype = {

  /**
   * Returns true iff the interval has a known prime factorization.
   *
   * @returns {boolean}
   */
  "hasFactors": function() {
    return !this._isApprox;
  },

  /**
   * Returns true iff the exponent of the given prime in an interval's prime
   * factorization is nonzero.
   *
   * e.g. `Interval(24).hasExp(2)` is `true`, `Interval(8).hasExp(5)` is `false`
   *
   * @param {integer} p a prime number
   * @returns {boolean}
   */
  "hasExp": function(p) {
    if (this._isApprox) {
      throw new Error("interval does not have a prime factorization");
    }
    if (!pf.isPrime(Number(p))) {
      throw new Error(p + " is not prime");
    }
    return !!this._fact[p];
  },

  /**
   * Returns the exponent of the given prime in an interval's prime
   * factorization.
   *
   * e.g. `Interval(24).expOf(2)` is `3`, `Interval(8).expOf(5)` is `0`
   *
   * @param {integer} p a prime number
   * @returns {Fraction}
   */
  "expOf": function(p) {
    return unBigFraction(this.expOfBig(p));
  },

  /**
   * Like `expOf`, but returns a BigFraction.
   *
   * @param {integer} p a prime number
   * @returns {BigFraction}
   */
  "expOfBig": function(p) {
    return this.hasExp(p) ? this._fact[p] : BigFraction(0);
  },

  /**
   * Returns the prime factorization of an interval as a list of pairs
   * `[[p1,e1], [p2,e2], ..., [pn,en]]` where each pn is prime such that
   * the interval is equal to `p1^e1 * p2^e2 * ... * pn^en`.
   *
   * @returns {Array.<Pair.<integer,BigFraction>>}
   */
  "factors": function() {
    if (this._isApprox) {
      throw new Error("interval does not have a prime factorization");
    }
    let fs = [];
    for (const p in this._fact) {
      if (!this._fact[p].equals(0n)) {
        fs.push([parseInt(p), unBigFraction(this._fact[p])]);
      }
    }
    return fs;
  },

  /**
   * Like `factors`, but returns an array of BigFraction.
   *
   * @returns {Array.<Pair.<integer,BigFraction>>}
   */
  "factorsBig": function() {
    if (this._isApprox) {
      throw new Error("interval does not have a prime factorization");
    }
    let fs = [];
    for (const p in this._fact) {
      if (!this._fact[p].equals(0n)) {
        fs.push([parseInt(p), this._fact[p]]);
      }
    }
    return fs;
  },

  /**
   * Multiplies (i.e. composes) two intervals.
   *
   * e.g. `Interval(3,2).mul(5,4)` is the composition of `3/2` and `5/4`, the
   * interval `15/8`, or `Interval(15,8)`
   *
   * @param {Interval} i
   * @returns {Interval}
   */
  "mul": function(a,b) {
    const rhs = parse(a,b);
    let ret_fact = {};
    for (const p of keys(this._fact, rhs._fact)) {
      ret_fact[p] = (this._fact[p] || BigFraction(0)).add(rhs._fact[p] || BigFraction(0));
    }
    return new Interval({ _fact: ret_fact, _isApprox: this._isApprox || rhs._isApprox });
  },

  /**
   * Divides two intervals.
   *
   * e.g. `Interval(2).div(3,2)` is exactly `Interval(4,3)`
   *
   * @param {Interval} i
   * @returns {Interval}
   */
  "div": function(a,b) {
    const rhs = parse(a,b);
    let ret_fact = {};
    for (const p of keys(this._fact, rhs._fact)) {
      ret_fact[p] = (this._fact[p] || BigFraction(0)).sub(rhs._fact[p] || BigFraction(0));
    }
    return new Interval({ _fact: ret_fact, _isApprox: this._isApprox || rhs._isApprox });
  },

  /**
   * Takes the reciprocal/inverse of an interval.
   *
   * e.g. `Interval(3,2).recip()` is exactly `Interval(2,3)`
   *
   * @returns {Interval}
   */
  "recip": function() {
    let ret_fact = {};
    for (const p in this._fact) {
      ret_fact[p] = this._fact[p].neg();
    }
    return new Interval({ _fact: ret_fact, _isApprox: this._isApprox });
  },

  /**
   * Raises an interval to a fractional power.
   *
   * e.g. `Interval(4,3).pow(2)` is the composition of `4/3` with itself, the
   * interval `16/9`
   *
   * e.g. `Interval(2).pow(4,12)` is the interval `4\12`, four steps of 12-EDO
   *
   * e.g. `Interval(5).pow(1,4)` is the fourth root of `5`, the fifth in
   * quarter-comma meantone
   *
   * @param {Fraction} k
   * @returns {Interval}
   */
  "pow": function(a,b) {
    const k = BigFraction(a,b);
    let ret_fact = {};
    for (const p in this._fact) {
      ret_fact[p] = this._fact[p].mul(k);
    }
    return new Interval({ _fact: ret_fact, _isApprox: this._isApprox });
  },

  /**
   * The nth root of an interval, i.e. `pow(1,n)`.
   *
   * @param {integer} n
   * @returns {Interval}
   */
  "root": function(a) {
    return this.pow(1,a);
  },

  /**
   * The square root of an interval, i.e. `pow(1,2)`. or `root(2)`
   *
   * @returns {Interval}
   */
  "sqrt": function() {
    return this.root(2);
  },

  /**
   * Checks whether an interval has integer prime exponents, i.e. whether the
   * interval can be expressed as a fraction
   *
   * e.g. `Interval(3,2).isFrac()` returns `true`
   *
   * e.g. `Interval(2).sqrt().isFrac()` returns `false`
   *
   * @returns {bool}
   */
  "isFrac": function() {
    if (this._isApprox) {
      return false;
    }
    for (const p in this._fact) {
      if (this._fact[p].d != 1n) {
        return false;
      }
    }
    return true;
  },

  /**
   * Converts an interval with integer prime exponents, i.e. an interval which
   * can be expressed as a fraction, to a `Fraction`.
   *
   * e.g. `Interval(3,2).toFrac()` is exactly `Fraction(3,2)`
   *
   * e.g. `Interval(2).sqrt().toFrac()` throws an error
   *
   * @returns {Fraction}
   */
  "toFrac": function() {
    return unBigFraction(this.toFracBig());
  },

  /**
   * Like `toFrac`, but returns a `BigFraction`
   *
   * @returns {BigFraction}
   */
  "toFracBig": function() {
    return BigFraction(this.toFracRaw());
  },

  /**
   * Like `toFrac`, but returns an unreduced `BigFraction`
   *
   * @param {bool} allowUnbounded if true, supresses errors related to the
   *                              exponents being too big
   * @returns {{s: BigInt, n:BigInt, d:BigInt}}
   */
  "toFracRaw": function(allowUnbounded) {
    if (this._isApprox) {
      throw new Error("interval does not have a prime factorization");
    }
    let [n, d] = [1n, 1n];
    for (const p in this._fact) {
      if (this._fact[p].d == 1) {
        let m = this._fact[p].s * this._fact[p].n;
        if ((m >= 4096 || m <= -4096) && !allowUnbounded) {
          throw new Error("exponent of " + p + " too big: " + m)
        }
        if (m > 0) {
          n *= BigInt(p) ** m;
        }
        if (m < 0) {
          d *= BigInt(p) ** (-1n * m);
        }
      } else {
        throw new Error("interval does not have integer exponents");
      }
    }
    return {s: 1n, n: n, d: d};
  },

  /**
   * Takes the mediant of two intervals with integer prime exponents, i.e. two
   * intervals which can be expressed as fractions.
   *
   * e.g. `Interval(5,4).med(9,7)` is the mediant of the intervals `5/4` and
   * `9/7`, the interval `14/11`
   *
   * @param {Interval} i
   * @returns {Interval}
   */
  "med": function(a,b) {
    let [f1, f2] = [this.toFracRaw(), Interval(a,b).toFracRaw()];
    return new Interval(f1.n + f2.n, f1.d + f2.d);
  },

  /**
   * Converts any interval to its representation as the nth root of a fraction.
   *
   * e.g. `Interval(3,2).toNthRoot()` is exactly `{k: Interval(3,2).toFrac(), n: 1}`
   *
   * e.g. `Interval({2: 1/2, 5: 1/3})` is exactly `{k: Interval({2: 3, 5: 2}).toFrac(), n: 6}`
   *
   * @returns {{k: Fraction, n: Integer}}
   */
  "toNthRoot": function() {
    const {k, n} = this.toNthRootBig();
    return { k: unBigFraction(k), n: Number(n) };
  },

  /**
   * Like `toNthRoot`, but returns a `BigFraction`.
   *
   * @returns {{k: BigFraction, n: Integer}}
   */
  "toNthRootBig": function() {
    const {k, n} = this.toNthRootRaw();
    return { k: BigFraction(k), n: n };
  },

  /**
   * Like `toNthRoot`, but returns an unreduced `BigFraction`.
   *
   * @returns {{k: {s: BigInt, n:BigInt, d:BigInt}, n: Integer}}
   */
  "toNthRootRaw": function() {
    const n = this.minPowFracBig();
    return { k: this.pow(n).toFracRaw(), n: n };
  },

  /**
   * Returns the smallest integer such that `this.pow(n).isFrac()` is true, i.e.
   * the `n` in `this.toNthRoot()`.
   *
   * @returns {Integer}
   */
  "minPowFrac": function() {
    return Number(this.minPowFracBig());
  },

  /**
   * Like `minPowFrac`, but returns a `BigInt`.
   *
   * @returns {BigInt}
   */
  "minPowFracBig": function() {
    if (this._isApprox) {
      throw new Error("interval does not have a prime factorization");
    }
    let ret = 1n;
    for (const p in this._fact) {
      ret = BigInt(bigInt.lcm(ret, this._fact[p].d));
    }
    return ret;
  },

  /**
   * Converts any interval to a string of its representation as the nth root of
   * a fraction.
   *
   * e.g. `Interval(3,2).toNthRoot()` gives `"3/2"`
   *
   * e.g. `Interval({2: 1/2, 5: 1/3})` gives `"root6(200)"`
   *
   * @returns {{k: Fraction, n: Integer}}
   */
  "toNthRootString": function() {
    if (this._isApprox) {
      throw new Error("interval does not have a prime factorization");
    }
    const {k,n} = this.toNthRootBig();
    if (n == 1) { return k.toFraction(); }
    if (n == 2) { return "sqrt(" + k.toFraction() + ")"; }
    return "root" + n + "(" + k.toFraction() + ")";
  },

  /**
   * Converts an interval to its decimal value, for automatic use by javascript.
   * Note that this function should not be used to compare relative sizes of
   * intervals, use `valueOf_log` or `toCents` instead.
   *
   * e.g. `Interval(3,2).valueOf()` is exactly `1.5`
   *
   * @returns {number}
   */
  "valueOf": function() {
    let ret = 1;
    for (const p in this._fact) {
      ret *= p ** this._fact[p].valueOf();
    }
    return ret;
  },

  /**
   * Performs an exact comparison of two intervals. Specifically, returns 0 if
   * the intervals are equal, 1 if the first interval is greater than the
   * second, and -1 if the second interval is greater than the first.
   *
   * In general, `i1 ineq i2`, where `i1`, `i2` are intervals and `ineq` is an
   * inequality (e.g. `>=`), can be incorrect since javascript uses `valueOf`
   * to convert both sides to finite precision floating point numbers before
   * doing the comparision. To perform an exact version of the same check,
   * use `i1.compare(i2) ineq 0`.
   *
   * e.g. `Interval(2).sqrt().compare(3,2) < 0` is true since `sqrt(2) < 3/2`
   *
   * @param {Interval} i
   * @returns {integer}
   */
  "compare": function(a,b) {
    const rhs = Interval(a,b);
    try {
      // this uses the facts that:
      // - x < y iff x/y < 1
      // - k^(1/n) < 1 iff k < 1
      // - n/d < 1 iff n - d < 0
      const {n, d} = this.div(rhs).toNthRootRaw().k;
      const t = n - d;
      return (0 < t) - (t < 0);
    }
    catch(e) {
      // if something goes wrong, just do an approximate comparison
      const [x, y] =
        this._isApprox || rhs._isApprox ? [this.valueOf(), rhs.valueOf()]
                                        : [this.valueOf_log(), rhs.valueOf_log()];
      if (x == y) { return 0; }
      else { return (y < x) - (x < y); }
    }
  },

  /**
   * Checks if the two intervals are the same. In general, `i1 == i2`, where
   * `i1`, `i2` are intervals, can give false positives since javascript uses
   * `valueOf` to convert both sides to finite precision floating point numbers
   * before doing the comparision.
   *
   * e.g. `Interval(4,3).pow(2).equals(16,9)` is true
   *
   * @param {Interval} i
   * @returns {boolean}
   */
  "equals": function(a,b) {
    const rhs = Interval(a,b);
    if (this._isApprox || rhs._isApprox) {
      const epsilon = this._isApprox && rhs._isApprox ? 1e-10 : 1e-13;
      const [this_val, rhs_val] = [this.valueOf(), rhs.valueOf()];
      return Math.abs(this_val - rhs_val) / Math.max(this_val, rhs_val) < epsilon;
    }
    for (const p of keys(this._fact, rhs._fact)) {
      if (!(this._fact[p] || BigFraction(0)).equals(rhs._fact[p] || BigFraction(0))) {
        return false;
      }
    }
    return true;
  },

  /**
   * If the given argument is a prime, returns a pair whose first element is the
   * exponent of that prime in this interval, and whose second element is the
   * interval without that prime (i.e. the rest of the factorization).
   *
   * e.g. `Interval(8*5,7).factorOut(2)` is exactly `[3, Interval(5,7)]`.
   *
   * More generally, if the given argument is an interval `i` with factorization
   * `p1^e1 ... pm^em` (where the `pk`s are prime and in ascending order, and
   * each `ek > 0`), returns a pair `[g, this.div(i.pow(g))]` where `g` is the
   * smallest fraction such that `this.div(i.pow(g))` contains no factors of
   * `pm` (the largest prime in the factorization of `i`).
   *
   * e.g. `Interval(9,8).factorOut(3,2)` is exactly `[2, Interval(1,2)]`.
   *
   * @param {Interval} i
   * @returns {Pair.<Fraction,Interval>}
   */
  "factorOut": function(a,b) {
    const base = new Interval(a,b);
    const gp = maxKey(base._fact);
    if (isFinite(gp)) {
      const g = (this._fact[gp] || BigFraction(0)).div(base._fact[gp]);
      let ret_fact = {};
      for (const p of keys(this._fact, base._fact)) {
        ret_fact[p] = (this._fact[p] || BigFraction(0)).sub((base._fact[p] || BigFraction(0)).mul(g));
      }
      return [unBigFraction(g), new Interval({ _fact: ret_fact, _isApprox: this._isApprox || base._isApprox })];
    }
    else {
      return [Fraction(0), this];
    }
  },

  /**
   * Converts an interval to its decimal value log the given base. If no
   * argument is given, the base is taken to be 2 (an octave).
   *
   * e.g. `Interval(3,2).valueOf_log()` gives `0.5849625007211561`
   *
   * Note that this function uses `factorOut` to preserve as much precision as
   * possible - for example, for any interval `i` != 1 and fraction `k`, then
   * `i.pow(k).valueOf_log(i) == k.valueOf()` *exactly*.
   *
   * e.g. `Interval(3,2).pow(1,2).valueOf_log(3,2)` gives `0.5`
   *
   * @param {Interval} [i=Interval(2)]
   * @returns {number}
   */
  "valueOf_log": function(a,b) {
    const i = new Interval(a,b);
    // If no base is given, default to 2. We also have a specical case for 2:
    if ((a == undefined && b == undefined) || i.equals(2)) {
      let ret = 0;
      for (const p in this._fact) {
        ret += (this._fact[p] || BigFraction(0)).valueOf() * cachedLog2(p);
      }
      return ret;
    }
    // We also have a special case for base 1:
    if (i.equals(1)) {
      return Math.log2(this.valueOf()) / 0;
    }
    // Otherwise we just have an unfolded version of:
    // const [g, j] = this.factorOut(base);
    // return g.valueOf() + Math.log2(j.valueOf()) / Math.log2(base.valueOf());
    const [base, base_log2] = [i, i.valueOf_log()];
    const gp = maxKey(i._fact);
    const g = (this._fact[gp] || BigFraction(0)).div(base._fact[gp]);
    let ret = g.valueOf();
    for (const p of keys(this._fact, base._fact)) {
      const e = (this._fact[p] || BigFraction(0)).sub((base._fact[p] || BigFraction(0)).mul(g));
      ret += e.valueOf() * cachedLog2(p) / base_log2;
    }
    return ret;
  },

  /**
   * Reduces an interval w.r.t. another interval. If no argument is given, it
   * is taken to be 2 (an octave).
   *
   * e.g. `Interval(3,2).pow(2).red()` is exactly `Interval(9,8)`
   *
   * For all intervals `i`, `j` this function satisfies the equality:
   * `i.div(i.red(j)).equals(j.pow(Math.floor(i.valueOf_log(j))))`
   *
   * @param {Interval} [i=Interval(2)]
   * @returns {Interval}
   */
  "red": function(a,b) {
    let base = new Interval(2);
    if (a != undefined || b != undefined) {
      base = new Interval(a,b);
    }
    const e = Math.floor(this.valueOf_log(base));
    return this.div(base.pow(e));
  },

  /**
   * Balanced reduces an interval w.r.t. another interval. If no argument is
   * given, the it is taken to be 2 (an octave).
   *
   * e.g. `Interval(3,2).reb()` is exactly `Interval(2,3)`
   *
   * For all intervals `i`, `j` this function satisfies the equality:
   * `i.div(i.reb(j)).equals(j.pow(Math.round(i.valueOf_log(j))))`
   *
   * @param {Interval} [i=Interval(2)]
   * @returns {Interval}
   */
  "reb": function(a,b) {
    let base = new Interval(2);
    if (a != undefined || b != undefined) {
      base = new Interval(a,b);
    }
    const e = Math.round(this.valueOf_log(base));
    return this.div(base.pow(e));
  },

  /**
   * Returns the "distance" between two intervals, or if no second interval is
   * given, between the first interval and `1`. By "distance" here, we mean
   * whichever of `i1.div(i2)` and `i2.div(i1)` is greater than `1`.
   *
   * e.g. `Interval(5,4).distance(3,2)` is exactly `Interval(6,5)`
   *      `Interval(2,3).distance()` is exactly `Interval(3,2)`
   *
   * @param {Interval} [i=Interval(1)]
   * @returns {Interval}
   */
   "distance": function(a,b) {
     const q = this.div(a,b);
     return q.compare(1) < 0 ? q.recip() : q;
   },

  /**
   * Converts an interval to its value in cents.
   *
   * e.g. `Interval(3,2).toCents()` gives `701.9550008653873`
   *
   * Note that this function uses `factorOut` to preserve as much precision as
   * possible - for example, for any fraction `k`,
   * `Interval(2).pow(k).toCents() == k.mul(1200)` *exactly*.
   *
   * e.g. `Interval(2).pow(4,12).toCents()` is exactly `400`
   *
   * @returns {number}
   */
  "toCents": function() {
    let ret = 0;
    for (const p in this._fact) {
      ret += (this._fact[p] || BigFraction(0)).mul(1200).valueOf() * cachedLog2(p);
    }
    return ret;
  },

  /**
   * Converts an interval to its Benedetti height
   *
   * e.g. `Interval(3,2).benedettiHeight()` gives `6`
   *
   * @returns {number}
   */
  "benedettiHeight": function() {
    if (this._isApprox) {
      throw new Error("interval does not have a prime factorization");
    }
    let ret = 1;
    for (const p in this._fact) {
      ret *= p ** this._fact[p].abs().valueOf();
    }
    return ret;
  },

  /**
   * Converts an interval to its Tenney harmonic distance, or Tenney height,
   * the log base 2 of its Benedetti height
   *
   * e.g. `Interval(3,2).tenneyHD()` gives `2.584962500721156`
   *
   * @returns {number}
   */
  "tenneyHD": function() {
    if (this._isApprox) {
      throw new Error("interval does not have a prime factorization");
    }
    let ret = 0;
    for (const p in this._fact) {
      ret += this._fact[p].abs().valueOf() * cachedLog2(p);
    }
    return ret;
  },

  /**
   * Converts an interval to a monzo.
   *
   * e.g. `Interval(11,9).toMonzo()` gives `[0,-2,0,0,1]`
   *
   * @returns {number}
   */
  "toMonzo": function() {
    if (this._isApprox) {
      throw new Error("interval does not have a prime factorization");
    }
    const gp = maxKey(this._fact);
    let [ret, isFrac] = [[], true];
    for (const p of primes()) {
      if (p > gp) { break; }
      ret.push(this._fact[p] || BigFraction(0));
      isFrac &= !this._fact[p] || this._fact[p].d == 1;
    }
    return ret.map(r => isFrac ? Number(r.s * r.n) : unBigFraction(r));
  },

  /**
   * Returns true iff the interval is in the given prime limit, i.e. has a
   * factorization only containing primes smaller than the given prime number.
   *
   * e.g. `Interval(11,9).inPrimeLimit(11)` is true but
   *      `Interval(11,9).inPrimeLimit(7)` is false
   *
   * @returns {boolean}
   */
  "inPrimeLimit": function (p) {
    return !this._isApprox && 2 <= p && Object.keys(this._fact).every(pi => pi <= p);
  },

  /**
   * Returns the smallest prime limit which contains this interval, i.e. the
   * smallest prime for which `inPrimeLimit` returns true.
   *
   * @returns {integer}
   */
  "primeLimit": function () {
    if (this._isApprox) {
      throw new Error("interval does not have a prime factorization");
    }
    return Math.max(2, ...Object.keys(this._fact).map(pi => parseInt(pi)));
  },

  /**
   * Returns true iff the interval is a fraction in the given odd limit, i.e.
   * has numerator and denominor which are less than the given number if they're
   * odd, respectively.
   *
   * e.g. `Interval(16,9).inOddLimit(9)` is true but
   *      `Interval(16,9).inOddLimit(7)` is false
   *
   * @returns {boolean}
   */
  "inOddLimit": function (o) {
    if (!this.isFrac()) { return false; }
    const {n,d} = this.toFracBig();
    return (n % 2n == 0n || n <= BigInt(o)) && (d % 2n == 0n || d <= BigInt(o));
  },

  /**
   * Returns the smallest odd limit which contains this interval, i.e. the
   * smallest odd number for which `inOddLimit` returns true.
   *
   * @returns {integer}
   */
  "oddLimit": function () {
    const {n,d} = this.toFrac();
    return n % 2 == 0 ? d : d % 2 == 0 ? n : Math.max(n,d);
  },

  // ~~~~~~~~~~~~~~~~~~~~~~~
  //  Approximate functions

  /**
   * Adds two intervals together, approximately if either interval is not a
   * fraction. NB: If either interval is not a fraction, the result may not
   * have a prime factorization, so functions like `factors`, `hasExp`, etc.
   * may not work.
   *
   * @param {Interval} i
   * @returns {Interval}
   */
  "add": function (a,b) {
    const rhs = new Interval(a,b);
    try {
      const [this_fr, rhs_fr] = [this.toFracRaw(), rhs.toFracRaw()];
      return new Interval(this_fr.n * rhs_fr.d + rhs_fr.n * this_fr.d,
                          this_fr.d * rhs_fr.d)
    }
    catch (e) {
      return new Interval(this.valueOf() + rhs.valueOf());
    }
  },

  /**
   * Subtracts two intervals, approximately if either interval is not a
   * fraction. Errors if the result would not be a valid interval (i.e. <= 0).
   * NB: If either interval is not a fraction, the result may not have a prime
   * factorization, so functions like `factors`, `hasExp`, etc. may not work.
   *
   * @param {Interval} i
   * @returns {Interval}
   */
  "sub": function (a,b) {
    const rhs = new Interval(a,b);
    const x = this.valueOf() - rhs.valueOf();
    if (x <= 0) {
      throw new Error("result of `sub` would be " + x + " <= 0")
    }
    try {
      const [this_fr, rhs_fr] = [this.toFracRaw(), rhs.toFracRaw()];
      return new Interval(this_fr.n * rhs_fr.d - rhs_fr.n * this_fr.d,
                          this_fr.d * rhs_fr.d)
    }
    catch (e) {
      return new Interval(x);
    }
  },

  /**
   * If "a : b : c" is an isoharmonic triple (e.g. 4 : 5 : 6), then
   * `c.isoMid(a)` is `b = (c + a)/2`. NB: This function uses `add`, be aware
   * of the caveats of using that method.
   *
   * e.g. `Interval(5).sqrt(2).isoMid()` is the golden ratio: (sqrt(5) + 1)/2
   *
   * @param {Interval} [i=Interval(1)]
   * @returns {Interval}
   */
  "isoMid": function(a,b) {
    return this.add(a,b).div(2);
  },

  /**
   * If "a : b : c" is an isoharmonic triple (e.g. 4 : 5 : 6), then
   * `b.isoMid(a)` is `c = 2*b - a`. NB: This method uses `sub`, be aware of
   * the caveats of using that method.
   *
   * @param {Interval} [i=Interval(1)]
   * @returns {Interval}
   */
  "isoUp": function(a,b) {
    return this.mul(2).sub(a,b);
  },

  /**
   * If "a : b : c" is an isoharmonic triple (e.g. 4 : 5 : 6), then
   * `c.isoMid(b)` is `a = 2*b - c`. NB: This method uses `sub`, be aware of
   * the caveats of using that method.
   *
   * @param {Interval} [i=Interval(1)]
   * @returns {Interval}
   */
  "isoDown": function(a,b) {
    return Interval(a,b).mul(2).sub(this);
  },

  /**
   * `b.iso(a,n)` is the nth entry in the isoharmonic chord starting "a : b",
   * i.e. the interval `n*b - (n-1)*a`
   *
   * e.g. `Interval(5).iso(4, 2)` is `Interval(6)` (or `Interval(5).isoUp(4)`),
   *      `Interval(5).iso(4, 3)` is `Interval(7)`,
   *      `Interval(5).iso(4, 4)` is `Interval(8)`, etc.
   *
   * You can also give negative or fractional values to this function.
   *
   * e.g. `Interval(5).iso(4, -1)` is `Interval(3)` (or `Interval(5).isoDown(4)`),
   *      `Interval(6).iso(4, 1/2)` is `Interval(5)` (or `Interval(6).isoMid(4)`)
   *
   * NB: This method uses `sub` and `add`, be aware of the caveats of using
   * these methods.
   *
   * @param {Interval} i
   * @param {Fraction} n
   * @returns {Interval}
   */
  "iso": function(a,b,c,d) {
    const [rhs,n] = c == undefined ? [Interval(a), Fraction(b)]
                                   : [Interval(a,b), Fraction(c,d)];
    const ncmp1 = n.compare(1);
    if (ncmp1 > 0) {
      return this.mul(n).sub(rhs.mul(n.sub(1)));
    }
    if (ncmp1 == 0) {
      return this.mul(1);
    }
    const ncmp0 = n.compare(0);
    if (ncmp0 > 0) {
      return this.mul(n).add(rhs.mul(Fraction(1).sub(n)));
    }
    if (ncmp0 == 0) {
      return rhs;
    }
    return rhs.mul(Fraction(1).sub(n)).sub(this.mul(n.neg()));
  },

  /**
   * `b.iso1(n)` is the nth entry in the isoharmonic chord starting "1 : b",
   * the same as `b.iso(1,n)`.
   *
   * NB: This method uses `sub` and `add`, be aware of the caveats of using
   * these methods.
   *
   * @param {Fraction} n
   * @returns {Interval}
   */
  "iso1": function(a,b) {
    return this.iso(1, Fraction(a,b));
  },

  /**
   * `b.invIso1(k_max)` returns an array of pairs [(i1,k1), ..., (in,kn)] such
   * that for each (i,k) in the list, `i.hasFactors()` and b.equals(i.iso1(k))`.
   * The `k_max` argument limits the values each `k` can take - in particular,
   * each k will be a ratio whose numerator and denominator are both less than
   * or equal to k_max (ignoring sign) and which is not equal to 0/1 or 1/1.
   *
   * If the interval is a fraction, each possible value of k will be present
   * in the returned array. Otherwise, there will be at most one entry in the
   * returned array.
   *
   * @param {integer} [k_max=2]
   * @returns {Array.<Pair.<Interval,integer>>}
   */
  "invIso1": function(k_max) {
    if (k_max == undefined) { k_max = 2; }
    // if the input is not a fraction, there is at most one possible answer -
    //  so if this variable is false, we return the first answer found
    const thisIsFrac = this.isFrac();
    // if the input is an nth root but not a fraction, there's definitely no answer
    if (!thisIsFrac && this.hasFactors()) {
      return [];
    }
    let res = [];
    for (let d = 1; d <= k_max; d++) {
      for (let n = -k_max; n <= k_max; n++) {
        const k = Fraction(n,d);
        if (k.d != d || k.n == 0 || k.equals(1)) { continue; }
        try {
          const i = this.iso1(k.inverse());
          if (i.hasFactors()) {
            if (thisIsFrac) { res.push([i,k]); }
            else            { return  [[i,k]]; }
          }
        } catch (_) { }
      }
    }
    return res.sort((a,b) => a[1].compare(b[1]));
  },

  /**
   * Approximates the noble mediant of two intervals with integer prime
   * exponents, i.e. two intervals which can be expressed as fractions. NB: The
   * result of using this method will not have a prime factorization, so
   * functions like `factors`, `hasExp`, etc. will not work.
   *
   * e.g. `Interval(5,4).nobleMed(9,7).toCents()` is `422.4873963821663`
   *
   * @param {Interval} i
   * @returns {Interval}
   */
  "nobleMed": function(a,b) {
    const phi = 1.618033988749895; // Interval.phi.valueOf()
    let [f1, f2] = [this.toFracRaw(), Interval(a,b).toFracRaw()];
    return new Interval((Number(f1.n) + Number(f2.n) * phi) /
                        (Number(f1.d) + Number(f2.d) * phi));
  }

}

/**
 * The golden ratio: (sqrt(5) + 1)/2.
 *
 * @constant {Interval}
 */
Interval.phi = Interval(5).sqrt().isoMid();

module.exports = Interval;

},{"./utils.js":13,"big-integer":14,"fraction.js":16,"fraction.js/bigfraction.js":15,"primes-and-factors":20}],8:[function(require,module,exports){
/**
 * Interface for parsing interval/note expressions
 * @copyright 2021 Matthew Yacavone (matthew [at] yacavone [dot] net)
 * @module parser
 **/

const {mod} = require('./utils.js');
const ne = require('nearley');
const Fraction = require('fraction.js');
const Interval = require('./interval.js');
const grammar = require('./parser/grammar.js');
const {ParseError, OtherError, evalExpr} = require('./parser/eval.js');
const {isPythagorean, pySymb, pyNote} = require('./pythagorean.js');
const {fjsSymb, fjsNote, fjsSpec, nfjsSpec} = require('./fjs.js');
const {edoApprox, edoPy, updnsSymb, updnsNote} = require('./edo.js');
const {colorSymb, colorNote} = require('./color.js');
const {enNames} = require('./english.js');

function expectedSymbols(parser) {
  let symbs = [];
  const lastColumnIndex = parser.table.length - 2;
  const lastColumn = parser.table[lastColumnIndex];
  const expectantStates = lastColumn.states
      .filter(function(state) {
          var nextSymbol = state.rule.symbols[state.dot];
          return nextSymbol && typeof nextSymbol !== "string";
      });

  const stateStacks = expectantStates
      .map(function(state) {
          return parser.buildFirstStateStack(state, []) || [state];
      }, parser);
  // Display each state that is expecting a terminal symbol next.
  stateStacks.forEach(function(stateStack) {
      var state = stateStack[0];
      var nextSymbol = state.rule.symbols[state.dot];
      var symbolDisplay = parser.getSymbolDisplay(nextSymbol);
      symbs.push(symbolDisplay);
  }, parser);

  // remove duplicates
  symbs = [...new Set(symbs)];
  symbs.sort((a,b) => a.length - b.length);
  if (symbs.length > 1) {
    symbs[symbs.length-1] = "or " + symbs[symbs.length-1];
  }
  return "expected " + (symbs.length > 0 ? "a " + symbs.join(", ") : "nothing");
}

/**
  * Returns the raw output of calling the parser on the given string, with no
  * evaluation or post-processing. Use `parse` to get a nicely-formatted version
  * of calling this function with start = "top1".
  *
  * @param {string} str
  * @param {string} [start="top1"] the grammar rule to start parsing from
  * @returns {Array}
  */
function parseFromRule(str, start) {
  if (start === undefined) {
    start = grammar.ParserStart;
  }
  else if (!grammar.ParserRules.some(r => r.name == start)) {
    throw new Error("Invalid start rule: " + start);
  }
  // These first two lines are adapated from the nearley source code of
  //  `ne.Grammar.fromCompiled`, since I can't figure out how to start from a
  //  specific rule using the given API
  const rules = grammar.ParserRules.map(r => new ne.Rule(r.name, r.symbols, r.postprocess));
  const parser = new ne.Parser(new ne.Grammar(rules, start));
  try {
    parser.feed(str);
    // the below will ensure an error is thrown if the input has no parses
    if (parser.results.length == 0) {
      parser.feed("$");
    }
    return parser.results;
  }
  catch (err) {
    if (err.offset != undefined) {
      if (err.name != "LocatedError") {
        err = new ParseError(expectedSymbols(parser), err.offset);
      }
      throw err.toError(str);
    }
    else {
      throw err;
    }
  }
}

/**
  * Parse a monzo.
  *
  * @param {string} str
  * @returns {Interval}
  */
function parseMonzo(str) {
  return parseFromRule(str, "monzo")[0];
}

/**
  * Parse a Pythagorean interval symbol, the inverse of `pySymb`.
  *
  * @param {string} str
  * @returns {Interval}
  */
function parsePySymb(str) {
  return evalExpr(parseFromRule(str, "anyPyIntv")[0]).val;
}

/**
  * Parse a Pythagorean note symbol and return its interval to A4, the inverse
  * of `pyNote`.
  *
  * @param {string} str
  * @returns {Interval}
  */
function parsePyNote(str) {
  return evalExpr(parseFromRule(str, "anyPyNote")[0]).val;
}

/**
  * Parse an FJS interval symbol, the inverse of `fjsSymb`.
  *
  * @param {string} str
  * @param {FJSLike} [spec=fjsSpec]
  * @returns {Interval}
  */
function parseFJSSymb(str, spec) {
  if (!spec) { spec = fjsSpec; }
  const result = parseFromRule(str, "fjsLikeIntv")[0];
  return evalExpr(result, undefined, {fjsLikeSpecs: [spec]}).val;
}

/**
  * Parse an FJS note symbol and return its interval to A4, the inverse of
  * `fjsNote`.
  *
  * @param {string} str
  * @param {FJSLike} [spec=fjsSpec]
  * @returns {Interval}
  */
function parseFJSNote(str, spec) {
  if (!spec) { spec = fjsSpec; }
  const result = parseFromRule(str, "fjsLikeNote")[0];
  return evalExpr(result, undefined, {fjsLikeSpecs: [spec]}).val;
}

/**
  * Parse an ups-and-downs notation symbol and return the number of steps it
  * corresponds to in the given EDO, the inverse of `updnsSymb`.
  *
  * @param {integer} edo
  * @param {string} str
  * @returns {integer}
  */
function parseUpdnsSymb(edo, str) {
  const result = parseFromRule(str, "upsDnsIntv")[0];
  return evalExpr(result, undefined, {}, {edo: edo}).val;
}

/**
  * Parse an ups-and-downs notation note and return the number of steps to A4 it
  * corresponds to in the given EDO, the inverse of `updnsNote`.
  *
  * @param {integer} edo
  * @param {string} str
  * @returns {integer}
  */
function parseUpdnsNote(edo, str) {
  const result = parseFromRule(str, "upsDnsNote")[0];
  return evalExpr(result, undefined, {}, {edo: edo}).val;
}

/**
  * Parse a color notation interval symbol, the inverse of `colorSymb`.
  *
  * @param {string} str
  * @returns {Interval}
  */
function parseColorSymb(str) {
  return evalExpr(parseFromRule(str, "anyClrIntv")[0]).val;
}

/**
  * Parse a color notation note symbol and return its interval to A4, the
  * inverse of `colorNote`.
  *
  * @param {string} str
  * @returns {Interval}
  */
function parseColorNote(str) {
  return evalExpr(parseFromRule(str, "anyClrNote")[0]).val;
}

/**
 * @typedef {Object} ParseResult
 * @property {string} type either "interval", "note", or "edo"
 * @property {string} queryType either "multiplicative", "additive", or "symbol",
 *                              if `type` is not "edo", or "name" otherwise
 * @property {string=} symbolType only defined if queryType is "symbol"
 * @property {Interval} intv the resulting interval (to the reference, if
 *                           type is "note"), if `type` is not "edo"
 * @property {integer} edo the value of the parsed EDO, if `type` is "edo"
 * @property {{hertz: Interval, intvToA4: Interval}} refNote the reference note
 * @property {integer=} prefEDO the preferred EDO, if any, of the interval
 */

/**
  * Parses the given string using the entire grammar and evaluates the result
  *
  * @param {string} str
  * @param {EvalOpts} [opts] options to pass to `evalExpr` from `parser/eval.js`
  * @returns {ParseResult}
  */
function parse(str, opts) {

  let results = parseFromRule(str, "top1");

  try {
    for (let i = 0; i < results.length; i++) {
      try {
        const res = evalExpr(results[i].expr, results[i].refNote, opts);
        results[i].val = res.val;
        results[i].prefEDO = res.prefEDO;
      }
      catch (err) {
        results[i].err = err;
      }
    }
    const resultsNoErrors = results.filter(d => d.err == undefined);
    if (resultsNoErrors.length == 0) {
      throw results[0].err;
    }
    else {
      results = resultsNoErrors;
    }
  }
  catch (err) {
    if (err.offset != undefined) {
      if (err.name != "LocatedError") {
        err = new OtherError(err.message, err.offset);
      }
      throw err.toError(str);
    }
    else {
      throw err;
    }
  }

  if (results.length == 1 && results[0].type[0] == "EDO") {
    return { type: results[0].type[0]
           , queryType: results[0].type[1]
           , edo: parseInt(results[0].val)
           , refNote: results[0].refNote };
  }

  if (results.some(d => d.type[0] == "interval" && d.type[1] == "symbol")) {
    results = results.filter(d => !(d.type[0] == "interval" && d.type[1] != "symbol"));
  }
  if (results.some(d => d.type[0] == "note" && d.type[1] == "symbol")) {
    results = results.filter(d => !(d.type[0] == "note" && d.type[1] != "symbol"));
  }
  if (results.length > 1) {
    console.dir("Parse was ambiguous on: \'" + str + "\' - full results:");
    console.dir(results, { depth: null });
  }
  let ret = { type: results[0].type[0]
            , queryType: results[0].type[1]
            , symbolType: results[0].symbolType
            , intv: results[0].val
            , refNote: results[0].refNote
            , prefEDO: results[0].prefEDO };

  // If `intv` is an EDO step (i.e. a fractional power of two),
  if (ret.intv.inPrimeLimit(2)) {
    let e2 = ret.intv.expOf(2);
    // forget `ret.prefEDO` if `ret.intv` is not `2^(k/prefEDO)` (sanity check)
    if (ret.prefEDO && e2.mul(ret.prefEDO).d != 1) {
      delete ret.prefEDO;
    }
    // forget `ret.prefEDO` if it is less than 2
    if (ret.prefEDO < 2) {
      delete ret.prefEDO;
    }
    // set `ret.prefEDO` if `ret.intv` is a simple enough power of two
    if (!ret.prefEDO && (e2.d == 2 || e2.d == 3 || e2.d == 4)) {
      ret.prefEDO = 12;
    }
    if (!ret.prefEDO && 4 < e2.d && e2.d <= 60) {
      ret.prefEDO = e2.d;
    }
  }
  // Otherwise, forget `ret.prefEDO` (sanity check)
  else {
    delete ret.prefEDO;
  }

  return ret;
}

/**
 * @typedef {Object} IntvParseCvtResult
 * @property {string} type always "interval"
 * @property {string} queryType either "multiplicative", "additive", or "symbol"
 * @property {string=} symbolType only defined if queryType is "symbol"
 * @property {number} cents the resulting interval converted to cents
 * @property {Interval} intv the resulting interval object
 * @property {ReferenceNote} ref the reference note
 * @property {Fraction=} ratio the resulting interval as a JI ratio
 * @property {Pair.<integer,integer>=} edoSteps the resulting interval as some
 *                                              number of EDO steps
 * @property {Object.<string,number>=} height various heights for the resulting
                                              interval as a JI ratio
 * @property {Object.<string,string>} symb various symbols for the resulting
 *                                         interval, including FJS,
 *                                         Neutral FJS, and ups-and-downs
 *                                         notations
 * @property {Array.<string>} english (experimental) english name for the
 *                                    resulting interval, based on
 *                                    Neutral FJS and ups-and-downs notations
 */

/**
 * @typedef {Object} NoteParseCvtResult
 * @property {string} type always "note"
 * @property {string} queryType either "multiplicative", "additive", or "symbol"
 * @property {string=} symbolType only defined if queryType is "symbol"
 * @property {number} freq the resulting interval converted to hertz
 * @property {Interval} intvToRef the resulting interval to the reference
 * @property {Pair.<integer,integer>=} edoStepsToRef the resulting interval as
 *                                                   some number of EDO steps
 *                                                   to the reference
 * @property {ReferenceNote} ref the reference note
 * @property {Object.<string,string>} symb various symbols for the resulting
 *                                         interval, including FJS and
 *                                         ups-and-downs notations
 */

/**
 * @typedef {Object} EDOParseCvtResult
 * @property {string} type always "edo"
 * @property {string} queryType always "name"
 * @property {integer} edo the EDO parsed
 * @property {ReferenceNote} ref the reference note
 * @property {Array.<EDOStepParseCvtResult>} intvs the intervals of the EDO
 */

/**
 * @typedef {Object} EDOStepParseCvtResult
 * @property {integer} steps the number of EDO steps of the interval
 * @property {number} cents the EDO step interval interval converted to cents
 * @property {string} ups_and_downs the EDO step as an ups-and-downs symbol
 * @property {string} ups_and_downs_verbose
 */

/**
 * @typedef {Object} ReferenceNote
 * @property {Interval} hertz
 * @property {Interval} intvToA4
 * @property {Pair.<integer,integer>=} edoStepsToA4
 */

/**
  * Parses the given string using the entire grammar and converts the result to
  * some convenient forms
  *
  * @param {string} str
  * @param {EvalOpts} [opts] options to pass to `evalExpr` from `parser/eval.js`
  * @returns {IntvParseCvtResult|NoteParseCvtResult}
  */
function parseCvt(str, opts) {
  let {type, queryType, symbolType, intv, edo, refNote, prefEDO} = parse(str, opts);
  let ret = { type: type, queryType: queryType };
  if (symbolType != undefined) { ret.symbolType = symbolType; }
  if (type == "EDO") {
    ret.edo = edo;
    ret.ref = { hertz: refNote.hertz.valueOf()
              , intvToA4: refNote.intvToA4 };
    ret.intvs = [];
    for (let i = 0; i < edo; i++) {
      let entry = { steps: i, cents: 1200 * i / edo };
      entry.ups_and_downs = updnsSymb(edo,i, {useExps:1});
      entry.ups_and_downs_verbose = updnsSymb(edo,i, {verbosity:1, useExps:1});
      ret.intvs.push(entry);
    }
  }
  if (type == "interval") {
    ret.cents = intv.toCents();
    ret.intv = intv;
    ret.ref = { hertz: refNote.hertz.valueOf()
              , intvToA4: refNote.intvToA4 };
    try {
      ret.ratio = intv.toFrac();
      let heights = { benedetti: intv.benedettiHeight()
                    , tenney:    intv.tenneyHD() }
      ret.height = heights;
    } catch (_) {}
    if (prefEDO) {
      let e2 = intv.expOf(2).mul(prefEDO);
      ret.edoSteps = [e2.s*e2.n, prefEDO];
    }
    if (!intv.isFrac()) {
      try {
        const isos = intv.invIso1(6);
        if (isos.length > 0) { ret.iso = isos[0]; };
      } catch (_) { }
    }
    ret.symb = {};
    if (isPythagorean(intv)) {
      ret.symb.py = pySymb(intv);
      ret.symb.py_verbose = pySymb(intv, {verbosity: 1});
    }
    else if (intv.hasFactors()) {
      let fjs = fjsSymb(intv);
      let nfjs = fjsSymb(intv, nfjsSpec);
      if (fjs) {
        ret.symb.FJS = fjs;
      }
      if (nfjs && nfjs != fjs) {
        ret.symb.NFJS = nfjs;
      }
    }
    if (prefEDO) {
      let e2 = intv.expOf(2).mul(prefEDO);
      ret.symb.ups_and_downs =
        updnsSymb(prefEDO,e2.s*e2.n, {useWordDesc:1, useExps:1})
          .map(s => s + "\\" + prefEDO);
      ret.symb.ups_and_downs_verbose =
        updnsSymb(prefEDO,e2.s*e2.n, {verbosity:1, useWordDesc:1, useExps:1})
          .map(s => s + " \\ " + prefEDO);
    }
    if (ret.ratio) {
      try {
        ret.symb.color = colorSymb(intv, {verbosity: 0});
      } catch (_) {}
      try {
        ret.symb.color_verbose = colorSymb(intv, {verbosity: 1});
      } catch (_) {}
    }
    if (intv.equals(Interval(2).sqrt())) {
      ret.symb.other = "TT";
    }
    if (intv.equals(Interval.phi)) {
      ret.symb.other = "phi";
    }
    try {
      const nms = enNames(intv, {prefEDO: prefEDO});
      if (nms.length > 0) {
        ret.english = nms;
      }
    } catch (_) {}
  }
  if (type == "note") {
    ret.hertz = refNote.hertz.mul(intv).valueOf();
    const intvToA4 = intv.mul(refNote.intvToA4);
    const closest12EDO = edoApprox(12, intvToA4);
    const diffTo12EDO = intvToA4.div(Interval(2).pow(closest12EDO,12)).toCents();
    ret.tuningMeter = updnsNote(12, mod(closest12EDO+9,12)-9, {useExps:1}).join("/") + " "
                      + (diffTo12EDO == 0 ? "±" : diffTo12EDO > 0 ? "+" : "-")
                      + Math.abs(diffTo12EDO).toFixed(1) + "c";
    ret.intvToRef = intv;
    if (prefEDO) {
      let e2 = intv.expOf(2).mul(prefEDO);
      ret.edoStepsToRef = [e2.s*e2.n, prefEDO];
    }
    ret.ref = { hertz: refNote.hertz.valueOf()
              , intvToA4: refNote.intvToA4 };
    ret.symb = {};

    if (isPythagorean(intv)) {
      ret.symb.py = pyNote(intv);
    }
    else if (intv.hasFactors()) {
      let fjs = fjsNote(intvToA4);
      if (fjs) {
        ret.symb.FJS = fjs;
      }
    }
    if (prefEDO) {
      const refEDOStepsToA4 = edoPy(prefEDO, refNote.intvToA4);
      ret.ref.edoStepsToA4 = [refEDOStepsToA4, prefEDO];
      let e2 = intv.expOf(2).mul(prefEDO).add(refEDOStepsToA4);
      ret.symb.ups_and_downs = updnsNote(prefEDO,e2.s*e2.n, {useExps:1}).map(s => s + "\\" + prefEDO);
    }
    if (intv.isFrac()) {
      try {
        ret.symb.color = colorNote(intvToA4, {verbosity: 0});
      } catch (_) {}
      try {
        ret.symb.color_verbose = colorNote(intvToA4, {verbosity: 1});
      } catch (_) {}
    }
  }
  return ret;
}

module['exports'].parseFromRule = parseFromRule;
module['exports'].parseMonzo = parseMonzo;
module['exports'].parsePySymb = parsePySymb;
module['exports'].parsePyNote = parsePyNote;
module['exports'].parseFJSSymb = parseFJSSymb;
module['exports'].parseFJSNote = parseFJSNote;
module['exports'].parseUpdnsSymb = parseUpdnsSymb;
module['exports'].parseUpdnsNote = parseUpdnsNote;
module['exports'].parseColorSymb = parseColorSymb;
module['exports'].parseColorNote = parseColorNote;
module['exports'].parse = parse;
module['exports'].parseCvt = parseCvt;

},{"./color.js":2,"./edo.js":3,"./english.js":4,"./fjs.js":5,"./interval.js":7,"./parser/eval.js":9,"./parser/grammar.js":10,"./pythagorean.js":11,"./utils.js":13,"fraction.js":16,"nearley":18}],9:[function(require,module,exports){
/**
 * A function for evaluating the results of running `grammar.ne`
 * @copyright 2021 Matthew Yacavone (matthew [at] yacavone [dot] net)
 * @module eval
 **/

const pf = require('primes-and-factors');
const Fraction = require('fraction.js');
const Interval = require('../interval.js');
const {pyInterval, pyRedDeg, isPerfectDeg} = require('../pythagorean.js');
const {fjsFactor, fjsSpec, nfjsSpec} = require('../fjs.js');
const {edoApprox, edoHasNeutrals, edoHasSemiNeutrals, updnsFromSymb} = require('../edo.js');
const {colorFromSymb, colorFromNote} = require('../color.js');

/**
 * Class representing an error with a location in a string
 * @extends Error
 */
class LocatedError extends Error {
  /**
   * Create a `LocatedError`
   * @param {string} kind e.g. "Parse error" or "Error"
   * @param {string} message
   * @param {integer} loc the index of where the error occurs in a string
   */
  constructor(kind, message, loc) {
    super(message);
    this.name = "LocatedError";
    this.kind = kind;
    this.offset = loc;
  }
  /**
   * Format a `LocatedError` using the string the error is about, producing a
   * regular `Error` with a nicely formatted `message`
   * @param {string} str
   */
  toError(str) {
    const errStr = "\n" + str + "\n" + " ".repeat(this.offset) + "^\n"
                   + this.kind + ": " + this.message;
    let err = new Error(errStr);
    err.kind = this.kind;
    err.offset = this.offset;
    err.srcStr = str;
    return err;
  }
}

/**
 * A `LocatedError` which is a parse error, i.e. has `kind` "Parse error"
 * @extends LocatedError
 */
class ParseError extends LocatedError {
  /**
   * Create a `ParseError`
   * @param {string} message
   * @param {integer} loc the index of where the error occurs in a string
   */
  constructor(message, loc) {
    super("Parse error", message, loc);
  }
}

/**
 * A `LocatedError` which is some other error, i.e. has `kind` "Error"
 * @extends LocatedError
 */
class OtherError extends LocatedError {
  /**
   * Create an `OtherError`
   * @param {string} message
   * @param {integer} loc the index of where the error occurs in a string
   */
  constructor(message, loc) {
    super("Error", message, loc);
  }
}

/**
  * The default reference note for the evaluator: A4 = 440Hz
  *
  * @constant {Interval}
  */
const defaultRefNote = { intvToA4: Interval(1), hertz: Interval(440) };

/**
 * @typedef {Object} EvalOpts
 * @param {Array.<FJSLike>} [fjsLikeSpecs=[fjsSpec,nfjsSpec]]
 *                          specs to use for FJS-like intervals, tried in the
 *                          order given based on whether they apply to the given
 *                          non-neutral/neutral/semi-neutral base Pythagorean
 *                          interval
 */

function cbnEDOs(a,b) {
  return a && b ? Fraction(1,a).gcd(1,b).d : undefined
}

/**
  * Evaluates the result of running `grammar.ne`
  *
  * @param {Array} e the expression to evaluate
  * @param {{hertz: Interval, intvToA4: Interval}} [refNote=defaultRefNote] the reference note
  * @param {EvalOpts} [opts] various options
  * @returns {{val: Interval, prefEDO: integer}}
  */
function evalExpr(e, r, opts, state) {
  if (!state) { state = {}; }
  let fjsLikeSpecs = [fjsSpec, nfjsSpec];
  if (opts && Array.isArray(opts.fjsLikeSpecs) && opts.fjsLikeSpecs.length > 0) {
    fjsLikeSpecs = opts.fjsLikeSpecs;
  }

  if (Array.isArray(e)) {
    // don't fail in the case of a nested array
    if (Array.isArray(e[0])) {
      console.log("evalExpr: nested arrays")
      return evalExpr(e[0], r, opts, state);
    }

    // 1 | Special cases:
    if (e[0] == "!isoExpr") {
      const args = e[1].map(([e1i,loc]) => [evalExpr(e1i, r, opts, state).val, loc]);
      const loc = e[2];
      // figure out the shape of the isoharmonic expression
      let [fstIntv, sndIntv, qs] = [undefined, undefined, 0];
      for (let i = 0; i < args.length; i++) {
        const [ai,loc] = args[i];
        if (ai === "?") {
          if (qs == 1) {
            throw new LocatedError("Isoharmonic expression cannot contain more than one `?`", loc);
          }
          qs++;
        }
        else if (ai !== "-") {
          if (fstIntv == undefined) {
            fstIntv = i;
          }
          else if (sndIntv == undefined) {
            sndIntv = i;
          }
        }
      }
      if (fstIntv == undefined || sndIntv == undefined) {
        throw new OtherError("Isoharmonic expression must contain at least two intervals", loc);
      }
      // check to make sure the whole expression is coherent
      let res = undefined;
      for (let i = 0; i < args.length; i++) {
        const [ai,loc] = args[i];
        const n = Fraction(i - fstIntv, sndIntv - fstIntv);
        let expected = undefined;
        try {
          expected = args[sndIntv][0].iso(args[fstIntv][0], n);
        }
        catch (e) {
          throw new OtherError("Invalid/impossible position in isoharmonic expression", loc);
        }
        if (ai === "?") {
          res = expected;
        }
        else if (ai !== "-" && !expected.equals(ai)) {
          const str = expected.hasFactors() ? ", should be: " + expected.toNthRootString() : "";
          throw new OtherError("Incorrect interval in isoharmonic expression" + str, loc);
        }
      }
      // return the result
      if (res) {
        return { val: res };
      }
      else if (args.length == 2) {
        return { val: args[1][0].div(args[0][0]) };
      }
      else {
        throw new OtherError("This is a valid isoharmonic chord, but it must contain one `?` to give a result", loc);
      }
    }
    else if (e[0] == "!refIntvToA4") {
      return { val: (r || defaultRefNote).intvToA4 };
    }
    else if (e[0] == "!refHertz") {
      return { val: (r || defaultRefNote).hertz };
    }
    else if (e[0] == "!med") {
      const arg0 = evalExpr(e[1], r, opts, state).val;
      const arg1 = evalExpr(e[2], r, opts, state).val;
      const loc = e[3];
      if (arg0.isFrac() && arg1.isFrac()) {
        return { val: arg0.med(arg1) };
      }
      else {
        throw new OtherError("One of the arguments to `med` is not a fraction", loc);
      }
    }
    else if (e[0] == "!nobleMed") {
      const arg0 = evalExpr(e[1], r, opts, state).val;
      const arg1 = evalExpr(e[2], r, opts, state).val;
      const [nm, loc] = [e[3], e[4]];
      if (arg0.isFrac() && arg1.isFrac()) {
        return { val: arg0.nobleMed(arg1) };
      }
      else {
        throw new OtherError("One of the arguments to `" + nm + "` is not a fraction", loc);
      }
    }
    else if (e[0] == "!isoUp1" || e[0] == "!isoDown1") {
      const arg0 = evalExpr(e[1], r, opts, state).val;
      const [nm, loc] = [e[2], e[3]];
      try {
        return { val: e[0] == "!isoUp1" ? arg0.isoUp()
                                        : arg0.isoDown() };
      }
      catch (err) {
        const str = e[0] == "!isoUp1" ? "greater than 1/2" : "less than 2";
        throw new OtherError("Argument to `" + nm + "` must be " + str, loc);
      }
    }
    else if (e[0] == "!isoUp2" || e[0] == "!isoDown2") {
      const arg0 = evalExpr(e[1], r, opts, state).val;
      const arg1 = evalExpr(e[2], r, opts, state).val;
      const [nm, loc] = [e[3], e[4]];
      try {
        return { val: e[0] == "!isoUp2" ? arg0.isoUp(arg1)
                                        : arg0.isoDown(arg1) };
      }
      catch (err) {
        const bound = e[0] == "!isoUp2" ? arg1.div(2) : arg1.mul(2);
        let str;
        // if arg1 is a 1, 2, 3, or 4th root
        if (bound.pow(3).isFrac() || bound.pow(4).isFrac()) {
          str = bound.toNthRootString();
        }
        else {
          str = bound.toCents().toFixed(5) + "c";
        }
        str = (e[0] == "!isoUp2" ? "greater than 1/2 * the first, i.e. > "
                                 : "less than 2 * the first, i.e. < ") + str;
        throw new OtherError("Second argument to `" + nm + "` must be " + str, loc);
      }
    }
    else if (e[0] == "!iso") {
      const arg0 = evalExpr(e[1], r, opts, state).val;
      const arg1 = evalExpr(e[2], r, opts, state).val;
      const arg2 = evalExpr(e[3], r, opts, state).val;
      const loc = e[4];
      try {
        return { val: arg0.iso(arg1, arg2) };
      }
      catch (err) {
        throw new OtherError("Result of `iso` out of range", loc);
      }
    }
    else if (e[0] == "!cents") {
      const arg0 = evalExpr(e[1], r, opts, state).val.div(1200);
      if (arg0.d < 100) {
        return { val: Interval(2).pow(arg0), prefEDO: arg0.d };
      }
      if (arg0.d < 1000) {
        return { val: Interval(2).pow(arg0) };
      }
      return { val: Interval(2 ** arg0.valueOf()) };
    }
    else if (e[0] == "!hertz") {
      const arg0 = evalExpr(e[1], r, opts, state).val;
      const arg1 = evalExpr(e[2], r, opts, state).val;
      const loc = e[3];
      if (arg0.compare(0) <= 0) {
        throw new OtherError("Hertz value cannot be negative or zero", loc);
      }
      return { val: Interval(arg0.valueOf()).div(arg1) };
    }
    else if (e[0] == "!edoApprox") {
      const arg0 = evalExpr(e[1], r, opts, state).val;
      const arg1 = evalExpr(e[2], r, opts, state).val;
      return { val: Interval(2).pow(edoApprox(arg1, arg0)).pow(1,arg1), prefEDO: arg1 };
    }
    else if (e[0] == "!inEDO") {
      const arg1 = evalExpr(e[2], r, opts, state).val;
      state.edo = arg1;
      const arg0 = evalExpr(e[1], r, opts, state).val;
      return { val: Interval(2).pow(arg0).pow(1,arg1), prefEDO: arg1 };
    }
    else if (e[0] == "!edoTT") { // `state.edo` should be set from "!inEDO"
      const loc = e[1];
      if (state.edo % 2 == 0) {
        return { val: state.edo / 2 };
      }
      else {
        throw new OtherError(state.edo + "-EDO does not have a tritone", loc);
      }
    }
    else if (e[0] == "!updnsSymb") { // `state.edo` should be set from "!inEDO"
      if (e[2][0] == "!perfPyIntv" && ![1,4,5].includes(pyRedDeg(e[2][1]))) {
        const [uds, deg, loc] = [e[1], e[2][1], e[3]];
        if (state.edo % 7 != 0) {
          throw new OtherError((uds > 0 ? "^" : "v").repeat(uds) + "P"
                                 + deg + " is not a valid interval ("
                                 + deg + " is not a perfect scale degree and "
                                 + state.edo + " is not a \"perfect\" EDO"
                                 + " in ups-and-downs notation)", loc);
        }
        try { return { val: updnsFromSymb(state.edo, uds, pyInterval(deg, 0)) }; }
        catch (err) {
          throw new OtherError(err.message, loc);
        }
      }
      const [uds, pyi, loc] = [e[1], evalExpr(e[2], r, opts, state).val, e[3]];
      try { return { val: updnsFromSymb(state.edo, uds, pyi) }; }
      catch (err) {
        throw new OtherError(err.message, loc);
      }
    }
    else if (e[0] == "!updnsPerfSymb") { // `state.edo` should be set from "!inEDO"
      const [uds, deg, loc] = [e[1], evalExpr(e[2], r, opts, state).val, e[3]];
      if (![1,4,5].includes(pyRedDeg(deg)) && state.edo % 7 != 0) {
        throw new OtherError((uds > 0 ? "^" : "v").repeat(uds)
                               + deg + " is not a valid interval ("
                               + deg + " is not a perfect scale degree and "
                               + state.edo + " is not a \"perfect\" EDO"
                               + " in ups-and-downs notation)", loc);
      }
      try { return { val: updnsFromSymb(state.edo, uds, pyInterval(deg, 0)) }; }
      catch (err) {
        throw new OtherError(err.message, loc);
      }
    }
    else if (e[0] == "!updnsNeutSymb") { // `state.edo` should be set from "!inEDO"
      const [uds, deg, loc] = [e[1], evalExpr(e[2], r, opts, state).val, e[3]];
      if (pyRedDeg(deg) == 1) {
        throw new OtherError((uds > 0 ? "^" : "v").repeat(uds) + "~" +
                               + deg + " is not a valid interval", loc);
      }
      const pyi = pyRedDeg(deg) == 4 ? pyInterval(deg, Math.sign(deg), 2) :
                  pyRedDeg(deg) == 5 ? pyInterval(deg, -Math.sign(deg), 2) :
                                       pyInterval(deg, 0);
      try { return { val: updnsFromSymb(state.edo, uds, pyi) }; }
      catch (err) {
        throw new OtherError(err.message, loc);
      }
    }
    else if (e[0] == "!updnsNote") { // `state.edo` should be set from "!inEDO"
      const [uds, pyi, loc] = [e[1], evalExpr(e[2], r, opts, state).val, e[3]];
      try { return { val: updnsFromSymb(state.edo, uds, pyi) }; }
      catch (err) {
        throw new OtherError(err.message, loc);
      }
    }
    else if (e[0] == "!perfPyIntv") {
      const [d, loc] = [e[1], e[2]];
      if (isPerfectDeg(d)) { return { val: pyInterval(d,0) }; }
      else { throw new OtherError("P" + d + " is not a valid interval ("
                                      + d + " is not a perfect scale degree)", loc); }
    }
    else if (e[0] == "!nonPerfPyIntv") {
      const [d, o, q, loc] = [e[1], e[2], e[3], e[4]];
      if (!isPerfectDeg(d)) { return { val: pyInterval(d,o) }; }
      else { throw new OtherError(q + d + " is not a valid interval ("
                                    + d + " is a perfect scale degree)", loc); }
    }
    else if (e[0] == "!augOrDimPyIntv") {
      const [d, a, b, loc] = [e[1], e[2], e[3], e[4]];
      const o = Fraction(a,b);
      const o_np = o.add(o.s,2);
      return { val: isPerfectDeg(d) ? pyInterval(d,o) : pyInterval(d,o_np) };
    }
    else if (e[0] == "!ensureNo2Or3") {
      const [k, loc] = [e[1], e[2]];
      if (k.equals(1) || k.hasExp(2) || k.hasExp(3)) {
        throw new OtherError("FJS accidental must be > 1 and cannot contain a factor or 2 or 3", loc);
      }
      return { val: k };
    }
    else if (e[0] == "!fjsFactor") {
      const arg0 = evalExpr(e[1], r, opts, state).val;
      const spec = e[2];
      return { val: fjsFactor(arg0, spec) };
    }
    else if (e[0] == "!fjsPy") {
      const [f, loc] = [e[1], e[2]];
      const spec = fjsLikeSpecs[0];
      return evalExpr(f(spec), r, opts, state);
    }
    else if (e[0] == "!fjsNPy") {
      const [f, loc] = [e[1], e[2]];
      const spec = fjsLikeSpecs.find(spec => spec.hasNeutrals);
      if (spec) {
        return evalExpr(f(spec), r, opts, state);
      }
      else {
        throw new OtherError("Neutral FJS-like interval not supported", loc);
      }
    }
    else if (e[0] == "!fjsSNPy") {
      const [f, loc] = [e[1], e[2]];
      const spec = fjsLikeSpecs.find(spec => spec.hasSemiNeutrals);
      if (spec) {
        return evalExpr(f(spec), r, opts, state);
      }
      else {
        throw new OtherError("Semi-neutral FJS-like interval not supported", loc);
      }
    }
    else if (e[0] == "!clrIntv") {
      const cs = evalExpr(e[1], r, opts, state).val;
      const m  = evalExpr(e[2], r, opts, state).val;
      const pps = e[3].map(ei => evalExpr(ei, r, opts, state).val); // prime powers
      const ps = pps.map(pp => pp.factors()[0][0]); // the primes in pps
      const d = evalExpr(e[4], r, opts, state).val;
      const loc = e[5];
      // ensure the list is decreasing
      if (pps.length > 0 && !ps.every((p,i) => i == 0 || p <= ps[i-1])) {
        throw new OtherError("Invalid color prefix (non-decreasing)", loc);
      }
      // ensure the list has only exact repetition
      if (pps.length > 0 && !pps.every((pp,i) => i == 0 || ps[i] != ps[i-1] || pp.equals(pps[i-1]))) {
        throw new OtherError("Invalid color prefix (bad repetition)", loc);
      }
      const i = pps.reduce(((a,b) => a.mul(b)), Interval(1));
      return { val: colorFromSymb(cs, m, i, d) };
    }
    else if (e[0] == "!clrNote") {
      const pps = e[1].map(ei => evalExpr(ei, r, opts, state).val); // prime powers
      const ps = pps.map(pp => pp.factors()[0][0]); // the primes in pps
      const [pyi, loc] = [evalExpr(e[2], r, opts, state).val, e[3]];
      // ensure the list is decreasing
      if (pps.length > 0 && !ps.every((p,i) => i == 0 || p <= ps[i-1])) {
        throw new OtherError("Invalid color prefix (non-decreasing)", loc);
      }
      // ensure the list has only exact repetition
      if (pps.length > 0 && !pps.every((pp,i) => i == 0 || ps[i] != ps[i-1] || pp.equals(pps[i-1]))) {
        throw new OtherError("Invalid color prefix (bad repetition)", loc);
      }
      const i = pps.reduce(((a,b) => a.mul(b)), Interval(1));
      return { val: colorFromNote(i, pyi) };
    }
    else if (e[0] == "!aclrPP") {
      const [p, x, loc] = [e[1], e[2], e[3]];
      if (p == 1) { return { val: Interval(11).pow(x) }; }
      if (p == 3) { return { val: Interval(13).pow(x) }; }
      if (!pf.isPrime(p)) {
        throw new OtherError("Expected a prime number", loc);
      }
      return { val: Interval(p).pow(x) };
    }
    else if (e[0] == "!clrMPs") {
      const [ps, loc] = [e[1].map(ei => evalExpr(ei, r, opts, state).val), e[2]];
      // ensure the list is decreasing
      if (ps.length > 0 && !ps.every((x,i) => i == 0 || x <= ps[i-1])) {
        throw new OtherError("Invalid color multi prefix (non-decreasing)", loc);
      }
      return { val: ps.reduce((a,b) => a * b, 1) };
    }
    else if (e[0] == "!clrGenPP") {
      const [p, loc] = [e[1], e[2]];
      if (!pf.isPrime(p)) {
        throw new OtherError(p + " is not a prime number", loc);
      }
      return { val: Interval(p) };
    }
    else if (e[0][0] == "!") {
      throw new LocatedError("Panic", "command " + e[0] + " not defined!", 0);
    }

    // for the remaining cases, we evaluate every argument
    const args = e.slice(1).map(ei => evalExpr(ei, r, opts, state));

    // 2 | Operators:
    if (e[0] == "+") { return { val: args[0].val + args[1].val }; }
    if (e[0] == "-") { return { val: args[0].val - args[1].val }; }
    if (e[0] == "*") { return { val: args[0].val * args[1].val }; }
    if (e[0] == "/") { return { val: args[0].val / args[1].val }; }

    // 3 | Otherwise, we assume `e[0]` is a method of `args[0]`
    let ret = { val: args[0].val[e[0]](...args.slice(1).map(argi => argi.val))
              , prefEDO: args.map(argi => argi.prefEDO).reduce(cbnEDOs) };
    // for some operations on intervals we don't want to look at every
    //  argument's perferred EDO
    if (e[0] == "pow") {
      ret.prefEDO = args[0].prefEDO;
    }
    if (e[0] == "red" || e[0] == "reb") {
      if (args[1] && args[1].equals && args[1].equals(2)) {
        ret.prefEDO = args[0].prefEDO;
      }
      else {
        ret.prefEDO = undefined;
      }
    }
    return ret;
  }
  if (e instanceof Interval && e.inPrimeLimit(2) && e.expOf(2) > 2) {
    return { val: e, prefEDO: e.expOf(2).d };
  }
  return { val: e };
}

module['exports'].LocatedError = LocatedError;
module['exports'].ParseError = ParseError;
module['exports'].OtherError = OtherError;
module['exports'].defaultRefNote = defaultRefNote;
module['exports'].evalExpr = evalExpr;

},{"../color.js":2,"../edo.js":3,"../fjs.js":5,"../interval.js":7,"../pythagorean.js":11,"fraction.js":16,"primes-and-factors":20}],10:[function(require,module,exports){
// Generated automatically by nearley, version 2.20.1
// http://github.com/Hardmath123/nearley
(function () {
function id(x) { return x[0]; }


const Fraction = require('fraction.js');
const Interval = require('../interval.js');
const {pyInterval, pyNote, pyRedDeg, baseNoteIntvToA} = require('../pythagorean.js');
const {fjsFactor, fjsSpec, nfjsSpec} = require('../fjs.js');
const {edoPy} = require('../edo.js');
const {ParseError, OtherError, defaultRefNote, evalExpr} = require('./eval.js');

var grammar = {
    Lexer: undefined,
    ParserRules: [
    {"name": "_$ebnf$1", "symbols": []},
    {"name": "_$ebnf$1", "symbols": ["_$ebnf$1", "wschar"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "_", "symbols": ["_$ebnf$1"], "postprocess": function(d) {return null;}},
    {"name": "__$ebnf$1", "symbols": ["wschar"]},
    {"name": "__$ebnf$1", "symbols": ["__$ebnf$1", "wschar"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "__", "symbols": ["__$ebnf$1"], "postprocess": function(d) {return null;}},
    {"name": "wschar", "symbols": [/[ \t\n\v\f]/], "postprocess": id},
    {"name": "top1", "symbols": ["_", "top2", "_"], "postprocess":  function (d) { let d1 = Object.assign({},d[1]); // copy this!
        d1.refNote = defaultRefNote;
        return d1; } },
    {"name": "top1$string$1", "symbols": [{"literal":"w"}, {"literal":"h"}, {"literal":"e"}, {"literal":"r"}, {"literal":"e"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "top1$ebnf$1", "symbols": ["hertz"], "postprocess": id},
    {"name": "top1$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "top1", "symbols": ["_", "top2", "__", "top1$string$1", "__", "pyNote", "_", {"literal":"="}, "_", "decimal", "top1$ebnf$1", "_"], "postprocess":  function (d) { let d1 = Object.assign({},d[1]); // copy this!
        d1.refNote = {};
        d1.refNote.intvToA4 = evalExpr(d[5], defaultRefNote).val;
        d1.refNote.hertz    = Interval(d[9]);
        return d1; } },
    {"name": "top1$string$2", "symbols": [{"literal":"w"}, {"literal":"h"}, {"literal":"e"}, {"literal":"r"}, {"literal":"e"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "top1", "symbols": ["_", "top2", "__", "top1$string$2", "__", "pyNote", "_", {"literal":"="}, "_", "eqPyNote", "_", {"literal":"\\"}, "_", "posInt", "_"], "postprocess":  function (d) { let d1 = Object.assign({},d[1]); // copy this!
        const d5 = evalExpr(d[5], defaultRefNote).val;
        const d9 = d[9](d5);
        const d13 = parseInt(d[13]);
        d1.refNote = {};
        d1.refNote.intvToA4 = d9;
        d1.refNote.hertz    = Interval(2).pow(edoPy(d13,d9),d13).mul(440);
        return d1; } },
    {"name": "top2", "symbols": ["intvSExpr"], "postprocess": d => ({type: ["interval", "symbol"], expr: d[0][0], symbolType: d[0][1]})},
    {"name": "top2", "symbols": ["intvMExpr0"], "postprocess": d => ({type: ["interval", "multiplicative"], expr: d[0]})},
    {"name": "top2", "symbols": ["intvAExpr1"], "postprocess": d => ({type: ["interval", "additive"], expr: d[0]})},
    {"name": "top2", "symbols": ["noteSExpr"], "postprocess": d => ({type: ["note", "symbol"], expr: d[0][0], symbolType: d[0][1]})},
    {"name": "top2", "symbols": ["noteMExpr1"], "postprocess": d => ({type: ["note", "multiplicative"], expr: d[0]})},
    {"name": "top2", "symbols": ["noteAExpr1"], "postprocess": d => ({type: ["note", "additive"], expr: d[0]})},
    {"name": "top2", "symbols": ["edoName"], "postprocess": d => ({type: ["EDO", "name"], expr: d[0]})},
    {"name": "edoName$ebnf$1$subexpression$1", "symbols": [{"literal":"-"}, "_"]},
    {"name": "edoName$ebnf$1", "symbols": ["edoName$ebnf$1$subexpression$1"], "postprocess": id},
    {"name": "edoName$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "edoName$subexpression$1", "symbols": [/[eE]/, /[dD]/, /[oO]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "edoName", "symbols": ["posInt", "_", "edoName$ebnf$1", "edoName$subexpression$1"], "postprocess": d => parseInt(d[0])},
    {"name": "eqPyNote", "symbols": ["pyNote"], "postprocess":  (d,loc,_) => function(ref) {
          let d0 = evalExpr(d[0], defaultRefNote).val;
          if (!ref || !ref.equals(d0)) {
            throw new ParseError("expected " + pyNote(ref), loc);
          }
          return d0;
        } },
    {"name": "intvMExpr0", "symbols": ["intvMExprIsoExpr"], "postprocess": (d,loc,_) => ["!isoExpr", d[0], loc]},
    {"name": "intvMExpr0", "symbols": ["intvMExpr1"], "postprocess": id},
    {"name": "intvMExprIsoExpr", "symbols": ["intvMExprIsoElt", "_", {"literal":":"}, "_", "intvMExprIsoElt"], "postprocess": d => [d[0], d[4]]},
    {"name": "intvMExprIsoExpr", "symbols": ["intvMExprIsoElt", "_", {"literal":":"}, "_", "intvMExprIsoExpr"], "postprocess": d => [d[0]].concat(d[4])},
    {"name": "intvMExprIsoElt", "symbols": ["intvMExpr1"], "postprocess": (d,loc,_) => [d[0], loc]},
    {"name": "intvMExprIsoElt", "symbols": [{"literal":"?"}], "postprocess": (d,loc,_) => [d[0], loc]},
    {"name": "intvMExprIsoElt", "symbols": [{"literal":"-"}], "postprocess": (d,loc,_) => [d[0], loc]},
    {"name": "intvMExpr1", "symbols": ["intvMExpr1", "_", {"literal":"*"}, "_", "intvMExpr2"], "postprocess": d => ["mul", d[0], d[4]]},
    {"name": "intvMExpr1", "symbols": ["intvMExpr1", "_", {"literal":"/"}, "_", "intvMExpr2"], "postprocess": d => ["div", d[0], d[4]]},
    {"name": "intvMExpr1", "symbols": ["noteMExpr1", "_", {"literal":"/"}, "_", "noteMExpr2"], "postprocess": d => ["div", d[0], d[4]]},
    {"name": "intvMExpr1", "symbols": ["intvMExpr2"], "postprocess": id},
    {"name": "intvMExpr2", "symbols": ["intvMExpr3", "_", {"literal":"^"}, "_", "frcExpr3"], "postprocess": d => ["pow", d[0], d[4]]},
    {"name": "intvMExpr2", "symbols": [{"literal":"("}, "_", "intvMExpr0", "_", {"literal":")"}, "_", "posIntSup"], "postprocess": d => ["pow", d[2], parseInt(d[6])]},
    {"name": "intvMExpr2$string$1", "symbols": [{"literal":"s"}, {"literal":"q"}, {"literal":"r"}, {"literal":"t"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvMExpr2", "symbols": ["intvMExpr2$string$1", "_", {"literal":"("}, "_", "intvMExpr0", "_", {"literal":")"}], "postprocess": d => ["sqrt", d[4]]},
    {"name": "intvMExpr2$string$2", "symbols": [{"literal":"r"}, {"literal":"o"}, {"literal":"o"}, {"literal":"t"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvMExpr2", "symbols": ["intvMExpr2$string$2", "posInt", "_", {"literal":"("}, "_", "intvMExpr0", "_", {"literal":")"}], "postprocess": d => ["root", d[5], parseInt(d[1])]},
    {"name": "intvMExpr2$string$3", "symbols": [{"literal":"m"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvMExpr2", "symbols": ["intvMExpr2$string$3", "_", {"literal":"("}, "_", "intvMExpr0", "_", {"literal":","}, "_", "intvMExpr0", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!med", d[4], d[8], loc]},
    {"name": "intvMExpr2", "symbols": ["nmed", "_", {"literal":"("}, "_", "intvMExpr0", "_", {"literal":","}, "_", "intvMExpr0", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!nobleMed", d[4], d[8], d[0], loc]},
    {"name": "intvMExpr2$macrocall$2", "symbols": ["intvMExpr0"]},
    {"name": "intvMExpr2$macrocall$1$string$1", "symbols": [{"literal":"r"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["intvMExpr2$macrocall$1$string$1", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":")"}], "postprocess": d => ["red", d[4][0]]},
    {"name": "intvMExpr2$macrocall$1$string$2", "symbols": [{"literal":"r"}, {"literal":"e"}, {"literal":"b"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["intvMExpr2$macrocall$1$string$2", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":")"}], "postprocess": d => ["reb", d[4][0]]},
    {"name": "intvMExpr2$macrocall$1$string$3", "symbols": [{"literal":"r"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["intvMExpr2$macrocall$1$string$3", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":","}, "_", "intvMExpr0", "_", {"literal":")"}], "postprocess": d => ["red", d[4][0], d[8]]},
    {"name": "intvMExpr2$macrocall$1$string$4", "symbols": [{"literal":"r"}, {"literal":"e"}, {"literal":"b"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["intvMExpr2$macrocall$1$string$4", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":","}, "_", "intvMExpr0", "_", {"literal":")"}], "postprocess": d => ["reb", d[4][0], d[8]]},
    {"name": "intvMExpr2$macrocall$1$string$5", "symbols": [{"literal":"a"}, {"literal":"p"}, {"literal":"p"}, {"literal":"r"}, {"literal":"o"}, {"literal":"x"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["intvMExpr2$macrocall$1$string$5", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":","}, "_", "posInt", "_", {"literal":")"}], "postprocess": d => ["!edoApprox", d[4][0], parseInt(d[8])]},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["isoUp", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!isoUp1", d[4][0], d[0], loc]},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["isoDn", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!isoDown1", d[4][0], d[0], loc]},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["isoMid", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":")"}], "postprocess": d => ["isoMid", d[4][0], Interval(1)]},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["isoUp", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":","}, "_", "intvMExpr2$macrocall$2", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!isoUp2", d[8][0], d[4][0], d[0], loc]},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["isoDn", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":","}, "_", "intvMExpr2$macrocall$2", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!isoDown2", d[8][0], d[4][0], d[0], loc]},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["isoMid", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":","}, "_", "intvMExpr2$macrocall$2", "_", {"literal":")"}], "postprocess": d => ["isoMid", d[8][0], d[4][0]]},
    {"name": "intvMExpr2$macrocall$1$string$6", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["intvMExpr2$macrocall$1$string$6", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":","}, "_", "frcExpr1", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!iso", d[4][0], Interval(1), d[8], loc]},
    {"name": "intvMExpr2$macrocall$1$string$7", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvMExpr2$macrocall$1", "symbols": ["intvMExpr2$macrocall$1$string$7", "_", {"literal":"("}, "_", "intvMExpr2$macrocall$2", "_", {"literal":","}, "_", "intvMExpr2$macrocall$2", "_", {"literal":","}, "_", "frcExpr1", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!iso", d[8][0], d[4][0], d[12], loc]},
    {"name": "intvMExpr2", "symbols": ["intvMExpr2$macrocall$1"], "postprocess": id},
    {"name": "intvMExpr2", "symbols": ["intvSymbol"], "postprocess": d => d[0][0]},
    {"name": "intvMExpr2", "symbols": ["intvMExpr3"], "postprocess": id},
    {"name": "intvMExpr3", "symbols": ["posInt"], "postprocess": d => Interval(d[0])},
    {"name": "intvMExpr3", "symbols": ["posInt", "_", "posIntSup"], "postprocess": d => Interval(Math.pow(parseInt(d[0]), parseInt(d[2])))},
    {"name": "intvMExpr3", "symbols": ["int", "_", {"literal":"\\"}, "_", "posInt"], "postprocess": d => ["!inEDO", parseInt(d[0]), parseInt(d[4])]},
    {"name": "intvMExpr3", "symbols": ["intvMEDOExpr3", "_", {"literal":"\\"}, "_", "posInt"], "postprocess": d => ["!inEDO", d[0], parseInt(d[4])]},
    {"name": "intvMExpr3", "symbols": [{"literal":"("}, "_", "intvMExpr0", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "isoUp$string$1", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}, {"literal":"u"}, {"literal":"p"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "isoUp", "symbols": ["isoUp$string$1"]},
    {"name": "isoUp$string$2", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}, {"literal":"U"}, {"literal":"p"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "isoUp", "symbols": ["isoUp$string$2"]},
    {"name": "isoDn$string$1", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}, {"literal":"d"}, {"literal":"n"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "isoDn", "symbols": ["isoDn$string$1"]},
    {"name": "isoDn$string$2", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}, {"literal":"D"}, {"literal":"n"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "isoDn", "symbols": ["isoDn$string$2"]},
    {"name": "isoDn$string$3", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}, {"literal":"D"}, {"literal":"o"}, {"literal":"w"}, {"literal":"n"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "isoDn", "symbols": ["isoDn$string$3"]},
    {"name": "isoMid$string$1", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}, {"literal":"m"}, {"literal":"i"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "isoMid", "symbols": ["isoMid$string$1"]},
    {"name": "isoMid$string$2", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}, {"literal":"M"}, {"literal":"i"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "isoMid", "symbols": ["isoMid$string$2"]},
    {"name": "nmed$string$1", "symbols": [{"literal":"n"}, {"literal":"m"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "nmed", "symbols": ["nmed$string$1"]},
    {"name": "nmed$string$2", "symbols": [{"literal":"n"}, {"literal":"M"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "nmed", "symbols": ["nmed$string$2"]},
    {"name": "nmed$string$3", "symbols": [{"literal":"n"}, {"literal":"o"}, {"literal":"b"}, {"literal":"l"}, {"literal":"e"}, {"literal":"M"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "nmed", "symbols": ["nmed$string$3"]},
    {"name": "nmed$string$4", "symbols": [{"literal":"N"}, {"literal":"o"}, {"literal":"b"}, {"literal":"l"}, {"literal":"e"}, {"literal":"M"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "nmed", "symbols": ["nmed$string$4"]},
    {"name": "noteMExpr1", "symbols": ["noteMExpr1", "_", {"literal":"*"}, "_", "intvMExpr2"], "postprocess": d => ["mul", d[0], d[4]]},
    {"name": "noteMExpr1", "symbols": ["intvMExpr1", "_", {"literal":"*"}, "_", "noteMExpr2"], "postprocess": d => ["mul", d[0], d[4]]},
    {"name": "noteMExpr1", "symbols": ["noteMExpr1", "_", {"literal":"/"}, "_", "intvMExpr2"], "postprocess": d => ["div", d[0], d[4]]},
    {"name": "noteMExpr1", "symbols": ["noteMExpr2"], "postprocess": id},
    {"name": "noteMExpr2$string$1", "symbols": [{"literal":"a"}, {"literal":"p"}, {"literal":"p"}, {"literal":"r"}, {"literal":"o"}, {"literal":"x"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "noteMExpr2", "symbols": ["noteMExpr2$string$1", "_", {"literal":"("}, "_", "noteMExpr1", "_", {"literal":","}, "_", "posInt", "_", {"literal":")"}], "postprocess": d => ["!edoApprox", d[4], parseInt(d[8])]},
    {"name": "noteMExpr2", "symbols": ["noteSymbol"], "postprocess": d => d[0][0]},
    {"name": "noteMExpr2", "symbols": ["noteMEDOExpr2", "_", {"literal":"\\"}, "_", "posInt"], "postprocess": d => ["!inEDO", d[0], parseInt(d[4])]},
    {"name": "noteMExpr2", "symbols": ["decExpr3", "hertz"], "postprocess": (d,loc,_) => ["!hertz", d[0], ["!refHertz"], loc]},
    {"name": "noteMExpr2", "symbols": [{"literal":"("}, "_", "noteMExpr1", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "intvAExpr1", "symbols": ["intvAExpr1", "_", {"literal":"+"}, "_", "intvAExpr2"], "postprocess": d => ["mul", d[0], d[4]]},
    {"name": "intvAExpr1", "symbols": ["intvAExpr1", "_", {"literal":"-"}, "_", "intvAExpr2"], "postprocess": d => ["div", d[0], d[4]]},
    {"name": "intvAExpr1", "symbols": ["noteAExpr1", "_", {"literal":"-"}, "_", "noteAExpr2"], "postprocess": d => ["div", d[0], d[4]]},
    {"name": "intvAExpr1", "symbols": ["intvAExpr2"], "postprocess": id},
    {"name": "intvAExpr2", "symbols": ["intvAExpr3", "_", {"literal":"x"}, "_", "frcExpr2"], "postprocess": d => ["pow", d[0], d[4]]},
    {"name": "intvAExpr2", "symbols": ["frcExpr2", "_", {"literal":"x"}, "_", "intvAExpr3"], "postprocess": d => ["pow", d[4], d[0]]},
    {"name": "intvAExpr2", "symbols": ["intvAExpr3"], "postprocess": id},
    {"name": "intvAExpr3$string$1", "symbols": [{"literal":"c"}, {"literal":"e"}, {"literal":"n"}, {"literal":"t"}, {"literal":"s"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvAExpr3", "symbols": ["intvAExpr3$string$1", "_", {"literal":"("}, "_", "intvMExpr0", "_", {"literal":")"}], "postprocess": d => d[4]},
    {"name": "intvAExpr3$macrocall$2", "symbols": ["intvAExpr1"]},
    {"name": "intvAExpr3$macrocall$1$string$1", "symbols": [{"literal":"r"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["intvAExpr3$macrocall$1$string$1", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":")"}], "postprocess": d => ["red", d[4][0]]},
    {"name": "intvAExpr3$macrocall$1$string$2", "symbols": [{"literal":"r"}, {"literal":"e"}, {"literal":"b"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["intvAExpr3$macrocall$1$string$2", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":")"}], "postprocess": d => ["reb", d[4][0]]},
    {"name": "intvAExpr3$macrocall$1$string$3", "symbols": [{"literal":"r"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["intvAExpr3$macrocall$1$string$3", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":","}, "_", "intvMExpr0", "_", {"literal":")"}], "postprocess": d => ["red", d[4][0], d[8]]},
    {"name": "intvAExpr3$macrocall$1$string$4", "symbols": [{"literal":"r"}, {"literal":"e"}, {"literal":"b"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["intvAExpr3$macrocall$1$string$4", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":","}, "_", "intvMExpr0", "_", {"literal":")"}], "postprocess": d => ["reb", d[4][0], d[8]]},
    {"name": "intvAExpr3$macrocall$1$string$5", "symbols": [{"literal":"a"}, {"literal":"p"}, {"literal":"p"}, {"literal":"r"}, {"literal":"o"}, {"literal":"x"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["intvAExpr3$macrocall$1$string$5", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":","}, "_", "posInt", "_", {"literal":")"}], "postprocess": d => ["!edoApprox", d[4][0], parseInt(d[8])]},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["isoUp", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!isoUp1", d[4][0], d[0], loc]},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["isoDn", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!isoDown1", d[4][0], d[0], loc]},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["isoMid", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":")"}], "postprocess": d => ["isoMid", d[4][0], Interval(1)]},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["isoUp", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":","}, "_", "intvAExpr3$macrocall$2", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!isoUp2", d[8][0], d[4][0], d[0], loc]},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["isoDn", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":","}, "_", "intvAExpr3$macrocall$2", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!isoDown2", d[8][0], d[4][0], d[0], loc]},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["isoMid", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":","}, "_", "intvAExpr3$macrocall$2", "_", {"literal":")"}], "postprocess": d => ["isoMid", d[8][0], d[4][0]]},
    {"name": "intvAExpr3$macrocall$1$string$6", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["intvAExpr3$macrocall$1$string$6", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":","}, "_", "frcExpr1", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!iso", d[4][0], Interval(1), d[8], loc]},
    {"name": "intvAExpr3$macrocall$1$string$7", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvAExpr3$macrocall$1", "symbols": ["intvAExpr3$macrocall$1$string$7", "_", {"literal":"("}, "_", "intvAExpr3$macrocall$2", "_", {"literal":","}, "_", "intvAExpr3$macrocall$2", "_", {"literal":","}, "_", "frcExpr1", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!iso", d[8][0], d[4][0], d[12], loc]},
    {"name": "intvAExpr3", "symbols": ["intvAExpr3$macrocall$1"], "postprocess": id},
    {"name": "intvAExpr3", "symbols": ["intvSymbol"], "postprocess": d => d[0][0]},
    {"name": "intvAExpr3", "symbols": ["intvAExpr4"], "postprocess": id},
    {"name": "intvAExpr4", "symbols": ["decExpr3", {"literal":"c"}], "postprocess": d => ["!cents", d[0]]},
    {"name": "intvAExpr4", "symbols": ["intvAEDOExpr3", "_", {"literal":"\\"}, "_", "posInt"], "postprocess": d => ["!inEDO", d[0], parseInt(d[4])]},
    {"name": "intvAExpr4", "symbols": [{"literal":"("}, "_", "intvAExpr1", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "noteAExpr1", "symbols": ["noteAExpr1", "_", {"literal":"+"}, "_", "intvAExpr2"], "postprocess": d => ["mul", d[0], d[4]]},
    {"name": "noteAExpr1", "symbols": ["intvAExpr1", "_", {"literal":"+"}, "_", "noteAExpr2"], "postprocess": d => ["mul", d[0], d[4]]},
    {"name": "noteAExpr1", "symbols": ["noteAExpr1", "_", {"literal":"-"}, "_", "intvAExpr2"], "postprocess": d => ["div", d[0], d[4]]},
    {"name": "noteAExpr1", "symbols": ["noteAExpr2"], "postprocess": id},
    {"name": "noteAExpr2$string$1", "symbols": [{"literal":"a"}, {"literal":"p"}, {"literal":"p"}, {"literal":"r"}, {"literal":"o"}, {"literal":"x"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "noteAExpr2", "symbols": ["noteAExpr2$string$1", "_", {"literal":"("}, "_", "noteAExpr1", "_", {"literal":","}, "_", "posInt", "_", {"literal":")"}], "postprocess": d => ["!edoApprox", d[4], parseInt(d[8])]},
    {"name": "noteAExpr2", "symbols": ["noteSymbol"], "postprocess": d => d[0][0]},
    {"name": "noteAExpr2", "symbols": ["noteAEDOExpr2", "_", {"literal":"\\"}, "_", "posInt"], "postprocess": d => ["!inEDO", d[0], parseInt(d[4])]},
    {"name": "noteAExpr2", "symbols": [{"literal":"("}, "_", "noteAExpr1", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "intvMEDOExpr1", "symbols": ["intvMEDOExpr1", "_", {"literal":"*"}, "_", "intvMEDOExpr2"], "postprocess": d => ["+", d[0], d[4]]},
    {"name": "intvMEDOExpr1", "symbols": ["intvMEDOExpr1", "_", {"literal":"/"}, "_", "intvMEDOExpr2"], "postprocess": d => ["-", d[0], d[4]]},
    {"name": "intvMEDOExpr1", "symbols": ["noteMEDOExpr1", "_", {"literal":"/"}, "_", "noteMEDOExpr2"], "postprocess": d => ["-", d[0], d[4]]},
    {"name": "intvMEDOExpr1", "symbols": ["intvMEDOExpr2"], "postprocess": id},
    {"name": "intvMEDOExpr2", "symbols": ["intvMEDOExpr3", "_", {"literal":"^"}, "_", "intExpr1"], "postprocess": d => ["*", d[0], d[4]]},
    {"name": "intvMEDOExpr2", "symbols": [{"literal":"("}, "_", "intvMEDOExpr1", "_", {"literal":")"}, "_", "posIntSup"], "postprocess": d => ["*", d[2], parseInt(d[6])]},
    {"name": "intvMEDOExpr2", "symbols": ["intvMEDOExpr3"], "postprocess": id},
    {"name": "intvMEDOExpr3", "symbols": ["upsDnsIntv"], "postprocess": id},
    {"name": "intvMEDOExpr3$string$1", "symbols": [{"literal":"T"}, {"literal":"T"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvMEDOExpr3", "symbols": ["intvMEDOExpr3$string$1"], "postprocess": (d,loc,_) => ["!edoTT", loc]},
    {"name": "intvMEDOExpr3", "symbols": [{"literal":"("}, "_", "intvMEDOExpr1", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "noteMEDOExpr1", "symbols": ["noteMEDOExpr1", "_", {"literal":"*"}, "_", "intvMEDOExpr2"], "postprocess": d => ["+", d[0], d[4]]},
    {"name": "noteMEDOExpr1", "symbols": ["intvMEDOExpr1", "_", {"literal":"*"}, "_", "noteMEDOExpr2"], "postprocess": d => ["+", d[0], d[4]]},
    {"name": "noteMEDOExpr1", "symbols": ["noteMEDOExpr1", "_", {"literal":"/"}, "_", "intvMEDOExpr2"], "postprocess": d => ["-", d[0], d[4]]},
    {"name": "noteMEDOExpr1", "symbols": ["noteMEDOExpr2"], "postprocess": id},
    {"name": "noteMEDOExpr2", "symbols": ["upsDnsNote"], "postprocess": id},
    {"name": "noteMEDOExpr2", "symbols": [{"literal":"("}, "_", "noteMEDOExpr1", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "intvAEDOExpr1", "symbols": ["intvAEDOExpr1", "_", {"literal":"+"}, "_", "intvAEDOExpr2"], "postprocess": d => ["+", d[0], d[4]]},
    {"name": "intvAEDOExpr1", "symbols": ["intvAEDOExpr1", "_", {"literal":"-"}, "_", "intvAEDOExpr2"], "postprocess": d => ["-", d[0], d[4]]},
    {"name": "intvAEDOExpr1", "symbols": ["noteAEDOExpr1", "_", {"literal":"-"}, "_", "noteAEDOExpr2"], "postprocess": d => ["-", d[0], d[4]]},
    {"name": "intvAEDOExpr1", "symbols": ["intvAEDOExpr2"], "postprocess": id},
    {"name": "intvAEDOExpr2", "symbols": ["intvAEDOExpr3", "_", {"literal":"x"}, "_", "intExpr1"], "postprocess": d => ["*", d[0], d[4]]},
    {"name": "intvAEDOExpr2", "symbols": ["intExpr1", "_", {"literal":"x"}, "_", "intvAEDOExpr3"], "postprocess": d => ["*", d[0], d[4]]},
    {"name": "intvAEDOExpr2", "symbols": ["intvAEDOExpr3"], "postprocess": id},
    {"name": "intvAEDOExpr3", "symbols": [{"literal":"-"}, "_", "intvAEDOExpr4"], "postprocess": d => ["-", 0, d[2]]},
    {"name": "intvAEDOExpr3", "symbols": ["intvAEDOExpr4"], "postprocess": id},
    {"name": "intvAEDOExpr4", "symbols": ["nonNegInt"], "postprocess": d => parseInt(d[0])},
    {"name": "intvAEDOExpr4", "symbols": ["upsDnsIntv"], "postprocess": id},
    {"name": "intvAEDOExpr4$string$1", "symbols": [{"literal":"T"}, {"literal":"T"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvAEDOExpr4", "symbols": ["intvAEDOExpr4$string$1"], "postprocess": d => ["!edoTT"]},
    {"name": "intvAEDOExpr4", "symbols": [{"literal":"("}, "_", "intvAEDOExpr1", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "noteAEDOExpr1", "symbols": ["noteAEDOExpr1", "_", {"literal":"+"}, "_", "intvAEDOExpr2"], "postprocess": d => ["+", d[0], d[4]]},
    {"name": "noteAEDOExpr1", "symbols": ["intvAEDOExpr1", "_", {"literal":"+"}, "_", "noteAEDOExpr2"], "postprocess": d => ["+", d[0], d[4]]},
    {"name": "noteAEDOExpr1", "symbols": ["noteAEDOExpr1", "_", {"literal":"-"}, "_", "intvAEDOExpr2"], "postprocess": d => ["-", d[0], d[4]]},
    {"name": "noteAEDOExpr1", "symbols": ["noteAEDOExpr2"], "postprocess": id},
    {"name": "noteAEDOExpr2", "symbols": ["upsDnsNote"], "postprocess": id},
    {"name": "noteAEDOExpr2", "symbols": [{"literal":"("}, "_", "noteAEDOExpr1", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "intvSExpr$macrocall$2", "symbols": ["intvSExpr0"]},
    {"name": "intvSExpr$macrocall$1$string$1", "symbols": [{"literal":"r"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvSExpr$macrocall$1", "symbols": ["intvSExpr$macrocall$1$string$1", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":")"}], "postprocess": d => ["red", d[4][0]]},
    {"name": "intvSExpr$macrocall$1$string$2", "symbols": [{"literal":"r"}, {"literal":"e"}, {"literal":"b"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvSExpr$macrocall$1", "symbols": ["intvSExpr$macrocall$1$string$2", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":")"}], "postprocess": d => ["reb", d[4][0]]},
    {"name": "intvSExpr$macrocall$1$string$3", "symbols": [{"literal":"r"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvSExpr$macrocall$1", "symbols": ["intvSExpr$macrocall$1$string$3", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":","}, "_", "intvMExpr0", "_", {"literal":")"}], "postprocess": d => ["red", d[4][0], d[8]]},
    {"name": "intvSExpr$macrocall$1$string$4", "symbols": [{"literal":"r"}, {"literal":"e"}, {"literal":"b"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvSExpr$macrocall$1", "symbols": ["intvSExpr$macrocall$1$string$4", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":","}, "_", "intvMExpr0", "_", {"literal":")"}], "postprocess": d => ["reb", d[4][0], d[8]]},
    {"name": "intvSExpr$macrocall$1$string$5", "symbols": [{"literal":"a"}, {"literal":"p"}, {"literal":"p"}, {"literal":"r"}, {"literal":"o"}, {"literal":"x"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvSExpr$macrocall$1", "symbols": ["intvSExpr$macrocall$1$string$5", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":","}, "_", "posInt", "_", {"literal":")"}], "postprocess": d => ["!edoApprox", d[4][0], parseInt(d[8])]},
    {"name": "intvSExpr$macrocall$1", "symbols": ["isoUp", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!isoUp1", d[4][0], d[0], loc]},
    {"name": "intvSExpr$macrocall$1", "symbols": ["isoDn", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!isoDown1", d[4][0], d[0], loc]},
    {"name": "intvSExpr$macrocall$1", "symbols": ["isoMid", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":")"}], "postprocess": d => ["isoMid", d[4][0], Interval(1)]},
    {"name": "intvSExpr$macrocall$1", "symbols": ["isoUp", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":","}, "_", "intvSExpr$macrocall$2", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!isoUp2", d[8][0], d[4][0], d[0], loc]},
    {"name": "intvSExpr$macrocall$1", "symbols": ["isoDn", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":","}, "_", "intvSExpr$macrocall$2", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!isoDown2", d[8][0], d[4][0], d[0], loc]},
    {"name": "intvSExpr$macrocall$1", "symbols": ["isoMid", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":","}, "_", "intvSExpr$macrocall$2", "_", {"literal":")"}], "postprocess": d => ["isoMid", d[8][0], d[4][0]]},
    {"name": "intvSExpr$macrocall$1$string$6", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvSExpr$macrocall$1", "symbols": ["intvSExpr$macrocall$1$string$6", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":","}, "_", "frcExpr1", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!iso", d[4][0], Interval(1), d[8], loc]},
    {"name": "intvSExpr$macrocall$1$string$7", "symbols": [{"literal":"i"}, {"literal":"s"}, {"literal":"o"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvSExpr$macrocall$1", "symbols": ["intvSExpr$macrocall$1$string$7", "_", {"literal":"("}, "_", "intvSExpr$macrocall$2", "_", {"literal":","}, "_", "intvSExpr$macrocall$2", "_", {"literal":","}, "_", "frcExpr1", "_", {"literal":")"}], "postprocess": (d,loc,_) => ["!iso", d[8][0], d[4][0], d[12], loc]},
    {"name": "intvSExpr", "symbols": ["intvSExpr$macrocall$1"], "postprocess": d => [d[0], "function call"]},
    {"name": "intvSExpr", "symbols": ["intvSymbol"], "postprocess": id},
    {"name": "intvSExpr", "symbols": ["intvEDOSymb"], "postprocess": id},
    {"name": "intvSExpr", "symbols": ["posInt", "_", {"literal":"/"}, "_", "posInt"], "postprocess": d => [Interval(d[0],d[4]), "ratio"]},
    {"name": "intvSExpr", "symbols": ["decExpr3", {"literal":"c"}], "postprocess": d => [["!cents", d[0]], "cents"]},
    {"name": "intvSExpr", "symbols": [{"literal":"("}, "_", "intvSExpr", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "intvSExpr0", "symbols": ["intvSExpr"], "postprocess": d => d[0][0]},
    {"name": "intvEDOSymb", "symbols": ["int", "_", {"literal":"\\"}, "_", "posInt"], "postprocess": d => [["!inEDO", parseInt(d[0]), parseInt(d[4])], "EDO step"]},
    {"name": "intvEDOSymb", "symbols": ["upsDnsIntvAbD", "_", {"literal":"\\"}, "_", "posInt"], "postprocess": d => [["!inEDO", d[0], parseInt(d[4])], "ups-and-downs"]},
    {"name": "intvEDOSymb", "symbols": ["upsDnsIntvVbD", "_", {"literal":"\\"}, "_", "posInt"], "postprocess": d => [["!inEDO", d[0], parseInt(d[4])], "ups-and-downs (verbose)"]},
    {"name": "intvEDOSymb$string$1", "symbols": [{"literal":"T"}, {"literal":"T"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvEDOSymb", "symbols": ["intvEDOSymb$string$1", "_", {"literal":"\\"}, "_", "posInt"], "postprocess": d => [["!inEDO", ["!edoTT"], parseInt(d[4])], "EDO TT"]},
    {"name": "noteSExpr$string$1", "symbols": [{"literal":"a"}, {"literal":"p"}, {"literal":"p"}, {"literal":"r"}, {"literal":"o"}, {"literal":"x"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "noteSExpr", "symbols": ["noteSExpr$string$1", "_", {"literal":"("}, "_", "noteSExpr", "_", {"literal":","}, "_", "posInt", "_", {"literal":")"}], "postprocess": d => [["!edoApprox", d[4][0], parseInt(d[8])], "function call"]},
    {"name": "noteSExpr", "symbols": ["noteSymbol"], "postprocess": id},
    {"name": "noteSExpr", "symbols": ["upsDnsNote", "_", {"literal":"\\"}, "_", "posInt"], "postprocess": d => [["!inEDO", d[0], parseInt(d[4])], "ups-and-downs"]},
    {"name": "noteSExpr", "symbols": ["decExpr3", "hertz"], "postprocess": (d,loc,_) => [["!hertz", d[0], ["!refHertz"], loc], "hertz"]},
    {"name": "noteSExpr", "symbols": [{"literal":"("}, "_", "noteSExpr", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "intvSymbol", "symbols": ["pyIntvD"], "postprocess": d => [d[0], "Pythagorean"]},
    {"name": "intvSymbol", "symbols": ["npyIntvD"], "postprocess": d => [d[0], "neutral Pythagorean"]},
    {"name": "intvSymbol", "symbols": ["snpyIntvD"], "postprocess": d => [d[0], "semi-neutral Pythagorean"]},
    {"name": "intvSymbol", "symbols": ["pyIntvVbD"], "postprocess": d => [d[0], "Pythagorean (verbose)"]},
    {"name": "intvSymbol", "symbols": ["npyIntvVbD"], "postprocess": d => [d[0], "neutral Pythagorean (verbose)"]},
    {"name": "intvSymbol", "symbols": ["snpyIntvVbD"], "postprocess": d => [d[0], "semi-neutral Pythagorean (verbose)"]},
    {"name": "intvSymbol", "symbols": ["strictFJSLikeIntv"], "postprocess": d => [d[0], "FJS-like"]},
    {"name": "intvSymbol$string$1", "symbols": [{"literal":"F"}, {"literal":"J"}, {"literal":"S"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvSymbol", "symbols": ["intvSymbol$string$1", "_", {"literal":"("}, "_", "fjsIntv", "_", {"literal":")"}], "postprocess": d => [d[4], "NFJS"]},
    {"name": "intvSymbol$string$2", "symbols": [{"literal":"N"}, {"literal":"F"}, {"literal":"J"}, {"literal":"S"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvSymbol", "symbols": ["intvSymbol$string$2", "_", {"literal":"("}, "_", "nfjsIntv", "_", {"literal":")"}], "postprocess": d => [d[4], "FJS"]},
    {"name": "intvSymbol", "symbols": ["aclrIntv"], "postprocess": d => [d[0], "color"]},
    {"name": "intvSymbol", "symbols": ["clrIntv"], "postprocess": d => [d[0], "color (verbose)"]},
    {"name": "intvSymbol", "symbols": ["monzo"], "postprocess": d => [d[0], "monzo"]},
    {"name": "intvSymbol$string$3", "symbols": [{"literal":"T"}, {"literal":"T"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "intvSymbol", "symbols": ["intvSymbol$string$3"], "postprocess": _ => [Interval(2).sqrt(), "TT"]},
    {"name": "intvSymbol", "symbols": ["phi"], "postprocess": _ => [Interval.phi, "phi"]},
    {"name": "phi$string$1", "symbols": [{"literal":"p"}, {"literal":"h"}, {"literal":"i"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "phi", "symbols": ["phi$string$1"]},
    {"name": "phi", "symbols": [{"literal":"φ"}]},
    {"name": "phi", "symbols": [{"literal":"ϕ"}]},
    {"name": "noteSymbol", "symbols": ["pyNote"], "postprocess": d => [d[0], "Pythagorean"]},
    {"name": "noteSymbol", "symbols": ["npyNote"], "postprocess": d => [d[0], "neutral Pythagorean"]},
    {"name": "noteSymbol", "symbols": ["strictFJSLikeNote"], "postprocess": d => [d[0], "FJS-like"]},
    {"name": "noteSymbol$string$1", "symbols": [{"literal":"F"}, {"literal":"J"}, {"literal":"S"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "noteSymbol", "symbols": ["noteSymbol$string$1", "_", {"literal":"("}, "_", "fjsNote", "_", {"literal":")"}], "postprocess": d => [d[4], "NFJS"]},
    {"name": "noteSymbol$string$2", "symbols": [{"literal":"N"}, {"literal":"F"}, {"literal":"J"}, {"literal":"S"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "noteSymbol", "symbols": ["noteSymbol$string$2", "_", {"literal":"("}, "_", "nfjsNote", "_", {"literal":")"}], "postprocess": d => [d[4], "FJS"]},
    {"name": "noteSymbol", "symbols": ["aclrNote"], "postprocess": d => [d[0], "color"]},
    {"name": "noteSymbol", "symbols": ["clrNote"], "postprocess": d => [d[0], "color (verbose)"]},
    {"name": "monzo", "symbols": [/[\[\|]/, "_", "monzoElts", /[\]>⟩]/], "postprocess": d => Interval(d[2])},
    {"name": "monzoElts", "symbols": [], "postprocess": d => []},
    {"name": "monzoElts", "symbols": ["frcExpr2"], "postprocess": d => [d[0]]},
    {"name": "monzoElts", "symbols": ["frcExpr2", "_", {"literal":","}, "_", "monzoElts"], "postprocess": d => [d[0]].concat(d[4])},
    {"name": "monzoElts", "symbols": ["frcExpr2", "__", "monzoElts"], "postprocess": d => [d[0]].concat(d[2])},
    {"name": "anyPyIntv", "symbols": ["pyIntvD"], "postprocess": id},
    {"name": "anyPyIntv", "symbols": ["npyIntvD"], "postprocess": id},
    {"name": "anyPyIntv", "symbols": ["snpyIntvD"], "postprocess": id},
    {"name": "anyPyIntv", "symbols": ["pyIntvVbD"], "postprocess": id},
    {"name": "anyPyIntv", "symbols": ["npyIntvVbD"], "postprocess": id},
    {"name": "anyPyIntv", "symbols": ["snpyIntvVbD"], "postprocess": id},
    {"name": "pyIntvD", "symbols": ["pyIntv"], "postprocess": id},
    {"name": "pyIntvD", "symbols": ["desc", "pyIntv"], "postprocess": d => ["recip", d[1]]},
    {"name": "npyIntvD", "symbols": ["npyIntv"], "postprocess": id},
    {"name": "npyIntvD", "symbols": ["desc", "npyIntv"], "postprocess": d => ["recip", d[1]]},
    {"name": "snpyIntvD", "symbols": ["snpyIntv"], "postprocess": id},
    {"name": "snpyIntvD", "symbols": ["desc", "snpyIntv"], "postprocess": d => ["recip", d[1]]},
    {"name": "pyIntv", "symbols": [{"literal":"P"}, "degV0"], "postprocess": (d,loc,_) => ["!perfPyIntv", d[1], loc]},
    {"name": "pyIntv", "symbols": [{"literal":"M"}, "degV0"], "postprocess": (d,loc,_) => ["!nonPerfPyIntv", d[1], Fraction(1,2), "M", loc]},
    {"name": "pyIntv", "symbols": [{"literal":"m"}, "degV0"], "postprocess": (d,loc,_) => ["!nonPerfPyIntv", d[1], Fraction(-1,2), "m", loc]},
    {"name": "pyIntv$ebnf$1", "symbols": [{"literal":"A"}]},
    {"name": "pyIntv$ebnf$1", "symbols": ["pyIntv$ebnf$1", {"literal":"A"}], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "pyIntv", "symbols": ["pyIntv$ebnf$1", "degV0"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[1], d[0].length, 1, loc]},
    {"name": "pyIntv$ebnf$2", "symbols": [{"literal":"d"}]},
    {"name": "pyIntv$ebnf$2", "symbols": ["pyIntv$ebnf$2", {"literal":"d"}], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "pyIntv", "symbols": ["pyIntv$ebnf$2", "degV0"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[1], -d[0].length, 1, loc]},
    {"name": "pyIntv", "symbols": ["posInt", {"literal":"A"}, "degV0"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[2], parseInt(d[0]), 1, loc]},
    {"name": "pyIntv", "symbols": ["posInt", {"literal":"d"}, "degV0"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[2], -parseInt(d[0]), 1, loc]},
    {"name": "npyIntv$subexpression$1", "symbols": [/[nN]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "npyIntv", "symbols": ["npyIntv$subexpression$1", "degV0"], "postprocess": (d,loc,_) => ["!nonPerfPyIntv", d[1], 0, "n", loc]},
    {"name": "npyIntv$string$1", "symbols": [{"literal":"s"}, {"literal":"A"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "npyIntv", "symbols": ["npyIntv$string$1", "degV0"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[1], 1, 2, loc]},
    {"name": "npyIntv$string$2", "symbols": [{"literal":"s"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "npyIntv", "symbols": ["npyIntv$string$2", "degV0"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[1], -1, 2, loc]},
    {"name": "npyIntv$string$3", "symbols": [{"literal":"/"}, {"literal":"2"}, {"literal":"-"}, {"literal":"A"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "npyIntv", "symbols": ["posInt", "npyIntv$string$3", "degV0"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[2], parseInt(d[0]), 2, loc]},
    {"name": "npyIntv$string$4", "symbols": [{"literal":"/"}, {"literal":"2"}, {"literal":"-"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "npyIntv", "symbols": ["posInt", "npyIntv$string$4", "degV0"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[2], -parseInt(d[0]), 2, loc]},
    {"name": "snpyIntv$string$1", "symbols": [{"literal":"s"}, {"literal":"M"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "snpyIntv", "symbols": ["snpyIntv$string$1", "degV0"], "postprocess": (d,loc,_) => ["!nonPerfPyIntv", d[1], Fraction(1,4), "sM", loc]},
    {"name": "snpyIntv$string$2", "symbols": [{"literal":"s"}, {"literal":"m"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "snpyIntv", "symbols": ["snpyIntv$string$2", "degV0"], "postprocess": (d,loc,_) => ["!nonPerfPyIntv", d[1], Fraction(-1,4), "sm", loc]},
    {"name": "snpyIntv$string$3", "symbols": [{"literal":"/"}, {"literal":"4"}, {"literal":"-"}, {"literal":"A"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "snpyIntv", "symbols": ["posInt", "snpyIntv$string$3", "degV0"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[2], parseInt(d[0]), 4, loc]},
    {"name": "snpyIntv$string$4", "symbols": [{"literal":"/"}, {"literal":"4"}, {"literal":"-"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "snpyIntv", "symbols": ["posInt", "snpyIntv$string$4", "degV0"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[2], -parseInt(d[0]), 4, loc]},
    {"name": "pyIntvVbD", "symbols": ["pyIntvVb"], "postprocess": id},
    {"name": "pyIntvVbD", "symbols": ["desc", "pyIntvVb"], "postprocess": d => ["recip", d[1]]},
    {"name": "npyIntvVbD", "symbols": ["npyIntvVb"], "postprocess": id},
    {"name": "npyIntvVbD", "symbols": ["desc", "npyIntvVb"], "postprocess": d => ["recip", d[1]]},
    {"name": "snpyIntvVbD", "symbols": ["snpyIntvVb"], "postprocess": id},
    {"name": "snpyIntvVbD", "symbols": ["desc", "snpyIntvVb"], "postprocess": d => ["recip", d[1]]},
    {"name": "pyIntvVb", "symbols": ["pyPrf", "degV1"], "postprocess": (d,loc,_) => ["!perfPyIntv", d[1], loc]},
    {"name": "pyIntvVb", "symbols": ["pyMaj", "degV1"], "postprocess": (d,loc,_) => ["!nonPerfPyIntv", d[1], Fraction(1,2), "M", loc]},
    {"name": "pyIntvVb", "symbols": ["pyMin", "degV1"], "postprocess": (d,loc,_) => ["!nonPerfPyIntv", d[1], Fraction(-1,2), "m", loc]},
    {"name": "pyIntvVb", "symbols": ["pyAug", "degV1"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[1], 1, 1, loc]},
    {"name": "pyIntvVb", "symbols": ["pyDim", "degV1"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[1], -1, 1, loc]},
    {"name": "pyIntvVb", "symbols": ["posInt", {"literal":"-"}, "pyAug", "degV1"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[3], parseInt(d[0]), 1, loc]},
    {"name": "pyIntvVb", "symbols": ["posInt", {"literal":"-"}, "pyDim", "degV1"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[3], -parseInt(d[0]), 1, loc]},
    {"name": "npyIntvVb", "symbols": ["pyNeut", "degV1"], "postprocess": (d,loc,_) => ["!nonPerfPyIntv", d[1], 0, "n", loc]},
    {"name": "npyIntvVb", "symbols": ["pySemi", "pyAug", "degV1"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[2], 1, 2, loc]},
    {"name": "npyIntvVb", "symbols": ["pySemi", "pyDim", "degV1"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[2], -1, 2, loc]},
    {"name": "npyIntvVb$string$1", "symbols": [{"literal":"/"}, {"literal":"2"}, {"literal":"-"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "npyIntvVb", "symbols": ["posInt", "npyIntvVb$string$1", "pyAug", "degV1"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[3], parseInt(d[0]), 2, loc]},
    {"name": "npyIntvVb$string$2", "symbols": [{"literal":"/"}, {"literal":"2"}, {"literal":"-"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "npyIntvVb", "symbols": ["posInt", "npyIntvVb$string$2", "pyDim", "degV1"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[3], -parseInt(d[0]), 2, loc]},
    {"name": "snpyIntvVb", "symbols": ["pySemi", "pyMaj", "degV1"], "postprocess": (d,loc,_) => ["!nonPerfPyIntv", d[2], Fraction(1,4), "sM", loc]},
    {"name": "snpyIntvVb", "symbols": ["pySemi", "pyMin", "degV1"], "postprocess": (d,loc,_) => ["!nonPerfPyIntv", d[2], Fraction(-1,4), "sm", loc]},
    {"name": "snpyIntvVb$string$1", "symbols": [{"literal":"/"}, {"literal":"4"}, {"literal":"-"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "snpyIntvVb", "symbols": ["posInt", "snpyIntvVb$string$1", "pyAug", "degV1"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[2], parseInt(d[0]), 4, loc]},
    {"name": "snpyIntvVb$string$2", "symbols": [{"literal":"/"}, {"literal":"4"}, {"literal":"-"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "snpyIntvVb", "symbols": ["posInt", "snpyIntvVb$string$2", "pyDim", "degV1"], "postprocess": (d,loc,_) => ["!augOrDimPyIntv", d[2], -parseInt(d[0]), 4, loc]},
    {"name": "pyPrf$subexpression$1", "symbols": [/[pP]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "pyPrf$string$1", "symbols": [{"literal":"e"}, {"literal":"r"}, {"literal":"f"}, {"literal":"e"}, {"literal":"c"}, {"literal":"t"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyPrf", "symbols": ["pyPrf$subexpression$1", "pyPrf$string$1"]},
    {"name": "pyMaj$subexpression$1", "symbols": [/[mM]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "pyMaj$string$1", "symbols": [{"literal":"a"}, {"literal":"j"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyMaj$ebnf$1$string$1", "symbols": [{"literal":"o"}, {"literal":"r"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyMaj$ebnf$1", "symbols": ["pyMaj$ebnf$1$string$1"], "postprocess": id},
    {"name": "pyMaj$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "pyMaj", "symbols": ["pyMaj$subexpression$1", "pyMaj$string$1", "pyMaj$ebnf$1"]},
    {"name": "pyMin$subexpression$1", "symbols": [/[mM]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "pyMin$string$1", "symbols": [{"literal":"i"}, {"literal":"n"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyMin$ebnf$1$string$1", "symbols": [{"literal":"o"}, {"literal":"r"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyMin$ebnf$1", "symbols": ["pyMin$ebnf$1$string$1"], "postprocess": id},
    {"name": "pyMin$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "pyMin", "symbols": ["pyMin$subexpression$1", "pyMin$string$1", "pyMin$ebnf$1"]},
    {"name": "pyAug$subexpression$1", "symbols": [/[aA]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "pyAug$string$1", "symbols": [{"literal":"u"}, {"literal":"g"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyAug$ebnf$1$string$1", "symbols": [{"literal":"m"}, {"literal":"e"}, {"literal":"n"}, {"literal":"t"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyAug$ebnf$1", "symbols": ["pyAug$ebnf$1$string$1"], "postprocess": id},
    {"name": "pyAug$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "pyAug", "symbols": ["pyAug$subexpression$1", "pyAug$string$1", "pyAug$ebnf$1"]},
    {"name": "pyDim$subexpression$1", "symbols": [/[dD]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "pyDim$string$1", "symbols": [{"literal":"i"}, {"literal":"m"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyDim$ebnf$1$string$1", "symbols": [{"literal":"i"}, {"literal":"n"}, {"literal":"i"}, {"literal":"s"}, {"literal":"h"}, {"literal":"e"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyDim$ebnf$1", "symbols": ["pyDim$ebnf$1$string$1"], "postprocess": id},
    {"name": "pyDim$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "pyDim", "symbols": ["pyDim$subexpression$1", "pyDim$string$1", "pyDim$ebnf$1"]},
    {"name": "pyNeut$subexpression$1", "symbols": [/[nN]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "pyNeut$string$1", "symbols": [{"literal":"e"}, {"literal":"u"}, {"literal":"t"}, {"literal":"r"}, {"literal":"a"}, {"literal":"l"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyNeut", "symbols": ["pyNeut$subexpression$1", "pyNeut$string$1"]},
    {"name": "pySemi$subexpression$1", "symbols": [/[sS]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "pySemi$string$1", "symbols": [{"literal":"e"}, {"literal":"m"}, {"literal":"i"}, {"literal":"-"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pySemi", "symbols": ["pySemi$subexpression$1", "pySemi$string$1"]},
    {"name": "anyPyNote", "symbols": ["pyNote"], "postprocess": id},
    {"name": "anyPyNote", "symbols": ["npyNote"], "postprocess": id},
    {"name": "pyNote", "symbols": [{"literal":"A"}], "postprocess": _ => ["recip", ["!refIntvToA4"]]},
    {"name": "pyNote$macrocall$2", "symbols": [/[B-G]/]},
    {"name": "pyNote$macrocall$3", "symbols": ["pyNoteNoAccs"]},
    {"name": "pyNote$macrocall$1$ebnf$1", "symbols": ["int"], "postprocess": id},
    {"name": "pyNote$macrocall$1$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "pyNote$macrocall$1", "symbols": ["pyNote$macrocall$2", "pyNote$macrocall$3", "pyNote$macrocall$1$ebnf$1"], "postprocess":  function(d) {
        const d2 = d[2] ? parseInt(d[2]) : 4;
        return ["mul", ["div", baseNoteIntvToA(d[0][0]), ["!refIntvToA4"]]
                     , d[1][0].mul(Interval(2).pow(d2 - 4))]; } },
    {"name": "pyNote", "symbols": ["pyNote$macrocall$1"], "postprocess": id},
    {"name": "pyNote$macrocall$5", "symbols": [/[A-G]/]},
    {"name": "pyNote$macrocall$6", "symbols": ["pyNoteAccs"]},
    {"name": "pyNote$macrocall$4$ebnf$1", "symbols": ["int"], "postprocess": id},
    {"name": "pyNote$macrocall$4$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "pyNote$macrocall$4", "symbols": ["pyNote$macrocall$5", "pyNote$macrocall$6", "pyNote$macrocall$4$ebnf$1"], "postprocess":  function(d) {
        const d2 = d[2] ? parseInt(d[2]) : 4;
        return ["mul", ["div", baseNoteIntvToA(d[0][0]), ["!refIntvToA4"]]
                     , d[1][0].mul(Interval(2).pow(d2 - 4))]; } },
    {"name": "pyNote", "symbols": ["pyNote$macrocall$4"], "postprocess": id},
    {"name": "pyNoteNoAccs", "symbols": [], "postprocess": _ => Interval(1)},
    {"name": "pyNoteAccs$subexpression$1", "symbols": [{"literal":"♮"}]},
    {"name": "pyNoteAccs$subexpression$1$string$1", "symbols": [{"literal":"n"}, {"literal":"a"}, {"literal":"t"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyNoteAccs$subexpression$1", "symbols": ["pyNoteAccs$subexpression$1$string$1"]},
    {"name": "pyNoteAccs", "symbols": ["pyNoteAccs$subexpression$1"], "postprocess": _ => Interval(1)},
    {"name": "pyNoteAccs$ebnf$1$subexpression$1", "symbols": [{"literal":"♯"}]},
    {"name": "pyNoteAccs$ebnf$1$subexpression$1", "symbols": [{"literal":"#"}]},
    {"name": "pyNoteAccs$ebnf$1", "symbols": ["pyNoteAccs$ebnf$1$subexpression$1"]},
    {"name": "pyNoteAccs$ebnf$1$subexpression$2", "symbols": [{"literal":"♯"}]},
    {"name": "pyNoteAccs$ebnf$1$subexpression$2", "symbols": [{"literal":"#"}]},
    {"name": "pyNoteAccs$ebnf$1", "symbols": ["pyNoteAccs$ebnf$1", "pyNoteAccs$ebnf$1$subexpression$2"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "pyNoteAccs", "symbols": ["pyNoteAccs$ebnf$1"], "postprocess": d => pyInterval(1, d[0].length)},
    {"name": "pyNoteAccs$ebnf$2$subexpression$1$string$1", "symbols": [{"literal":"\ud834"}, {"literal":"\udd2a"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyNoteAccs$ebnf$2$subexpression$1", "symbols": ["pyNoteAccs$ebnf$2$subexpression$1$string$1"]},
    {"name": "pyNoteAccs$ebnf$2$subexpression$1", "symbols": [{"literal":"X"}]},
    {"name": "pyNoteAccs$ebnf$2", "symbols": ["pyNoteAccs$ebnf$2$subexpression$1"]},
    {"name": "pyNoteAccs$ebnf$2$subexpression$2$string$1", "symbols": [{"literal":"\ud834"}, {"literal":"\udd2a"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyNoteAccs$ebnf$2$subexpression$2", "symbols": ["pyNoteAccs$ebnf$2$subexpression$2$string$1"]},
    {"name": "pyNoteAccs$ebnf$2$subexpression$2", "symbols": [{"literal":"X"}]},
    {"name": "pyNoteAccs$ebnf$2", "symbols": ["pyNoteAccs$ebnf$2", "pyNoteAccs$ebnf$2$subexpression$2"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "pyNoteAccs$ebnf$3", "symbols": []},
    {"name": "pyNoteAccs$ebnf$3$subexpression$1", "symbols": [{"literal":"♯"}]},
    {"name": "pyNoteAccs$ebnf$3$subexpression$1", "symbols": [{"literal":"#"}]},
    {"name": "pyNoteAccs$ebnf$3", "symbols": ["pyNoteAccs$ebnf$3", "pyNoteAccs$ebnf$3$subexpression$1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "pyNoteAccs", "symbols": ["pyNoteAccs$ebnf$2", "pyNoteAccs$ebnf$3"], "postprocess": d => pyInterval(1, 2*d[0].length + d[1].length)},
    {"name": "pyNoteAccs$ebnf$4$subexpression$1", "symbols": [{"literal":"♭"}]},
    {"name": "pyNoteAccs$ebnf$4$subexpression$1", "symbols": [{"literal":"b"}]},
    {"name": "pyNoteAccs$ebnf$4", "symbols": ["pyNoteAccs$ebnf$4$subexpression$1"]},
    {"name": "pyNoteAccs$ebnf$4$subexpression$2", "symbols": [{"literal":"♭"}]},
    {"name": "pyNoteAccs$ebnf$4$subexpression$2", "symbols": [{"literal":"b"}]},
    {"name": "pyNoteAccs$ebnf$4", "symbols": ["pyNoteAccs$ebnf$4", "pyNoteAccs$ebnf$4$subexpression$2"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "pyNoteAccs", "symbols": ["pyNoteAccs$ebnf$4"], "postprocess": d => pyInterval(-1, d[0].length)},
    {"name": "pyNoteAccs$ebnf$5", "symbols": []},
    {"name": "pyNoteAccs$ebnf$5$subexpression$1", "symbols": [{"literal":"♭"}]},
    {"name": "pyNoteAccs$ebnf$5$subexpression$1", "symbols": [{"literal":"b"}]},
    {"name": "pyNoteAccs$ebnf$5", "symbols": ["pyNoteAccs$ebnf$5", "pyNoteAccs$ebnf$5$subexpression$1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "pyNoteAccs$ebnf$6$string$1", "symbols": [{"literal":"\ud834"}, {"literal":"\udd2b"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyNoteAccs$ebnf$6", "symbols": ["pyNoteAccs$ebnf$6$string$1"]},
    {"name": "pyNoteAccs$ebnf$6$string$2", "symbols": [{"literal":"\ud834"}, {"literal":"\udd2b"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "pyNoteAccs$ebnf$6", "symbols": ["pyNoteAccs$ebnf$6", "pyNoteAccs$ebnf$6$string$2"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "pyNoteAccs", "symbols": ["pyNoteAccs$ebnf$5", "pyNoteAccs$ebnf$6"], "postprocess": d => pyInterval(-1, 2*d[0].length + d[1].length)},
    {"name": "npyNote$macrocall$2", "symbols": [/[A-G]/]},
    {"name": "npyNote$macrocall$3", "symbols": ["npyNoteAccs"]},
    {"name": "npyNote$macrocall$1$ebnf$1", "symbols": ["int"], "postprocess": id},
    {"name": "npyNote$macrocall$1$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "npyNote$macrocall$1", "symbols": ["npyNote$macrocall$2", "npyNote$macrocall$3", "npyNote$macrocall$1$ebnf$1"], "postprocess":  function(d) {
        const d2 = d[2] ? parseInt(d[2]) : 4;
        return ["mul", ["div", baseNoteIntvToA(d[0][0]), ["!refIntvToA4"]]
                     , d[1][0].mul(Interval(2).pow(d2 - 4))]; } },
    {"name": "npyNote", "symbols": ["npyNote$macrocall$1"], "postprocess": id},
    {"name": "npyNoteAccs$ebnf$1", "symbols": []},
    {"name": "npyNoteAccs$ebnf$1$subexpression$1$string$1", "symbols": [{"literal":"\ud834"}, {"literal":"\udd2a"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "npyNoteAccs$ebnf$1$subexpression$1", "symbols": ["npyNoteAccs$ebnf$1$subexpression$1$string$1"]},
    {"name": "npyNoteAccs$ebnf$1$subexpression$1", "symbols": [{"literal":"X"}]},
    {"name": "npyNoteAccs$ebnf$1", "symbols": ["npyNoteAccs$ebnf$1", "npyNoteAccs$ebnf$1$subexpression$1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "npyNoteAccs$ebnf$2", "symbols": []},
    {"name": "npyNoteAccs$ebnf$2$subexpression$1", "symbols": [{"literal":"♯"}]},
    {"name": "npyNoteAccs$ebnf$2$subexpression$1", "symbols": [{"literal":"#"}]},
    {"name": "npyNoteAccs$ebnf$2", "symbols": ["npyNoteAccs$ebnf$2", "npyNoteAccs$ebnf$2$subexpression$1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "npyNoteAccs$ebnf$3$subexpression$1$string$1", "symbols": [{"literal":"\ud834"}, {"literal":"\udd32"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "npyNoteAccs$ebnf$3$subexpression$1", "symbols": ["npyNoteAccs$ebnf$3$subexpression$1$string$1"]},
    {"name": "npyNoteAccs$ebnf$3$subexpression$1", "symbols": [{"literal":"t"}]},
    {"name": "npyNoteAccs$ebnf$3", "symbols": ["npyNoteAccs$ebnf$3$subexpression$1"]},
    {"name": "npyNoteAccs$ebnf$3$subexpression$2$string$1", "symbols": [{"literal":"\ud834"}, {"literal":"\udd32"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "npyNoteAccs$ebnf$3$subexpression$2", "symbols": ["npyNoteAccs$ebnf$3$subexpression$2$string$1"]},
    {"name": "npyNoteAccs$ebnf$3$subexpression$2", "symbols": [{"literal":"t"}]},
    {"name": "npyNoteAccs$ebnf$3", "symbols": ["npyNoteAccs$ebnf$3", "npyNoteAccs$ebnf$3$subexpression$2"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "npyNoteAccs", "symbols": ["npyNoteAccs$ebnf$1", "npyNoteAccs$ebnf$2", "npyNoteAccs$ebnf$3"], "postprocess": d => pyInterval(1, 2*d[0].length + d[1].length + 0.5*d[2].length)},
    {"name": "npyNoteAccs$ebnf$4$subexpression$1$string$1", "symbols": [{"literal":"\ud834"}, {"literal":"\udd33"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "npyNoteAccs$ebnf$4$subexpression$1", "symbols": ["npyNoteAccs$ebnf$4$subexpression$1$string$1"]},
    {"name": "npyNoteAccs$ebnf$4$subexpression$1", "symbols": [{"literal":"d"}]},
    {"name": "npyNoteAccs$ebnf$4", "symbols": ["npyNoteAccs$ebnf$4$subexpression$1"]},
    {"name": "npyNoteAccs$ebnf$4$subexpression$2$string$1", "symbols": [{"literal":"\ud834"}, {"literal":"\udd33"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "npyNoteAccs$ebnf$4$subexpression$2", "symbols": ["npyNoteAccs$ebnf$4$subexpression$2$string$1"]},
    {"name": "npyNoteAccs$ebnf$4$subexpression$2", "symbols": [{"literal":"d"}]},
    {"name": "npyNoteAccs$ebnf$4", "symbols": ["npyNoteAccs$ebnf$4", "npyNoteAccs$ebnf$4$subexpression$2"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "npyNoteAccs$ebnf$5", "symbols": []},
    {"name": "npyNoteAccs$ebnf$5$subexpression$1", "symbols": [{"literal":"♭"}]},
    {"name": "npyNoteAccs$ebnf$5$subexpression$1", "symbols": [{"literal":"b"}]},
    {"name": "npyNoteAccs$ebnf$5", "symbols": ["npyNoteAccs$ebnf$5", "npyNoteAccs$ebnf$5$subexpression$1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "npyNoteAccs$ebnf$6", "symbols": []},
    {"name": "npyNoteAccs$ebnf$6$string$1", "symbols": [{"literal":"\ud834"}, {"literal":"\udd2b"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "npyNoteAccs$ebnf$6", "symbols": ["npyNoteAccs$ebnf$6", "npyNoteAccs$ebnf$6$string$1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "npyNoteAccs", "symbols": ["npyNoteAccs$ebnf$4", "npyNoteAccs$ebnf$5", "npyNoteAccs$ebnf$6"], "postprocess": d => pyInterval(-1, 2*d[0].length + d[1].length + 0.5*d[2].length)},
    {"name": "fjsIntv", "symbols": ["fjsNonNeutIntv"], "postprocess": d => d[0](fjsSpec)},
    {"name": "fjsNote", "symbols": ["fjsNonNeutNote"], "postprocess": d => d[0](fjsSpec)},
    {"name": "fjsNonNeutIntv", "symbols": ["pyIntv"], "postprocess": d => _ => d[0]},
    {"name": "fjsNonNeutIntv$macrocall$2", "symbols": ["fjsNonNeutIntv"]},
    {"name": "fjsNonNeutIntv$macrocall$1", "symbols": ["fjsNonNeutIntv$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "fjsNonNeutIntv$macrocall$1", "symbols": ["fjsNonNeutIntv$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "fjsNonNeutIntv$macrocall$1", "symbols": ["fjsNonNeutIntv$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "fjsNonNeutIntv$macrocall$1", "symbols": ["fjsNonNeutIntv$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "fjsNonNeutIntv", "symbols": ["fjsNonNeutIntv$macrocall$1"], "postprocess": id},
    {"name": "fjsNonNeutNote", "symbols": ["pyNote"], "postprocess": d => _ => d[0]},
    {"name": "fjsNonNeutNote$macrocall$2", "symbols": ["fjsNonNeutNote"]},
    {"name": "fjsNonNeutNote$macrocall$1", "symbols": ["fjsNonNeutNote$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "fjsNonNeutNote$macrocall$1", "symbols": ["fjsNonNeutNote$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "fjsNonNeutNote$macrocall$1", "symbols": ["fjsNonNeutNote$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "fjsNonNeutNote$macrocall$1", "symbols": ["fjsNonNeutNote$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "fjsNonNeutNote", "symbols": ["fjsNonNeutNote$macrocall$1"], "postprocess": id},
    {"name": "nfjsIntv", "symbols": ["nfjsNeutIntv"], "postprocess": d => d[0](nfjsSpec)},
    {"name": "nfjsIntv", "symbols": ["nfjsNonNeutIntv"], "postprocess": d => d[0](nfjsSpec)},
    {"name": "nfjsNote", "symbols": ["nfjsNeutNote"], "postprocess": d => d[0](nfjsSpec)},
    {"name": "nfjsNote", "symbols": ["nfjsNonNeutNote"], "postprocess": d => d[0](nfjsSpec)},
    {"name": "nfjsNeutIntv", "symbols": ["npyIntv"], "postprocess": d => _ => d[0]},
    {"name": "nfjsNeutIntv$macrocall$2", "symbols": ["nfjsNeutIntv"]},
    {"name": "nfjsNeutIntv$macrocall$1", "symbols": ["nfjsNeutIntv$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "nfjsNeutIntv$macrocall$1", "symbols": ["nfjsNeutIntv$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "nfjsNeutIntv$macrocall$1", "symbols": ["nfjsNeutIntv$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "nfjsNeutIntv$macrocall$1", "symbols": ["nfjsNeutIntv$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "nfjsNeutIntv", "symbols": ["nfjsNeutIntv$macrocall$1"], "postprocess": id},
    {"name": "nfjsNonNeutIntv", "symbols": ["pyIntv"], "postprocess": d => _ => d[0]},
    {"name": "nfjsNonNeutIntv$macrocall$2", "symbols": ["nfjsNonNeutIntv"]},
    {"name": "nfjsNonNeutIntv$macrocall$1", "symbols": ["nfjsNonNeutIntv$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "nfjsNonNeutIntv$macrocall$1", "symbols": ["nfjsNonNeutIntv$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "nfjsNonNeutIntv$macrocall$1", "symbols": ["nfjsNonNeutIntv$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "nfjsNonNeutIntv$macrocall$1", "symbols": ["nfjsNonNeutIntv$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "nfjsNonNeutIntv", "symbols": ["nfjsNonNeutIntv$macrocall$1"], "postprocess": id},
    {"name": "nfjsNeutNote", "symbols": ["npyNote"], "postprocess": d => _ => d[0]},
    {"name": "nfjsNeutNote$macrocall$2", "symbols": ["nfjsNeutNote"]},
    {"name": "nfjsNeutNote$macrocall$1", "symbols": ["nfjsNeutNote$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "nfjsNeutNote$macrocall$1", "symbols": ["nfjsNeutNote$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "nfjsNeutNote$macrocall$1", "symbols": ["nfjsNeutNote$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "nfjsNeutNote$macrocall$1", "symbols": ["nfjsNeutNote$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "nfjsNeutNote", "symbols": ["nfjsNeutNote$macrocall$1"], "postprocess": id},
    {"name": "nfjsNonNeutNote", "symbols": ["pyNote"], "postprocess": d => _ => d[0]},
    {"name": "nfjsNonNeutNote$macrocall$2", "symbols": ["nfjsNonNeutNote"]},
    {"name": "nfjsNonNeutNote$macrocall$1", "symbols": ["nfjsNonNeutNote$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "nfjsNonNeutNote$macrocall$1", "symbols": ["nfjsNonNeutNote$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "nfjsNonNeutNote$macrocall$1", "symbols": ["nfjsNonNeutNote$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "nfjsNonNeutNote$macrocall$1", "symbols": ["nfjsNonNeutNote$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "nfjsNonNeutNote", "symbols": ["nfjsNonNeutNote$macrocall$1"], "postprocess": id},
    {"name": "fjsLikeIntv", "symbols": ["fjsLikeSemiNeutIntv"], "postprocess": (d,loc,_) => ["!fjsSNPy", d[0], loc]},
    {"name": "fjsLikeIntv", "symbols": ["fjsLikeNeutIntv"], "postprocess": (d,loc,_) => ["!fjsNPy", d[0], loc]},
    {"name": "fjsLikeIntv", "symbols": ["fjsLikeNonNeutIntv"], "postprocess": (d,loc,_) => ["!fjsPy", d[0], loc]},
    {"name": "fjsLikeNote", "symbols": ["fjsLikeNeutNote"], "postprocess": (d,loc,_) => ["!fjsNPy", d[0], loc]},
    {"name": "fjsLikeNote", "symbols": ["fjsLikeNonNeutNote"], "postprocess": (d,loc,_) => ["!fjsPy", d[0], loc]},
    {"name": "strictFJSLikeIntv$macrocall$2", "symbols": ["fjsLikeSemiNeutIntv"]},
    {"name": "strictFJSLikeIntv$macrocall$1", "symbols": ["strictFJSLikeIntv$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "strictFJSLikeIntv$macrocall$1", "symbols": ["strictFJSLikeIntv$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "strictFJSLikeIntv$macrocall$1", "symbols": ["strictFJSLikeIntv$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "strictFJSLikeIntv$macrocall$1", "symbols": ["strictFJSLikeIntv$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "strictFJSLikeIntv", "symbols": ["strictFJSLikeIntv$macrocall$1"], "postprocess": (d,loc,_) => ["!fjsSNPy", d[0], loc]},
    {"name": "strictFJSLikeIntv$macrocall$4", "symbols": ["fjsLikeNeutIntv"]},
    {"name": "strictFJSLikeIntv$macrocall$3", "symbols": ["strictFJSLikeIntv$macrocall$4", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "strictFJSLikeIntv$macrocall$3", "symbols": ["strictFJSLikeIntv$macrocall$4", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "strictFJSLikeIntv$macrocall$3", "symbols": ["strictFJSLikeIntv$macrocall$4", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "strictFJSLikeIntv$macrocall$3", "symbols": ["strictFJSLikeIntv$macrocall$4", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "strictFJSLikeIntv", "symbols": ["strictFJSLikeIntv$macrocall$3"], "postprocess": (d,loc,_) => ["!fjsNPy", d[0], loc]},
    {"name": "strictFJSLikeIntv$macrocall$6", "symbols": ["fjsLikeNonNeutIntv"]},
    {"name": "strictFJSLikeIntv$macrocall$5", "symbols": ["strictFJSLikeIntv$macrocall$6", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "strictFJSLikeIntv$macrocall$5", "symbols": ["strictFJSLikeIntv$macrocall$6", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "strictFJSLikeIntv$macrocall$5", "symbols": ["strictFJSLikeIntv$macrocall$6", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "strictFJSLikeIntv$macrocall$5", "symbols": ["strictFJSLikeIntv$macrocall$6", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "strictFJSLikeIntv", "symbols": ["strictFJSLikeIntv$macrocall$5"], "postprocess": (d,loc,_) => ["!fjsPy", d[0], loc]},
    {"name": "strictFJSLikeNote$macrocall$2", "symbols": ["fjsLikeNeutNote"]},
    {"name": "strictFJSLikeNote$macrocall$1", "symbols": ["strictFJSLikeNote$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "strictFJSLikeNote$macrocall$1", "symbols": ["strictFJSLikeNote$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "strictFJSLikeNote$macrocall$1", "symbols": ["strictFJSLikeNote$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "strictFJSLikeNote$macrocall$1", "symbols": ["strictFJSLikeNote$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "strictFJSLikeNote", "symbols": ["strictFJSLikeNote$macrocall$1"], "postprocess": (d,loc,_) => ["!fjsNPy", d[0], loc]},
    {"name": "strictFJSLikeNote$macrocall$4", "symbols": ["fjsLikeNonNeutNote"]},
    {"name": "strictFJSLikeNote$macrocall$3", "symbols": ["strictFJSLikeNote$macrocall$4", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "strictFJSLikeNote$macrocall$3", "symbols": ["strictFJSLikeNote$macrocall$4", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "strictFJSLikeNote$macrocall$3", "symbols": ["strictFJSLikeNote$macrocall$4", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "strictFJSLikeNote$macrocall$3", "symbols": ["strictFJSLikeNote$macrocall$4", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "strictFJSLikeNote", "symbols": ["strictFJSLikeNote$macrocall$3"], "postprocess": (d,loc,_) => ["!fjsPy", d[0], loc]},
    {"name": "fjsLikeSemiNeutIntv", "symbols": ["snpyIntv"], "postprocess": d => _ => d[0]},
    {"name": "fjsLikeSemiNeutIntv$macrocall$2", "symbols": ["fjsLikeSemiNeutIntv"]},
    {"name": "fjsLikeSemiNeutIntv$macrocall$1", "symbols": ["fjsLikeSemiNeutIntv$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "fjsLikeSemiNeutIntv$macrocall$1", "symbols": ["fjsLikeSemiNeutIntv$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "fjsLikeSemiNeutIntv$macrocall$1", "symbols": ["fjsLikeSemiNeutIntv$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "fjsLikeSemiNeutIntv$macrocall$1", "symbols": ["fjsLikeSemiNeutIntv$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "fjsLikeSemiNeutIntv", "symbols": ["fjsLikeSemiNeutIntv$macrocall$1"], "postprocess": id},
    {"name": "fjsLikeNeutIntv", "symbols": ["npyIntv"], "postprocess": d => _ => d[0]},
    {"name": "fjsLikeNeutIntv$macrocall$2", "symbols": ["fjsLikeNeutIntv"]},
    {"name": "fjsLikeNeutIntv$macrocall$1", "symbols": ["fjsLikeNeutIntv$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "fjsLikeNeutIntv$macrocall$1", "symbols": ["fjsLikeNeutIntv$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "fjsLikeNeutIntv$macrocall$1", "symbols": ["fjsLikeNeutIntv$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "fjsLikeNeutIntv$macrocall$1", "symbols": ["fjsLikeNeutIntv$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "fjsLikeNeutIntv", "symbols": ["fjsLikeNeutIntv$macrocall$1"], "postprocess": id},
    {"name": "fjsLikeNonNeutIntv", "symbols": ["pyIntv"], "postprocess": d => _ => d[0]},
    {"name": "fjsLikeNonNeutIntv$macrocall$2", "symbols": ["fjsLikeNonNeutIntv"]},
    {"name": "fjsLikeNonNeutIntv$macrocall$1", "symbols": ["fjsLikeNonNeutIntv$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "fjsLikeNonNeutIntv$macrocall$1", "symbols": ["fjsLikeNonNeutIntv$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "fjsLikeNonNeutIntv$macrocall$1", "symbols": ["fjsLikeNonNeutIntv$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "fjsLikeNonNeutIntv$macrocall$1", "symbols": ["fjsLikeNonNeutIntv$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "fjsLikeNonNeutIntv", "symbols": ["fjsLikeNonNeutIntv$macrocall$1"], "postprocess": id},
    {"name": "fjsLikeNeutNote", "symbols": ["npyNote"], "postprocess": d => _ => d[0]},
    {"name": "fjsLikeNeutNote$macrocall$2", "symbols": ["fjsLikeNeutNote"]},
    {"name": "fjsLikeNeutNote$macrocall$1", "symbols": ["fjsLikeNeutNote$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "fjsLikeNeutNote$macrocall$1", "symbols": ["fjsLikeNeutNote$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "fjsLikeNeutNote$macrocall$1", "symbols": ["fjsLikeNeutNote$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "fjsLikeNeutNote$macrocall$1", "symbols": ["fjsLikeNeutNote$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "fjsLikeNeutNote", "symbols": ["fjsLikeNeutNote$macrocall$1"], "postprocess": id},
    {"name": "fjsLikeNonNeutNote", "symbols": ["pyNote"], "postprocess": d => _ => d[0]},
    {"name": "fjsLikeNonNeutNote$macrocall$2", "symbols": ["fjsLikeNonNeutNote"]},
    {"name": "fjsLikeNonNeutNote$macrocall$1", "symbols": ["fjsLikeNonNeutNote$macrocall$2", {"literal":"^"}, "fjsAccList"], "postprocess": d => spec => ["mul", d[0][0](spec), d[2](spec)]},
    {"name": "fjsLikeNonNeutNote$macrocall$1", "symbols": ["fjsLikeNonNeutNote$macrocall$2", "fjsSupAcc"], "postprocess": d => spec => ["mul", d[0][0](spec), d[1](spec)]},
    {"name": "fjsLikeNonNeutNote$macrocall$1", "symbols": ["fjsLikeNonNeutNote$macrocall$2", {"literal":"_"}, "fjsAccList"], "postprocess": d => spec => ["div", d[0][0](spec), d[2](spec)]},
    {"name": "fjsLikeNonNeutNote$macrocall$1", "symbols": ["fjsLikeNonNeutNote$macrocall$2", "fjsSubAcc"], "postprocess": d => spec => ["div", d[0][0](spec), d[1](spec)]},
    {"name": "fjsLikeNonNeutNote", "symbols": ["fjsLikeNonNeutNote$macrocall$1"], "postprocess": id},
    {"name": "fjsAccList", "symbols": ["fjsAcc"], "postprocess": d => spec => ["!fjsFactor", d[0], spec]},
    {"name": "fjsAccList", "symbols": ["fjsAccList", {"literal":","}, "fjsAcc"], "postprocess": d => spec => ["mul", d[0](spec), ["!fjsFactor", d[2], spec]]},
    {"name": "fjsAcc", "symbols": ["fjsAccExpr"], "postprocess": (d,loc,_) => ["!ensureNo2Or3", d[0], loc]},
    {"name": "fjsAccExpr", "symbols": ["posInt"], "postprocess": d => Interval(d[0])},
    {"name": "fjsAccExpr$string$1", "symbols": [{"literal":"s"}, {"literal":"q"}, {"literal":"r"}, {"literal":"t"}, {"literal":"("}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "fjsAccExpr", "symbols": ["fjsAccExpr$string$1", "fjsAccExpr", {"literal":")"}], "postprocess": d => d[1].sqrt()},
    {"name": "fjsAccExpr$string$2", "symbols": [{"literal":"r"}, {"literal":"o"}, {"literal":"o"}, {"literal":"t"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "fjsAccExpr", "symbols": ["fjsAccExpr$string$2", "posInt", {"literal":"("}, "fjsAccExpr", {"literal":")"}], "postprocess": d => d[3].root(parseInt(d[1]))},
    {"name": "fjsAccExpr", "symbols": [{"literal":"("}, "fjsAccExpr", {"literal":"^"}, "frcExpr3", {"literal":")"}], "postprocess": d => d[1].pow(d[3])},
    {"name": "fjsSupAcc", "symbols": ["posIntSup"], "postprocess": (d,loc,_) => spec => ["!fjsFactor", ["!ensureNo2Or3", Interval(d[0]), loc], spec]},
    {"name": "fjsSubAcc", "symbols": ["posIntSub"], "postprocess": (d,loc,_) => spec => ["!fjsFactor", ["!ensureNo2Or3", Interval(d[0]), loc], spec]},
    {"name": "upsDnsIntv", "symbols": ["upsDnsIntvAbD"], "postprocess": id},
    {"name": "upsDnsIntv", "symbols": ["upsDnsIntvVbD"], "postprocess": id},
    {"name": "upsDnsIntvAbD", "symbols": ["upsDnsIntvAb"], "postprocess": id},
    {"name": "upsDnsIntvAbD", "symbols": ["desc", "upsDnsIntvAb"], "postprocess": d => ["-", 0, d[1]]},
    {"name": "upsDnsIntvAb", "symbols": ["upsDns", "pyIntv"], "postprocess": (d,loc,_) => ["!updnsSymb", d[0], d[1], loc]},
    {"name": "upsDnsIntvAb", "symbols": ["upsDns", "npyIntv"], "postprocess": (d,loc,_) => ["!updnsSymb", d[0], d[1], loc]},
    {"name": "upsDnsIntvAb", "symbols": ["upsDns", "snpyIntv"], "postprocess": (d,loc,_) => ["!updnsSymb", d[0], d[1], loc]},
    {"name": "upsDnsIntvAb", "symbols": ["upsDnsNz", "degV0"], "postprocess": (d,loc,_) => ["!updnsPerfSymb", d[0], d[1], loc]},
    {"name": "upsDnsIntvAb", "symbols": ["upsDns", {"literal":"~"}, "degV0"], "postprocess": (d,loc,_) => ["!updnsNeutSymb", d[0], d[2], loc]},
    {"name": "upsDnsIntvVbD", "symbols": ["upsDnsIntvVb"], "postprocess": id},
    {"name": "upsDnsIntvVbD", "symbols": ["desc", "upsDnsIntvVb"], "postprocess": d => ["-", 0, d[1]]},
    {"name": "upsDnsIntvVb", "symbols": ["upsDnsVb", "upDnsVbSep", "pyIntvVb"], "postprocess": (d,loc,_) => ["!updnsSymb", d[0], d[2], loc]},
    {"name": "upsDnsIntvVb", "symbols": ["upsDnsVb", "upDnsVbSep", "npyIntvVb"], "postprocess": (d,loc,_) => ["!updnsSymb", d[0], d[2], loc]},
    {"name": "upsDnsIntvVb", "symbols": ["upsDnsVb", "upDnsVbSep", "snpyIntvVb"], "postprocess": (d,loc,_) => ["!updnsSymb", d[0], d[2], loc]},
    {"name": "upsDnsIntvVb", "symbols": ["upsDnsVbNz", "degV1"], "postprocess": (d,loc,_) => ["!updnsPerfSymb", d[0], d[1], loc]},
    {"name": "upsDnsIntvVb", "symbols": ["degV1Uniq"], "postprocess": (d,loc,_) => ["!updnsPerfSymb", 0, d[0], loc]},
    {"name": "upsDnsIntvVb$string$1", "symbols": [{"literal":"m"}, {"literal":"i"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsIntvVb", "symbols": ["upsDnsVb", "upDnsVbSep", "upsDnsIntvVb$string$1", "degV1"], "postprocess": (d,loc,_) => ["!updnsNeutSymb", d[0], d[3], loc]},
    {"name": "upsDnsNote", "symbols": ["upsDns", "pyNote"], "postprocess": (d,loc,_) => ["!updnsNote", d[0], d[1], loc]},
    {"name": "upsDnsNote", "symbols": ["upsDns", "npyNote"], "postprocess": (d,loc,_) => ["!updnsNote", d[0], d[1], loc]},
    {"name": "upsDns", "symbols": [], "postprocess": d => 0},
    {"name": "upsDns", "symbols": ["upsDnsNz"], "postprocess": id},
    {"name": "upsDnsNz$ebnf$1", "symbols": [{"literal":"^"}]},
    {"name": "upsDnsNz$ebnf$1", "symbols": ["upsDnsNz$ebnf$1", {"literal":"^"}], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "upsDnsNz", "symbols": ["upsDnsNz$ebnf$1"], "postprocess": d => d[0].length},
    {"name": "upsDnsNz$ebnf$2", "symbols": [{"literal":"v"}]},
    {"name": "upsDnsNz$ebnf$2", "symbols": ["upsDnsNz$ebnf$2", {"literal":"v"}], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "upsDnsNz", "symbols": ["upsDnsNz$ebnf$2"], "postprocess": d => -d[0].length},
    {"name": "upsDnsNz$string$1", "symbols": [{"literal":"("}, {"literal":"^"}, {"literal":")"}, {"literal":"^"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsNz", "symbols": ["upsDnsNz$string$1", /[1-9]/], "postprocess": d => parseInt(d[1])},
    {"name": "upsDnsNz$string$2", "symbols": [{"literal":"("}, {"literal":"v"}, {"literal":")"}, {"literal":"^"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsNz", "symbols": ["upsDnsNz$string$2", /[1-9]/], "postprocess": d => -parseInt(d[1])},
    {"name": "upsDnsNz$string$3", "symbols": [{"literal":"("}, {"literal":"^"}, {"literal":")"}, {"literal":"^"}, {"literal":"("}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsNz", "symbols": ["upsDnsNz$string$3", "posInt", {"literal":")"}], "postprocess": d => parseInt(d[1])},
    {"name": "upsDnsNz$string$4", "symbols": [{"literal":"("}, {"literal":"v"}, {"literal":")"}, {"literal":"^"}, {"literal":"("}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsNz", "symbols": ["upsDnsNz$string$4", "posInt", {"literal":")"}], "postprocess": d => -parseInt(d[1])},
    {"name": "upsDnsNz", "symbols": [{"literal":"^"}, "posIntSup"], "postprocess": d => d[1]},
    {"name": "upsDnsNz", "symbols": [{"literal":"v"}, "posIntSup"], "postprocess": d => -d[1]},
    {"name": "upsDnsVb", "symbols": [], "postprocess": d => 0},
    {"name": "upsDnsVb", "symbols": ["upsDnsVbNz"], "postprocess": id},
    {"name": "upsDnsVbNz$string$1", "symbols": [{"literal":"u"}, {"literal":"p"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsVbNz", "symbols": ["upsDnsVbNz$string$1"], "postprocess": d => 1},
    {"name": "upsDnsVbNz$string$2", "symbols": [{"literal":"d"}, {"literal":"o"}, {"literal":"w"}, {"literal":"n"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsVbNz", "symbols": ["upsDnsVbNz$string$2"], "postprocess": d => -1},
    {"name": "upsDnsVbNz$string$3", "symbols": [{"literal":"d"}, {"literal":"o"}, {"literal":"u"}, {"literal":"b"}, {"literal":"l"}, {"literal":"e"}, {"literal":"-"}, {"literal":"u"}, {"literal":"p"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsVbNz", "symbols": ["upsDnsVbNz$string$3"], "postprocess": d => 2},
    {"name": "upsDnsVbNz$string$4", "symbols": [{"literal":"d"}, {"literal":"o"}, {"literal":"u"}, {"literal":"b"}, {"literal":"l"}, {"literal":"e"}, {"literal":"-"}, {"literal":"d"}, {"literal":"o"}, {"literal":"w"}, {"literal":"n"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsVbNz", "symbols": ["upsDnsVbNz$string$4"], "postprocess": d => -2},
    {"name": "upsDnsVbNz$string$5", "symbols": [{"literal":"t"}, {"literal":"r"}, {"literal":"i"}, {"literal":"p"}, {"literal":"l"}, {"literal":"e"}, {"literal":"-"}, {"literal":"u"}, {"literal":"p"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsVbNz", "symbols": ["upsDnsVbNz$string$5"], "postprocess": d => 3},
    {"name": "upsDnsVbNz$string$6", "symbols": [{"literal":"t"}, {"literal":"r"}, {"literal":"i"}, {"literal":"p"}, {"literal":"l"}, {"literal":"e"}, {"literal":"-"}, {"literal":"d"}, {"literal":"o"}, {"literal":"w"}, {"literal":"n"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsVbNz", "symbols": ["upsDnsVbNz$string$6"], "postprocess": d => -3},
    {"name": "upsDnsVbNz$string$7", "symbols": [{"literal":"-"}, {"literal":"u"}, {"literal":"p"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsVbNz", "symbols": ["posInt", "upsDnsVbNz$string$7"], "postprocess": d => parseInt(d[0])},
    {"name": "upsDnsVbNz$string$8", "symbols": [{"literal":"-"}, {"literal":"d"}, {"literal":"o"}, {"literal":"w"}, {"literal":"n"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "upsDnsVbNz", "symbols": ["posInt", "upsDnsVbNz$string$8"], "postprocess": d => -parseInt(d[0])},
    {"name": "upDnsVbSep", "symbols": ["_"]},
    {"name": "upDnsVbSep", "symbols": ["_", {"literal":"-"}, "_"]},
    {"name": "anyClrIntv", "symbols": ["aclrIntv"], "postprocess": id},
    {"name": "anyClrIntv", "symbols": ["clrIntv"], "postprocess": id},
    {"name": "anyClrNote", "symbols": ["aclrNote"], "postprocess": id},
    {"name": "anyClrNote", "symbols": ["clrNote"], "postprocess": id},
    {"name": "aclrIntv", "symbols": ["aclrCos", "aclrM", "aclrP", "degV0"], "postprocess": (d,loc,_) => ["!clrIntv", d[0], d[1], d[2], d[3], loc]},
    {"name": "aclrIntv", "symbols": ["desc", "aclrCos", "aclrM", "aclrP", "degV0"], "postprocess": (d,loc,_) => ["recip", ["!clrIntv", d[1], d[2], d[3], d[4], loc]]},
    {"name": "aclrNote", "symbols": ["aclrP", "pyNote"], "postprocess": (d,loc,_) => ["!clrNote", d[0], d[1], loc]},
    {"name": "aclrCos", "symbols": [], "postprocess": d => 0},
    {"name": "aclrCos$ebnf$1", "symbols": [{"literal":"c"}]},
    {"name": "aclrCos$ebnf$1", "symbols": ["aclrCos$ebnf$1", {"literal":"c"}], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "aclrCos", "symbols": ["aclrCos$ebnf$1"], "postprocess": d => d[0].length},
    {"name": "aclrCos$string$1", "symbols": [{"literal":"c"}, {"literal":"^"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "aclrCos", "symbols": ["aclrCos$string$1", /[1-9]/], "postprocess": d => parseInt(d[1])},
    {"name": "aclrCos$string$2", "symbols": [{"literal":"c"}, {"literal":"^"}, {"literal":"("}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "aclrCos", "symbols": ["aclrCos$string$2", "posInt", {"literal":")"}], "postprocess": d => parseInt(d[1])},
    {"name": "aclrCos", "symbols": [{"literal":"c"}, "posIntSup"], "postprocess": d => parseInt(d[1])},
    {"name": "aclrM", "symbols": [], "postprocess": d => 0},
    {"name": "aclrM$ebnf$1", "symbols": [{"literal":"L"}]},
    {"name": "aclrM$ebnf$1", "symbols": ["aclrM$ebnf$1", {"literal":"L"}], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "aclrM", "symbols": ["aclrM$ebnf$1"], "postprocess": d => d[0].length},
    {"name": "aclrM$string$1", "symbols": [{"literal":"L"}, {"literal":"^"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "aclrM", "symbols": ["aclrM$string$1", /[1-9]/], "postprocess": d => parseInt(d[1])},
    {"name": "aclrM$string$2", "symbols": [{"literal":"L"}, {"literal":"^"}, {"literal":"("}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "aclrM", "symbols": ["aclrM$string$2", "posInt", {"literal":")"}], "postprocess": d => parseInt(d[1])},
    {"name": "aclrM", "symbols": [{"literal":"L"}, "posIntSup"], "postprocess": d => parseInt(d[1])},
    {"name": "aclrM$ebnf$2", "symbols": [{"literal":"s"}]},
    {"name": "aclrM$ebnf$2", "symbols": ["aclrM$ebnf$2", {"literal":"s"}], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "aclrM", "symbols": ["aclrM$ebnf$2"], "postprocess": d => -d[0].length},
    {"name": "aclrM$string$3", "symbols": [{"literal":"s"}, {"literal":"^"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "aclrM", "symbols": ["aclrM$string$3", /[1-9]/], "postprocess": d => -parseInt(d[1])},
    {"name": "aclrM$string$4", "symbols": [{"literal":"s"}, {"literal":"^"}, {"literal":"("}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "aclrM", "symbols": ["aclrM$string$4", "posInt", {"literal":")"}], "postprocess": d => -parseInt(d[1])},
    {"name": "aclrM", "symbols": [{"literal":"s"}, "posIntSup"], "postprocess": d => -parseInt(d[1])},
    {"name": "aclrP", "symbols": [{"literal":"w"}], "postprocess": d => []},
    {"name": "aclrP$ebnf$1", "symbols": ["aclrPP1"]},
    {"name": "aclrP$ebnf$1", "symbols": ["aclrP$ebnf$1", "aclrPP1"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "aclrP", "symbols": ["aclrP$ebnf$1"], "postprocess": d => d[0].flat(1)},
    {"name": "aclrPP1", "symbols": ["aclrPP"], "postprocess": d => [d[0]]},
    {"name": "aclrPP1", "symbols": ["aclrPP", {"literal":"^"}, /[1-9]/], "postprocess": d => Array(parseInt(d[2])).fill(d[0])},
    {"name": "aclrPP1$string$1", "symbols": [{"literal":"^"}, {"literal":"("}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "aclrPP1", "symbols": ["aclrPP", "aclrPP1$string$1", "posInt", {"literal":")"}], "postprocess": d => Array(parseInt(d[2])).fill(d[0])},
    {"name": "aclrPP1", "symbols": ["aclrPP", "posIntSup"], "postprocess": d => Array(parseInt(d[1])).fill(d[0])},
    {"name": "aclrPP", "symbols": [{"literal":"y"}], "postprocess": d => Interval(5)},
    {"name": "aclrPP", "symbols": [{"literal":"g"}], "postprocess": d => Interval(1,5)},
    {"name": "aclrPP", "symbols": [{"literal":"z"}], "postprocess": d => Interval(7)},
    {"name": "aclrPP", "symbols": [{"literal":"r"}], "postprocess": d => Interval(1,7)},
    {"name": "aclrPP$ebnf$1", "symbols": [{"literal":"o"}]},
    {"name": "aclrPP$ebnf$1", "symbols": ["aclrPP$ebnf$1", {"literal":"o"}], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "aclrPP", "symbols": ["posInt", "aclrPP$ebnf$1"], "postprocess": (d,loc,_) => ["!aclrPP", parseInt(d[0]), d[1].length, loc]},
    {"name": "aclrPP$ebnf$2", "symbols": [{"literal":"u"}]},
    {"name": "aclrPP$ebnf$2", "symbols": ["aclrPP$ebnf$2", {"literal":"u"}], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "aclrPP", "symbols": ["posInt", "aclrPP$ebnf$2"], "postprocess": (d,loc,_) => ["!aclrPP", parseInt(d[0]), -d[1].length, loc]},
    {"name": "clrIntv", "symbols": ["clrCos", "clrM", "clrP", "degV1"], "postprocess": (d,loc,_) => ["!clrIntv", d[0], d[1], d[2], d[3], loc]},
    {"name": "clrIntv", "symbols": ["desc", "clrCos", "clrM", "clrP", "degV1"], "postprocess": (d,loc,_) => ["recip", ["!clrIntv", d[1], d[2], d[3], d[4], loc]]},
    {"name": "clrNote", "symbols": ["clrP", "_", "pyNote"], "postprocess": (d,loc,_) => ["!clrNote", d[0], d[2], loc]},
    {"name": "clrCos", "symbols": [], "postprocess": d => 0},
    {"name": "clrCos$subexpression$1", "symbols": [/[cC]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrCos$ebnf$1", "symbols": [{"literal":"-"}], "postprocess": id},
    {"name": "clrCos$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "clrCos", "symbols": ["clrCos$subexpression$1", {"literal":"o"}, "clrCos$ebnf$1", "clrCos"], "postprocess": d => ["+", d[3], 1]},
    {"name": "clrCos$subexpression$2", "symbols": [/[cC]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrCos$ebnf$2", "symbols": [{"literal":"-"}], "postprocess": id},
    {"name": "clrCos$ebnf$2", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "clrCos", "symbols": ["clrMPs", "clrCos$subexpression$2", {"literal":"o"}, "clrCos$ebnf$2", "clrCos"], "postprocess": d => ["+", d[4], d[0]]},
    {"name": "clrM", "symbols": [], "postprocess": d => 0},
    {"name": "clrM$subexpression$1", "symbols": [/[lL]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrM$ebnf$1", "symbols": [{"literal":"-"}], "postprocess": id},
    {"name": "clrM$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "clrM", "symbols": ["clrM$subexpression$1", {"literal":"a"}, "clrM$ebnf$1", "clrM"], "postprocess": d => ["+", d[3], 1]},
    {"name": "clrM$subexpression$2", "symbols": [/[lL]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrM$ebnf$2", "symbols": [{"literal":"-"}], "postprocess": id},
    {"name": "clrM$ebnf$2", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "clrM", "symbols": ["clrMPs", "clrM$subexpression$2", {"literal":"a"}, "clrM$ebnf$2", "clrM"], "postprocess": d => ["+", d[4], d[0]]},
    {"name": "clrM$subexpression$3", "symbols": [/[sS]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrM$ebnf$3", "symbols": [{"literal":"-"}], "postprocess": id},
    {"name": "clrM$ebnf$3", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "clrM", "symbols": ["clrM$subexpression$3", {"literal":"a"}, "clrM$ebnf$3", "clrM"], "postprocess": d => ["-", d[3], 1]},
    {"name": "clrM$subexpression$4", "symbols": [/[sS]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrM$ebnf$4", "symbols": [{"literal":"-"}], "postprocess": id},
    {"name": "clrM$ebnf$4", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "clrM", "symbols": ["clrMPs", "clrM$subexpression$4", {"literal":"a"}, "clrM$ebnf$4", "clrM"], "postprocess": d => ["-", d[4], d[0]]},
    {"name": "clrP$subexpression$1", "symbols": [/[wW]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrP", "symbols": ["clrP$subexpression$1", {"literal":"a"}], "postprocess": d => []},
    {"name": "clrP$subexpression$2", "symbols": [/[iI]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrP$string$1", "symbols": [{"literal":"l"}, {"literal":"o"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "clrP", "symbols": ["clrP$subexpression$2", "clrP$string$1"], "postprocess": d => [Interval(11)]},
    {"name": "clrP$subexpression$3", "symbols": [/[iI]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrP$string$2", "symbols": [{"literal":"s"}, {"literal":"o"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "clrP", "symbols": ["clrP$subexpression$3", "clrP$string$2"], "postprocess": d => [Interval(17)]},
    {"name": "clrP$subexpression$4", "symbols": [/[iI]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrP$string$3", "symbols": [{"literal":"n"}, {"literal":"o"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "clrP", "symbols": ["clrP$subexpression$4", "clrP$string$3"], "postprocess": d => [Interval(19)]},
    {"name": "clrP$subexpression$5", "symbols": [/[iI]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrP$string$4", "symbols": [{"literal":"n"}, {"literal":"u"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "clrP", "symbols": ["clrP$subexpression$5", "clrP$string$4"], "postprocess": d => [Interval(1,19)]},
    {"name": "clrP", "symbols": ["clrPPs"], "postprocess": id},
    {"name": "clrPPs$ebnf$1", "symbols": ["clrPPsMid1"], "postprocess": id},
    {"name": "clrPPs$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "clrPPs", "symbols": ["clrPPs$ebnf$1", "clrPPsMid3", "clrPPsEnd"], "postprocess": d => (d[0] || []).concat(d[1]).concat(d[2])},
    {"name": "clrPPs", "symbols": ["clrPPsEnd"], "postprocess": id},
    {"name": "clrPPsEnd", "symbols": ["clrPP"], "postprocess": d => [d[0]]},
    {"name": "clrPPsEnd", "symbols": ["clrPP", "clrPPsEnd"], "postprocess": d => [d[0]].concat(d[1])},
    {"name": "clrPPsEnd$ebnf$1$string$1", "symbols": [{"literal":"-"}, {"literal":"a"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "clrPPsEnd$ebnf$1", "symbols": ["clrPPsEnd$ebnf$1$string$1"], "postprocess": id},
    {"name": "clrPPsEnd$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "clrPPsEnd", "symbols": ["clrMPs", "clrPPsEnd", "clrPPsEnd$ebnf$1"], "postprocess": d => d[1].map(i => ["pow", i, d[0]])},
    {"name": "clrPPsMid1", "symbols": ["clrPPsMid1", "clrPPsMid2"], "postprocess": d => d[0].concat(d[1])},
    {"name": "clrPPsMid1", "symbols": ["clrPPsMid2"], "postprocess": id},
    {"name": "clrPPsMid2", "symbols": ["clrPP"], "postprocess": d => [d[0]]},
    {"name": "clrPPsMid2", "symbols": ["clrPPsMid3"], "postprocess": id},
    {"name": "clrPPsMid3$ebnf$1", "symbols": [{"literal":"a"}], "postprocess": id},
    {"name": "clrPPsMid3$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "clrPPsMid3", "symbols": ["clrMPs", "clrPPsMid1", {"literal":"-"}, "clrPPsMid3$ebnf$1"], "postprocess": d => d[1].map(i => ["pow", i, d[0]])},
    {"name": "clrPP$subexpression$1", "symbols": [/[yY]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrPP", "symbols": ["clrPP$subexpression$1", {"literal":"o"}], "postprocess": d => Interval(5)},
    {"name": "clrPP$subexpression$2", "symbols": [/[gG]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrPP", "symbols": ["clrPP$subexpression$2", {"literal":"u"}], "postprocess": d => Interval(1,5)},
    {"name": "clrPP$subexpression$3", "symbols": [/[zZ]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrPP", "symbols": ["clrPP$subexpression$3", {"literal":"o"}], "postprocess": d => Interval(7)},
    {"name": "clrPP$subexpression$4", "symbols": [/[rR]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrPP", "symbols": ["clrPP$subexpression$4", {"literal":"u"}], "postprocess": d => Interval(1,7)},
    {"name": "clrPP$subexpression$5", "symbols": [/[lL]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrPP", "symbols": ["clrPP$subexpression$5", {"literal":"o"}], "postprocess": d => Interval(11)},
    {"name": "clrPP$subexpression$6", "symbols": [/[lL]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrPP", "symbols": ["clrPP$subexpression$6", {"literal":"u"}], "postprocess": d => Interval(1,11)},
    {"name": "clrPP", "symbols": ["clrGenPP", {"literal":"o"}], "postprocess": d => d[0]},
    {"name": "clrPP", "symbols": ["clrGenPP", {"literal":"u"}], "postprocess": d => ["recip", d[0]]},
    {"name": "clrMPs$ebnf$1", "symbols": ["clrMP"]},
    {"name": "clrMPs$ebnf$1", "symbols": ["clrMPs$ebnf$1", "clrMP"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "clrMPs", "symbols": ["clrMPs$ebnf$1"], "postprocess": (d,loc,_) => ["!clrMPs", d[0], loc]},
    {"name": "clrMP$subexpression$1", "symbols": [/[bB]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrMP", "symbols": ["clrMP$subexpression$1", {"literal":"i"}], "postprocess": d => 2},
    {"name": "clrMP$subexpression$2", "symbols": [/[tT]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrMP$string$1", "symbols": [{"literal":"r"}, {"literal":"i"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "clrMP", "symbols": ["clrMP$subexpression$2", "clrMP$string$1"], "postprocess": d => 3},
    {"name": "clrMP$subexpression$3", "symbols": [/[qQ]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrMP$string$2", "symbols": [{"literal":"u"}, {"literal":"a"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "clrMP", "symbols": ["clrMP$subexpression$3", "clrMP$string$2"], "postprocess": d => 4},
    {"name": "clrMP$subexpression$4", "symbols": [/[qQ]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrMP$string$3", "symbols": [{"literal":"u"}, {"literal":"i"}, {"literal":"n"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "clrMP", "symbols": ["clrMP$subexpression$4", "clrMP$string$3"], "postprocess": d => 5},
    {"name": "clrMP$subexpression$5", "symbols": [/[sS]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrMP$string$4", "symbols": [{"literal":"e"}, {"literal":"p"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "clrMP", "symbols": ["clrMP$subexpression$5", "clrMP$string$4"], "postprocess": d => 7},
    {"name": "clrMP$subexpression$6", "symbols": [/[lL]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrMP", "symbols": ["clrMP$subexpression$6", {"literal":"e"}], "postprocess": d => 11},
    {"name": "clrMP", "symbols": ["clrGenPP", {"literal":"e"}], "postprocess": d => ["valueOf", d[0]]},
    {"name": "clrGenPP", "symbols": ["clrTens", "clrOnes"], "postprocess": (d,loc,_) => ["!clrGenPP", d[0] + d[1], loc]},
    {"name": "clrTens", "symbols": [], "postprocess": d => 10},
    {"name": "clrTens$subexpression$1", "symbols": [/[tT]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrTens$string$1", "symbols": [{"literal":"w"}, {"literal":"e"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "clrTens", "symbols": ["clrTens$subexpression$1", "clrTens$string$1"], "postprocess": d => 20},
    {"name": "clrTens$subexpression$2", "symbols": [/[tT]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrTens$string$2", "symbols": [{"literal":"h"}, {"literal":"i"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "clrTens", "symbols": ["clrTens$subexpression$2", "clrTens$string$2"], "postprocess": d => 30},
    {"name": "clrTens$subexpression$3", "symbols": [/[fF]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrTens", "symbols": ["clrTens$subexpression$3", {"literal":"o"}], "postprocess": d => 40},
    {"name": "clrTens$subexpression$4", "symbols": [/[fF]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrTens", "symbols": ["clrTens$subexpression$4", {"literal":"i"}], "postprocess": d => 50},
    {"name": "clrTens$subexpression$5", "symbols": [/[sS]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrTens", "symbols": ["clrTens$subexpression$5", {"literal":"i"}], "postprocess": d => 60},
    {"name": "clrOnes$subexpression$1", "symbols": [/[wW]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrOnes", "symbols": ["clrOnes$subexpression$1"], "postprocess": d => 1},
    {"name": "clrOnes$subexpression$2", "symbols": [/[tT]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrOnes", "symbols": ["clrOnes$subexpression$2", {"literal":"h"}], "postprocess": d => 3},
    {"name": "clrOnes$subexpression$3", "symbols": [/[sS]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrOnes", "symbols": ["clrOnes$subexpression$3"], "postprocess": d => 7},
    {"name": "clrOnes$subexpression$4", "symbols": [/[nN]/], "postprocess": function(d) {return d.join(""); }},
    {"name": "clrOnes", "symbols": ["clrOnes$subexpression$4"], "postprocess": d => 9},
    {"name": "degV0", "symbols": ["posInt"], "postprocess": d => parseInt(d[0])},
    {"name": "degV0", "symbols": [{"literal":"-"}, "posInt"], "postprocess": d => - parseInt(d[1])},
    {"name": "degV1$string$1", "symbols": [{"literal":"n"}, {"literal":"e"}, {"literal":"g"}, {"literal":"a"}, {"literal":"t"}, {"literal":"i"}, {"literal":"v"}, {"literal":"e"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "degV1", "symbols": ["__", "degV1$string$1", "__", "degV1Pos"], "postprocess": d => -d[3]},
    {"name": "degV1", "symbols": ["_", {"literal":"-"}, "_", "degOrdinal"], "postprocess": d => -d[3]},
    {"name": "degV1", "symbols": ["__", "degWord"], "postprocess": d => d[1]},
    {"name": "degV1", "symbols": ["_", "degOrdinal"], "postprocess": d => d[1]},
    {"name": "degV1", "symbols": ["_", "posInt"], "postprocess": d => parseInt(d[1])},
    {"name": "degV1", "symbols": ["_", {"literal":"-"}, "_", "posInt"], "postprocess": d => - parseInt(d[3])},
    {"name": "degV1Pos", "symbols": ["degWord"], "postprocess": id},
    {"name": "degV1Pos", "symbols": ["degOrdinal"], "postprocess": id},
    {"name": "degWord$string$1", "symbols": [{"literal":"u"}, {"literal":"n"}, {"literal":"i"}, {"literal":"s"}, {"literal":"o"}, {"literal":"n"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "degWord", "symbols": ["degWord$string$1"], "postprocess": d => 1},
    {"name": "degWord$string$2", "symbols": [{"literal":"o"}, {"literal":"c"}, {"literal":"t"}, {"literal":"a"}, {"literal":"v"}, {"literal":"e"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "degWord", "symbols": ["degWord$string$2"], "postprocess": d => 8},
    {"name": "degOrdinal$string$1", "symbols": [{"literal":"1"}, {"literal":"s"}, {"literal":"n"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "degOrdinal", "symbols": ["degOrdinal$string$1"], "postprocess": d => 1},
    {"name": "degOrdinal$string$2", "symbols": [{"literal":"8"}, {"literal":"v"}, {"literal":"e"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "degOrdinal", "symbols": ["degOrdinal$string$2"], "postprocess": d => 8},
    {"name": "degOrdinal", "symbols": ["ordinal"], "postprocess": d => parseInt(d[0])},
    {"name": "degV1Uniq$string$1", "symbols": [{"literal":"n"}, {"literal":"e"}, {"literal":"g"}, {"literal":"a"}, {"literal":"t"}, {"literal":"i"}, {"literal":"v"}, {"literal":"e"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "degV1Uniq", "symbols": ["degV1Uniq$string$1", "__", "degV1Pos"], "postprocess": d => -d[2]},
    {"name": "degV1Uniq", "symbols": ["degV1Pos"], "postprocess": id},
    {"name": "desc$string$1", "symbols": [{"literal":"d"}, {"literal":"e"}, {"literal":"s"}, {"literal":"c"}, {"literal":"."}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "desc", "symbols": ["desc$string$1", "__"]},
    {"name": "desc$string$2", "symbols": [{"literal":"d"}, {"literal":"e"}, {"literal":"s"}, {"literal":"c"}, {"literal":"e"}, {"literal":"n"}, {"literal":"d"}, {"literal":"i"}, {"literal":"n"}, {"literal":"g"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "desc", "symbols": ["desc$string$2", "__"]},
    {"name": "frcExpr1", "symbols": ["frcExpr1", "_", {"literal":"+"}, "_", "frcExpr2"], "postprocess": d => d[0].add(d[4])},
    {"name": "frcExpr1", "symbols": ["frcExpr1", "_", {"literal":"-"}, "_", "frcExpr2"], "postprocess": d => d[0].sub(d[4])},
    {"name": "frcExpr1", "symbols": ["frcExpr2"], "postprocess": id},
    {"name": "frcExpr2", "symbols": ["frcExpr2", "_", {"literal":"*"}, "_", "frcExpr3"], "postprocess": d => d[0].mul(d[4])},
    {"name": "frcExpr2", "symbols": ["frcExpr2", "_", {"literal":"/"}, "_", "locFrcExpr3"], "postprocess":  function(d) { try { return d[0].div(d[4][0]); }
        catch(err) {
          throw new OtherError("Division by zero", d[4][1])
        } } },
    {"name": "frcExpr2", "symbols": ["frcExpr3"], "postprocess": id},
    {"name": "frcExpr3", "symbols": [{"literal":"-"}, "_", "frcExpr4"], "postprocess": d => d[2].neg()},
    {"name": "frcExpr3", "symbols": ["frcExpr4"], "postprocess": id},
    {"name": "frcExpr4", "symbols": ["frcExpr5", "_", {"literal":"^"}, "_", "intExpr3"], "postprocess": d => d[0].pow(d[4])},
    {"name": "frcExpr4", "symbols": ["frcExpr5"], "postprocess": id},
    {"name": "frcExpr5", "symbols": ["nonNegInt"], "postprocess": d => Fraction(d[0])},
    {"name": "frcExpr5", "symbols": [{"literal":"("}, "_", "frcExpr1", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "locFrcExpr3", "symbols": ["frcExpr3"], "postprocess": (d,loc,_) => [d[0],loc]},
    {"name": "intExpr1", "symbols": ["intExpr1", "_", {"literal":"+"}, "_", "intExpr2"], "postprocess": d => d[0] + d[4]},
    {"name": "intExpr1", "symbols": ["intExpr1", "_", {"literal":"-"}, "_", "intExpr2"], "postprocess": d => d[0] - d[4]},
    {"name": "intExpr1", "symbols": ["intExpr2"], "postprocess": id},
    {"name": "intExpr2", "symbols": ["intExpr2", "_", {"literal":"*"}, "_", "intExpr3"], "postprocess": d => d[0] * d[4]},
    {"name": "intExpr2", "symbols": ["intExpr3"], "postprocess": id},
    {"name": "intExpr3", "symbols": [{"literal":"-"}, "_", "intExpr4"], "postprocess": d => - d[2]},
    {"name": "intExpr3", "symbols": ["intExpr4"], "postprocess": id},
    {"name": "intExpr4", "symbols": ["intExpr5", "_", {"literal":"^"}, "_", "posInt"], "postprocess": d => Math.pow(d[0],d[4])},
    {"name": "intExpr4", "symbols": ["intExpr5"], "postprocess": id},
    {"name": "intExpr5", "symbols": ["nonNegInt"], "postprocess": d => parseInt(d[0])},
    {"name": "intExpr5", "symbols": [{"literal":"("}, "_", "intExpr1", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "decExpr1", "symbols": ["decExpr1", "_", {"literal":"+"}, "_", "decExpr2"], "postprocess": d => d[0].add(d[4])},
    {"name": "decExpr1", "symbols": ["decExpr1", "_", {"literal":"-"}, "_", "decExpr2"], "postprocess": d => d[0].sub(d[4])},
    {"name": "decExpr1", "symbols": ["decExpr2"], "postprocess": id},
    {"name": "decExpr2", "symbols": ["decExpr2", "_", {"literal":"*"}, "_", "decExpr3"], "postprocess": d => d[0].mul(d[4])},
    {"name": "decExpr2", "symbols": ["decExpr2", "_", {"literal":"/"}, "_", "locDecExpr3"], "postprocess":  function(d) { try { return d[0].div(d[4][0]); }
        catch(err) {
          throw new OtherError("Division by zero", d[4][1])
        } } },
    {"name": "decExpr2", "symbols": ["decExpr3"], "postprocess": id},
    {"name": "decExpr3", "symbols": [{"literal":"-"}, "_", "decExpr4"], "postprocess": d => d[2].neg()},
    {"name": "decExpr3", "symbols": ["decExpr4"], "postprocess": id},
    {"name": "decExpr4", "symbols": ["decimal"], "postprocess": d => Fraction(d[0])},
    {"name": "decExpr4", "symbols": [{"literal":"("}, "_", "decExpr1", "_", {"literal":")"}], "postprocess": d => d[2]},
    {"name": "locDecExpr3", "symbols": ["decExpr3"], "postprocess": (d,loc,_) => [d[0],loc]},
    {"name": "posInt$ebnf$1", "symbols": []},
    {"name": "posInt$ebnf$1", "symbols": ["posInt$ebnf$1", /[0-9]/], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "posInt", "symbols": [/[1-9]/, "posInt$ebnf$1"], "postprocess": d => d[0] + d[1].join("")},
    {"name": "posIntSup$ebnf$1", "symbols": []},
    {"name": "posIntSup$ebnf$1", "symbols": ["posIntSup$ebnf$1", "sup09"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "posIntSup", "symbols": ["sup19", "posIntSup$ebnf$1"], "postprocess": d => d[0] + d[1].join("")},
    {"name": "sup09", "symbols": [{"literal":"⁰"}], "postprocess": d => "0"},
    {"name": "sup09", "symbols": ["sup19"], "postprocess": id},
    {"name": "sup19", "symbols": [{"literal":"¹"}], "postprocess": d => "1"},
    {"name": "sup19", "symbols": [{"literal":"²"}], "postprocess": d => "2"},
    {"name": "sup19", "symbols": [{"literal":"³"}], "postprocess": d => "3"},
    {"name": "sup19", "symbols": [{"literal":"⁴"}], "postprocess": d => "4"},
    {"name": "sup19", "symbols": [{"literal":"⁵"}], "postprocess": d => "5"},
    {"name": "sup19", "symbols": [{"literal":"⁶"}], "postprocess": d => "6"},
    {"name": "sup19", "symbols": [{"literal":"⁷"}], "postprocess": d => "7"},
    {"name": "sup19", "symbols": [{"literal":"⁸"}], "postprocess": d => "8"},
    {"name": "sup19", "symbols": [{"literal":"⁹"}], "postprocess": d => "9"},
    {"name": "posIntSub$ebnf$1", "symbols": []},
    {"name": "posIntSub$ebnf$1", "symbols": ["posIntSub$ebnf$1", "sub09"], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "posIntSub", "symbols": ["sub19", "posIntSub$ebnf$1"], "postprocess": d => d[0] + d[1].join("")},
    {"name": "sub09", "symbols": [{"literal":"₀"}], "postprocess": d => "0"},
    {"name": "sub09", "symbols": ["sub19"], "postprocess": id},
    {"name": "sub19", "symbols": [{"literal":"₁"}], "postprocess": d => "1"},
    {"name": "sub19", "symbols": [{"literal":"₂"}], "postprocess": d => "2"},
    {"name": "sub19", "symbols": [{"literal":"₃"}], "postprocess": d => "3"},
    {"name": "sub19", "symbols": [{"literal":"₄"}], "postprocess": d => "4"},
    {"name": "sub19", "symbols": [{"literal":"₅"}], "postprocess": d => "5"},
    {"name": "sub19", "symbols": [{"literal":"₆"}], "postprocess": d => "6"},
    {"name": "sub19", "symbols": [{"literal":"₇"}], "postprocess": d => "7"},
    {"name": "sub19", "symbols": [{"literal":"₈"}], "postprocess": d => "8"},
    {"name": "sub19", "symbols": [{"literal":"₉"}], "postprocess": d => "9"},
    {"name": "nonNegInt", "symbols": [{"literal":"0"}], "postprocess": _ => "0"},
    {"name": "nonNegInt", "symbols": ["posInt"], "postprocess": id},
    {"name": "int$ebnf$1", "symbols": [{"literal":"-"}], "postprocess": id},
    {"name": "int$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "int", "symbols": ["int$ebnf$1", "nonNegInt"], "postprocess": d => (d[0] || "") + d[1]},
    {"name": "decimal$ebnf$1", "symbols": [/[0-9]/]},
    {"name": "decimal$ebnf$1", "symbols": ["decimal$ebnf$1", /[0-9]/], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "decimal$ebnf$2$subexpression$1$ebnf$1", "symbols": []},
    {"name": "decimal$ebnf$2$subexpression$1$ebnf$1", "symbols": ["decimal$ebnf$2$subexpression$1$ebnf$1", /[0-9]/], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "decimal$ebnf$2$subexpression$1$ebnf$2$subexpression$1$ebnf$1", "symbols": [/[0-9]/]},
    {"name": "decimal$ebnf$2$subexpression$1$ebnf$2$subexpression$1$ebnf$1", "symbols": ["decimal$ebnf$2$subexpression$1$ebnf$2$subexpression$1$ebnf$1", /[0-9]/], "postprocess": function arrpush(d) {return d[0].concat([d[1]]);}},
    {"name": "decimal$ebnf$2$subexpression$1$ebnf$2$subexpression$1", "symbols": [{"literal":"("}, "decimal$ebnf$2$subexpression$1$ebnf$2$subexpression$1$ebnf$1", {"literal":")"}]},
    {"name": "decimal$ebnf$2$subexpression$1$ebnf$2", "symbols": ["decimal$ebnf$2$subexpression$1$ebnf$2$subexpression$1"], "postprocess": id},
    {"name": "decimal$ebnf$2$subexpression$1$ebnf$2", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "decimal$ebnf$2$subexpression$1", "symbols": [{"literal":"."}, "decimal$ebnf$2$subexpression$1$ebnf$1", "decimal$ebnf$2$subexpression$1$ebnf$2"]},
    {"name": "decimal$ebnf$2", "symbols": ["decimal$ebnf$2$subexpression$1"], "postprocess": id},
    {"name": "decimal$ebnf$2", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "decimal", "symbols": ["decimal$ebnf$1", "decimal$ebnf$2"], "postprocess":  d => d[0].join("") + (d[1] ? "." + d[1][1].join("")
              + (d[1][2] ? "("+d[1][2][1].join("")+")"
                         : "")
        : "") },
    {"name": "hertz$string$1", "symbols": [{"literal":"h"}, {"literal":"z"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "hertz", "symbols": ["hertz$string$1"]},
    {"name": "hertz$string$2", "symbols": [{"literal":"H"}, {"literal":"z"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "hertz", "symbols": ["hertz$string$2"]},
    {"name": "ordinal$string$1", "symbols": [{"literal":"1"}, {"literal":"s"}, {"literal":"t"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "ordinal", "symbols": ["ordinal$string$1"], "postprocess": d => "1"},
    {"name": "ordinal$string$2", "symbols": [{"literal":"2"}, {"literal":"n"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "ordinal", "symbols": ["ordinal$string$2"], "postprocess": d => "2"},
    {"name": "ordinal$string$3", "symbols": [{"literal":"3"}, {"literal":"r"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "ordinal", "symbols": ["ordinal$string$3"], "postprocess": d => "3"},
    {"name": "ordinal$string$4", "symbols": [{"literal":"t"}, {"literal":"h"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "ordinal", "symbols": [/[4-9]/, "ordinal$string$4"], "postprocess": d => d[0]},
    {"name": "ordinal$ebnf$1", "symbols": ["posInt"], "postprocess": id},
    {"name": "ordinal$ebnf$1", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "ordinal$string$5", "symbols": [{"literal":"t"}, {"literal":"h"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "ordinal", "symbols": ["ordinal$ebnf$1", {"literal":"1"}, /[0-9]/, "ordinal$string$5"], "postprocess": d => (d[0] || "") + "1" + d[2]},
    {"name": "ordinal$ebnf$2", "symbols": ["posInt"], "postprocess": id},
    {"name": "ordinal$ebnf$2", "symbols": [], "postprocess": function(d) {return null;}},
    {"name": "ordinal", "symbols": ["ordinal$ebnf$2", /[2-9]/, "ordinalOnesDigit"], "postprocess": d => (d[0] || "") + d[1] + d[2]},
    {"name": "ordinal", "symbols": ["posInt", {"literal":"0"}, "ordinalOnesDigit"], "postprocess": d => d[0] + "0" + d[2]},
    {"name": "ordinalOnesDigit$string$1", "symbols": [{"literal":"0"}, {"literal":"t"}, {"literal":"h"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "ordinalOnesDigit", "symbols": ["ordinalOnesDigit$string$1"], "postprocess": d => "0"},
    {"name": "ordinalOnesDigit$string$2", "symbols": [{"literal":"1"}, {"literal":"s"}, {"literal":"t"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "ordinalOnesDigit", "symbols": ["ordinalOnesDigit$string$2"], "postprocess": d => "1"},
    {"name": "ordinalOnesDigit$string$3", "symbols": [{"literal":"2"}, {"literal":"n"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "ordinalOnesDigit", "symbols": ["ordinalOnesDigit$string$3"], "postprocess": d => "2"},
    {"name": "ordinalOnesDigit$string$4", "symbols": [{"literal":"3"}, {"literal":"r"}, {"literal":"d"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "ordinalOnesDigit", "symbols": ["ordinalOnesDigit$string$4"], "postprocess": d => "3"},
    {"name": "ordinalOnesDigit$string$5", "symbols": [{"literal":"t"}, {"literal":"h"}], "postprocess": function joiner(d) {return d.join('');}},
    {"name": "ordinalOnesDigit", "symbols": [/[4-9]/, "ordinalOnesDigit$string$5"], "postprocess": d => d[0]}
]
  , ParserStart: "top1"
}
if (typeof module !== 'undefined'&& typeof module.exports !== 'undefined') {
   module.exports = grammar;
} else {
   window.grammar = grammar;
}
})();

},{"../edo.js":3,"../fjs.js":5,"../interval.js":7,"../pythagorean.js":11,"./eval.js":9,"fraction.js":16}],11:[function(require,module,exports){
/**
 * Functions for working with pythagorean and neutral pythagorean intervals
 * @copyright 2021 Matthew Yacavone (matthew [at] yacavone [dot] net)
 * @module pythagorean
 **/

const {sign1, mod} = require('./utils.js');
const pf = require('primes-and-factors');
const ntw = require('number-to-words');
const Fraction = require('fraction.js');
const Interval = require('./interval.js');

/**
  * Constructs an interval from a pythagorean degree and offset
  *
  * @param {integer} d
  * @param {Fraction} o
  * @returns {Interval}
  */
function pyInterval(d,a,b) {
  if (d == 0) {
    throw new Error("Pythagorean interval cannot have a degree of zero")
  }
  const ox4 = Fraction(a,b).mul(4 * Math.sign(d));
  if (ox4.d != 1) {
    throw new Error("offset does not have denominator 1, 2, or 4");
  }
  const zd = d - Math.sign(d);
  const ng = mod(zd * 4 + 3, 7) - 3;
  const g = ng * 2 + ox4.s * ox4.n * 7;
  return Interval({ 2: Fraction(g,4).sub((zd - g) / 7).neg(),
                    3: Fraction(g,4) });
}

/**
  * A pythagorean augmented unison, `pyInterval(1,1)`
  *
  * @constant {number}
  */
const pyA1 = pyInterval(1,1);

/**
  * Checks whether the given interval is pythagorean
  *
  * @param {Interval} i
  * @returns {boolean}
  */
function isPythagorean(a,b) {
  const i = new Interval(a,b);
  return i.inPrimeLimit(3)
         && i.expOf(3).mul(4).d == 1
         && i.expOf(2).add(i.expOf(3)).d == 1;
}

/**
  * For a given pythagorean interval `(3/2)^(g/4) * 2^p`, returns the `g`.
  *
  * @param {Interval} i
  * @returns {integer}
  */
function pyGenerator(a,b) {
  const i = new Interval(a,b);
  const g = i.expOf(3).mul(4);
  if (g.d != 1) {
    throw new Error("interval is not pythagorean");
  }
  return g.s * g.n;
}

/**
  * For a given pythagorean interval `(3/2)^(g/4) * 2^p`, returns the `p`.
  *
  * @param {Interval} i
  * @returns {integer}
  */
function pyOctaves(a,b) {
  const i = new Interval(a,b);
  const p = i.expOf(2).add(i.expOf(3));
  if (p.d != 1) {
    throw new Error("interval is not pythagorean");
  }
  return p.s * p.n;
}

/**
  * Returns the degree of the given pythagorean interval
  *
  * @param {Interval} i
  * @returns {integer}
  */
function pyDegree(a,b) {
  const zd = pyZDegree(a,b);
  return zd + sign1(zd);
}

/**
  * Returns the "zeroed" degree of the given pythagorean interval
  *
  * @param {Interval} i
  * @returns {integer}
  */
function pyZDegree(a,b) {
  const i = new Interval(a,b);
  const g = pyGenerator(i);
  const p = pyOctaves(i);
  return g + p * 7;
}

/**
  * Returns the offset of the given pythagorean interval
  *
  * @param {Interval} i
  * @returns {Fraction}
  */
function pyOffset(a,b) {
  const i = new Interval(a,b);
  const g = pyGenerator(i);
  const p = pyOctaves(i);
  const zd = g + p * 7;
  return Fraction(sign1(zd) * (2 * Math.floor((4 * g + 3) / 7) - g), 4);
}

/**
  * Reduces a pythagorean degree so it lies between 1 and 7
  *
  * @param {integer} d
  * @returns {integer}
  */
function pyRedDeg(d) {
  return mod(d - Math.sign(d), 7) + 1;
}

/**
  * Checks whether a given degree (of a pythagorean interval) is a unison,
  * fourth, or fifth
  *
  * @param {integer} d
  * @returns {boolean}
  */
function isPerfectDeg(d) {
  return pyRedDeg(d) == 1 || pyRedDeg(d) == 4 || pyRedDeg(d) == 5;
}

function case2(n, a, b) {
  if (n == 0 || !n) { return a; }
  return b;
}

function case3(n, a, b, c) {
  if (n == 0 || !n) { return a; }
  if (n == 1) { return b; }
  return c;
}

/**
  * Returns the quality of the given pythagorean interval
  *
  * @param {Interval} i
  * @param {{verbosity: integer}=} opts verbosity can be the default 0
  *                                     (e.g. "d"), 1 (e.g. "dim"), or 2
  *                                     (e.g. "diminished")
  * @returns {string}
  */
function pyQuality(a,b, opts) {
  // if only two arguments are given, the second one may be `opts`!
  if (!opts && typeof b == 'object' && b != null) {
      opts = b;
      b = undefined;
  }
  const {verbosity} = opts || {};
  let o = pyOffset(a,b);
  if (isPerfectDeg(pyDegree(a,b))) {
    if (o == 0    ) { return case2(verbosity, "P", "perfect"); }
  }
  else {
    if (o == 0    ) { return case2(verbosity, "n", "neutral"); }
    if (o == 0.25 ) { return case2(verbosity, "sM", "semi-major"); }
    if (o == 0.5  ) { return case2(verbosity, "M", "major"); }
    if (o == -0.25) { return case2(verbosity, "sm", "semi-minor"); }
    if (o == -0.5 ) { return case2(verbosity, "m", "minor"); }
    o = o.sub(o.s,2);
  }
  if (o == 0.5 ) { return case3(verbosity, "sA", "semi-aug", "semi-augmented"); }
  if (o == 1   ) { return case3(verbosity, "A", "aug", "augmented"); }
  if (o == -0.5) { return case3(verbosity, "sd", "semi-dim", "semi-diminished"); }
  if (o == -1  ) { return case3(verbosity, "d", "dim", "diminished"); }
  if (o ==  2  ) { return case3(verbosity, "AA", "2-aug", "doubly augmented"); }
  if (o == -2  ) { return case3(verbosity, "dd", "2-dim", "doubly diminished"); }
  if (o > 0 && o.d == 1) { return o.n + case3(verbosity, "A", "-aug", "-augmented"); }
  if (o > 0 && o.d != 1) { return o.toFraction() + case3(verbosity, "-A", "-aug", "-augmented"); }
  if (o < 0 && o.d == 1) { return o.n + case3(verbosity, "d", "-dim", "-diminished"); }
  if (o < 0 && o.d != 1) { return o.neg().toFraction() + case3(verbosity, "-d", "-dim", "-diminished"); }
}

function pyDegreeString(d, opts) {
  const {verbosity, useWordNegative} = opts || {};
  if (verbosity == 0 || !verbosity) {
    return d;
  }
  if (verbosity == 1) {
    const neg_str = d < 0 ? useWordNegative ? "negative " : "-" : "";
    if (Math.abs(d) == 1) { return neg_str + "1sn"; }
    if (Math.abs(d) == 8) { return neg_str + "8ve"; }
    return neg_str + ntw.toOrdinal(Math.abs(d));
  }
  const neg_str = d < 0 ? "negative " : "";
  if (Math.abs(d) == 1) { return neg_str + "unison"; }
  if (Math.abs(d) == 8) { return neg_str + "octave"; }
  return neg_str + ntw.toWordsOrdinal(Math.abs(d));
}

/**
  * Returns the symbol of the given pythagorean interval
  *
  * @param {Interval} i
  * @param {Object} opts
  * @param {integer=} opts.verbosity can be the default 0 (e.g. "d2"), 1
  *                                  (e.g. "dim 2nd"), or 2
  *                                  (e.g. "diminished second")
  * @param {boolean=} opts.useWordNegative defaults to false
  * @param {boolean=} opts.useWordDesc defaults to false
  * @param {boolean=} opts.useDescSuffix defaults to false
  * @returns {string}
  */
function pySymb(a,b, opts) {
  // if only two arguments are given, the second one may be `opts`!
  if (!opts && typeof b == 'object' && b != null) {
      opts = b;
      b = undefined;
  }
  const {verbosity, useWordNegative, useWordDesc, useDescSuffix} = opts || {};
  const d = pyDegree(a,b);
  const d_str = case2(verbosity, "", " ") +
                pyDegreeString(verbosity && useWordDesc ? Math.abs(d) : d, opts);
  let [desc_prefix, desc_suffix] = ["", ""];
  if (useWordDesc && d < 0) {
    if (verbosity && useDescSuffix) { desc_suffix = " (descending)"; }
    else { desc_prefix = verbosity == 0 ? "desc. " : "descending " }
  }
  return desc_prefix + pyQuality(a,b, opts) + d_str + desc_suffix;
}

/**
  * Returns the interval to A of the given base note name (i.e. A, B, C, D, E,
  * F or G) within a single octave of scientific pitch notation
  *
  * @param {string} baseNote
  * @returns {Interval}
  */
function baseNoteIntvToA(x) {
  if (x == "C") { return pyInterval(-6, 0.5) /* M6 down */ }
  if (x == "D") { return pyInterval(-5, 0)   /* P5 down */ }
  if (x == "E") { return pyInterval(-4, 0)   /* P4 down */ }
  if (x == "F") { return pyInterval(-3, 0.5) /* M3 down */ }
  if (x == "G") { return pyInterval(-2, 0.5) /* M2 down */ }
  if (x == "A") { return Interval(1)         /* P1 */      }
  if (x == "B") { return pyInterval(2, 0.5)  /* M2 */      }
}

/**
  * Returns the octave in scientific pitch notation of the given interval to A4
  *
  * @param {Interval} intvToA4
  * @returns {integer}
  */
function octaveOfIntvToA4(a,b) {
  const intvToA4 = Interval(a,b);
  const intvToC4 = intvToA4.div(baseNoteIntvToA("C"));
  return 4 + Math.floor(intvToC4.valueOf_log(2));
}

/**
  * Returns the note name of the given non-neutral pythagorean interval to A4.
  * The returned string uses ASCII instead of uniode wherever possible iff the
  * second argument is given and is true
  *
  * @param {Interval} intvToA4
  * @param {Object} [opts]
  * @param {boolean} [opts.ignoreOctave] defaults to false
  * @param {boolean} [opts.useASCII] defaults to false
  * @returns {string}
  */
function pyNote(intvToA4, opts) {
  const {ignoreOctave, useASCII} = opts || {};
  const intvToF4 = Interval(intvToA4).div(baseNoteIntvToA("F"));
  if (!isPythagorean(intvToF4) || (intvToF4['3'] && intvToF4['3'].d != 1)) {
    throw new Error("interval is not a non-neutral pythagorean interval");
  }
  const e3 = intvToF4.expOf(3).s * intvToF4.expOf(3).n;
  const zd = mod(4*e3, 7);
  let o = Math.floor(e3 / 7);

  let octave = octaveOfIntvToA4(intvToA4);
  if (ignoreOctave || octave == 4) { octave = ""; }

  let baseNote;
  if (zd == 0) { baseNote = "F"; }
  if (zd == 1) { baseNote = "G"; }
  if (zd == 2) { baseNote = "A"; }
  if (zd == 3) { baseNote = "B"; }
  if (zd == 4) { baseNote = "C"; }
  if (zd == 5) { baseNote = "D"; }
  if (zd == 6) { baseNote = "E"; }

  let accidentals = "";
  if (o == 0 && baseNote == "A" && octave != "") {
    accidentals += "♮";
  }
  while (o > 1) {
    accidentals += useASCII ? "X" : "𝄪";
    o -= 2;
  }
  if (o == 1) {
    accidentals += useASCII ? "#" : "♯";
  }
  while (o < -1) {
    if (useASCII) {
      accidentals += "b";
      o += 1;
    } else {
      accidentals += "𝄫";
      o += 2;
    }
  }
  if (o == -1) {
    accidentals += useASCII ? "b" : "♭";
  }

  return baseNote + accidentals + octave;
}

module['exports'].pyInterval = pyInterval;
module['exports'].pyA1 = pyA1;
module['exports'].isPythagorean = isPythagorean;
module['exports'].pyGenerator = pyGenerator;
module['exports'].pyOctaves = pyOctaves;
module['exports'].pyDegree = pyDegree;
module['exports'].pyZDegree = pyZDegree;
module['exports'].pyOffset = pyOffset;
module['exports'].pyRedDeg = pyRedDeg;
module['exports'].isPerfectDeg = isPerfectDeg;
module['exports'].pyQuality = pyQuality;
module['exports'].pyDegreeString = pyDegreeString;
module['exports'].pySymb = pySymb;
module['exports'].baseNoteIntvToA = baseNoteIntvToA;
module['exports'].octaveOfIntvToA4 = octaveOfIntvToA4;
module['exports'].pyNote = pyNote;

},{"./interval.js":7,"./utils.js":13,"fraction.js":16,"number-to-words":19,"primes-and-factors":20}],12:[function(require,module,exports){
/**
 * Generators for sets of intervals
 * @copyright 2021 Matthew Yacavone (matthew [at] yacavone [dot] net)
 * @module sets
 **/

const {cachedLog2} = require('./utils.js');
const Fraction = require('fraction.js');
const Interval = require('./interval.js');

// For a given interval with factorization `p1^e1 ... pm^em` (where `pk` is
// prime and `ek > 0` for all `k`), `signPerms(intv)` is the array of all
// intervals with factorizations `p1^(+/- e1) ... pm^(+/- em)`. For example, if
// `i = 45` then `i = 3^2 * 5^1` and
// `signPerms(i) = [ 3^2 * 5^1, 3^(-2) * 5^1, 3^2 * 5^(-1), 3^(-2) * 5(-1) ]`.
// Note that we also include the log2 values of each interval as well.
function* signPerms(intv) {
  const intv_fact = intv.factors();
  for (let bits = 0; bits < (1 << intv_fact.length); bits++) {
    let [i, fact, logval] = [0, {}, 0];
    for (const [p,e] of intv_fact) {
      fact[p] = e.mul((bits & (1 << i)) == 0 ? 1 : -1);
      logval += fact[p].valueOf() * cachedLog2(p);
      i++;
    }
    yield [Interval(fact), logval];
  }
}

/**
  * A helper function for generating ratios by no-2s Benedetti/Tenney height.
  *
  * @param {integer} startOdd the no-2s Benedetti height to start with (inclusive)
  * @param {integer} endOdd the no-2s Benedetti height to end with (exclusive)
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @yields {Pair.<Interval, Iterable.<Pair.<Interval, integer>>>}
  */
function* ratioPermsByNo2sHeight(startOdd, endOdd, opts) {
  if (startOdd == undefined || startOdd < 1 || endOdd < -1) {
    throw new Error("Invalid arguments to ratiosByNo2sHeight: startOdd = " + start + ", endOdd = " + end);
  }
  const start = Math.ceil((startOdd-1)/2);
  const end = Math.floor((endOdd-1)/2);
  if (opts == undefined) { opts = {}; }
  const {primeLimit} = opts;
  for (let h = start; !isFinite(end) || h < end; h++) {
    const i = Interval(2*h + 1);
    if (primeLimit && !i.inPrimeLimit(primeLimit)) {
      continue;
    }
    yield [i, signPerms(i)];
  }
}

/**
  * Generates ratios between 1 and 2 sorted by the Benedetti height of the
  * ratio with all factors of 2 removed (or equivalently, the Tenney height of
  * the ratio with all factors of 2 removed). To specify `start` and `end`
  * using Tenney height, use `2 ** tenneyStart` and `2 ** tenneyEnd`.
  *
  * @param {integer} start the no-2s Benedetti height to start with (inclusive)
  * @param {integer} end the no-2s Benedetti height to end with (exclusive)
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @yields {Fraction}
  */
function* redRatiosByNo2sHeight(start, end, opts) {
  const {oddLimit} = opts == undefined ? {} : opts;
  for (const [i, perms] of ratioPermsByNo2sHeight(start, end, opts)) {
    for (const [j_no2s, j_no2s_logval] of perms) {
      const j = j_no2s.red();
      if (oddLimit && !j.inOddLimit(oddLimit)) {
        continue;
      }
      yield j.toFrac();
    }
  }
}

/**
  * Generates ratios between 1/sqrt(2) and sqrt(2) sorted by the Benedetti
  * height of the ratio with all factors of 2 removed (or equivalently, the
  * Tenney height of the ratio with all factors of 2 removed). To specify
  * `start` and `end` using Tenney height, use `2 ** tenneyStart` and
  * `2 ** tenneyEnd`.
  *
  * @param {integer} start the no-2s Benedetti height to start with (inclusive)
  * @param {integer} end the no-2s Benedetti height to end with (exclusive)
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @yields {Fraction}
  */
function* rebRatiosByNo2sHeight(start, end, opts) {
  const {oddLimit} = opts == undefined ? {} : opts;
  for (const [i, perms] of ratioPermsByNo2sHeight(start, end, opts)) {
    for (const [j_no2s, j_no2s_logval] of perms) {
      const j = j_no2s.reb();
      if (oddLimit && !j.inOddLimit(oddLimit)) {
        continue;
      }
      yield j.toFrac();
    }
  }
}

/**
  * A helper function for generating ratios by Benedetti/Tenney height.
  *
  * @param {integer} start the Benedetti height to start with (inclusive)
  * @param {integer} end the Benedetti height to end with (exclusive)
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @param {integer} [opts.oddLimit]
  * @yields {Pair.<Interval, Iterable.<Pair.<Interval, integer>>>}
  */
function* ratioPermsByHeight(start, end, opts) {
  if (start == undefined || start < 1 || end < -1) {
    throw new Error("Invalid arguments to ratiosByHeight: start = " + start + ", end = " + end);
  }
  if (opts == undefined) { opts = {}; }
  let {primeLimit, oddLimit} = opts;
  for (let h = Math.ceil(start); !isFinite(end) || h < end; h++) {
    const i = Interval(h);
    if (primeLimit && !i.inPrimeLimit(primeLimit)) {
      continue;
    }
    function* perms() {
      for (const [j, j_logval] of signPerms(i)) {
        if (oddLimit && !j.inOddLimit(oddLimit)) {
          continue;
        }
        yield [j, j_logval];
      }
    }
    yield [i, perms()];
  }
}

/**
  * Generates ratios sorted by the Benedetti height of the ratio (or
  * equivalently, the Tenney height of the ratio). To specify `start` and `end`
  * using Tenney height, use `2 ** tenneyStart` and `2 ** tenneyEnd`.
  *
  * @param {integer} start the Benedetti height to start with (inclusive)
  * @param {integer} end the Benedetti height to end with (exclusive)
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @yields {Fraction}
  */
function* ratiosByHeight(start, end, opts) {
  for (const [i, perms] of ratioPermsByHeight(start, end, opts)) {
    for (const [j, j_logval] of perms) {
      yield j.toFrac();
    }
  }
}

/**
  * Generates all ratios with the given denominator in the given range [lo, hi],
  * or between 1 and 2 if no range is given, sorted by value.
  *
  * @param {integer} d
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @param {integer} [opts.oddLimit]
  * @param {Interval} [opts.lo] defaults to 1
  * @param {Interval} [opts.hi] defaults to 2
  * @yields {Fraction}
  */
function* ratiosWithDenom(d, opts) {
  if (!isFinite(d) || d < 1) {
    throw new Error("Invalid argument to ratiosWithDenom: d = " + d);
  }
  if (opts == undefined) { opts = {}; }
  let {primeLimit, oddLimit, lo, hi} = opts;
  lo = Interval(lo == undefined ? 1 : lo);
  hi = Interval(hi == undefined ? 2 : hi);
  if (oddLimit && d % 2 != 0 && d > oddLimit) {
    return;
  }
  const nLo = Math.ceil(lo.mul(d).valueOf());
  const nHi = Math.floor(hi.mul(d).valueOf());
  for (let n = nLo; n <= nHi; n++) {
    const r = Fraction(n,d);
    // if n/d reduces, we've seen it already - so we can safely skip
    if (r.d != d) {
      continue;
    }
    if (oddLimit && r.n % 2 != 0 && r.n > oddLimit) {
      continue;
    }
    if (primeLimit && !Interval(r).inPrimeLimit(primeLimit)) {
      continue;
    }
    yield r;
  }
}

/**
  * Generates all ratios with the given numerator in the given range [lo, hi],
  * or between 1 and 2 if no range is given, sorted by value.
  *
  * @param {integer} n
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @param {integer} [opts.oddLimit]
  * @param {Interval} [opts.lo] defaults to 1
  * @param {Interval} [opts.hi] defaults to 2
  * @yields {Fraction}
  */
function* ratiosWithNumer(n, opts) {
  if (!isFinite(n) || n < 1) {
    throw new Error("Invalid argument to ratiosWithNumer: n = " + n);
  }
  if (opts == undefined) { opts = {}; }
  let {primeLimit, oddLimit, lo, hi} = opts;
  lo = Interval(lo == undefined ? 1 : lo);
  hi = Interval(hi == undefined ? 2 : hi);
  if (oddLimit && n % 2 != 0 && n > oddLimit) {
    return;
  }
  const dLo = Math.ceil(hi.recip().mul(n).valueOf());
  const dHi = Math.floor(lo.recip().mul(n).valueOf());
  for (let d = dHi; d >= dLo; d--) {
    const r = Fraction(n,d);
    // if n/d reduces, we've seen it already - so we can safely skip
    if (r.n != n) {
      continue;
    }
    if (oddLimit && r.d % 2 != 0 && r.d > oddLimit) {
      continue;
    }
    if (primeLimit && !Interval(r).inPrimeLimit(primeLimit)) {
      continue;
    }
    yield r;
  }
}

/**
  * Generates all ratios with denominators in the given range [start, end] with
  * values in the given range [lo, hi], or between 1 and 2 if no range is given,
  * sorted by denominator.
  *
  * @param {integer} start the lowest denominator to include (inclusive)
  * @param {integer} end the highest denominator to include (inclusive)
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @param {integer} [opts.oddLimit]
  * @param {Interval} [opts.lo] defaults to 1
  * @param {Interval} [opts.hi] defaults to 2
  * @yields {Fraction}
  */
function* ratiosByDenom(start, end, opts) {
  if (start == undefined || start < 1 || end < -1) {
    throw new Error("Invalid arguments to ratiosByDenom: start = " + start + ", end = " + end);
  }
  if (opts == undefined) { opts = {}; }
  let {primeLimit, oddLimit, lo, hi} = opts;
  lo = Interval(lo == undefined ? 1 : lo);
  hi = Interval(hi == undefined ? 2 : hi);
  for (let d = start; !isFinite(end) || d < end; d++) {
    for (const r of ratiosWithDenom(d, opts)) {
      yield r;
    }
  }
}

/**
  * Generates all ratios with numerators in the given range [start, end] with
  * values in the given range [lo, hi], or between 1 and 2 if no range is given,
  * sorted by numerator.
  *
  * @param {integer} start the lowest numerator to include (inclusive)
  * @param {integer} end the highest numerator to include (inclusive)
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @param {integer} [opts.oddLimit]
  * @param {Interval} [opts.lo] defaults to 1
  * @param {Interval} [opts.hi] defaults to 2
  * @yields {Fraction}
  */
function* ratiosByNumer(start, end, opts) {
  if (start == undefined || start < 1 || end < -1) {
    throw new Error("Invalid arguments to ratiosByNumer: start = " + start + ", end = " + end);
  }
  if (opts == undefined) { opts = {}; }
  let {primeLimit, oddLimit, lo, hi} = opts;
  lo = Interval(lo == undefined ? 1 : lo);
  hi = Interval(hi == undefined ? 2 : hi);
  for (let n = start; !isFinite(end) || n < end; n++) {
    for (const r of ratiosWithNumer(n, opts)) {
      yield r;
    }
  }
}

/**
  * Generates all ratios with denominators in the given range [start, end] with
  * values in the given range [lo, hi], or between 1 and 2 if no range is given,
  * sorted by value.
  *
  * @param {integer} start the lowest denominator to include (inclusive)
  * @param {integer} end the highest denominator to include (inclusive)
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @param {integer} [opts.oddLimit]
  * @param {Interval} [opts.lo] defaults to 1
  * @param {Interval} [opts.hi] defaults to 2
  * @yields {Fraction}
  */
function* ratiosByDenomSorted(start, end, opts) {
  if (start == undefined || start < 1 || end < -1) {
    throw new Error("Invalid arguments to ratiosByDenom: start = " + start + ", end = " + end);
  }
  if (opts == undefined) { opts = {}; }
  let {primeLimit, oddLimit, lo, hi} = opts;
  lo = Interval(lo == undefined ? 1 : lo);
  hi = Interval(hi == undefined ? 2 : hi);
  let ret = [];
  for (let d = start; !isFinite(end) || d < end; d++) {
    let i = 0;
    for (const r of ratiosWithDenom(d, opts)) {
      let added = false;
      for (; !added && i < ret.length; i++) {
        if (r.compare(ret[i]) < 0) {
          ret.splice(i, 0, r);
          added = true;
        }
      }
      if (!added) {
        ret.push(r);
      }
    }
  }
  for (const r of ret) {
    yield r;
  }
}

/**
  * Generates all ratios with numerators in the given range [start, end] with
  * values in the given range [lo, hi], or between 1 and 2 if no range is given,
  * sorted by numerator.
  *
  * @param {integer} start the lowest numerator to include (inclusive)
  * @param {integer} end the highest numerator to include (inclusive)
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @param {integer} [opts.oddLimit]
  * @param {Interval} [opts.lo] defaults to 1
  * @param {Interval} [opts.hi] defaults to 2
  * @yields {Fraction}
  */
function* ratiosByNumerSorted(start, end, opts) {
  if (start == undefined || start < 1 || end < -1) {
    throw new Error("Invalid arguments to ratiosByDenom: start = " + start + ", end = " + end);
  }
  if (opts == undefined) { opts = {}; }
  let {primeLimit, oddLimit, lo, hi} = opts;
  lo = Interval(lo == undefined ? 1 : lo);
  hi = Interval(hi == undefined ? 2 : hi);
  let ret = [];
  for (let n = start; !isFinite(end) || n < end; n++) {
    let i = 0;
    for (const r of ratiosWithNumer(n, opts)) {
      let added = false;
      for (; !added && i < ret.length; i++) {
        if (r.compare(ret[i]) < 0) {
          ret.splice(i, 0, r);
          added = true;
        }
      }
      if (!added) {
        ret.push(r);
      }
    }
  }
  for (const r of ret) {
    yield r;
  }
}

/**
  * Generates all ratios in the given odd limit which are not in the previous
  * odd limit with values in the given range [lo, hi], or between 1 and 2 if no
  * range is given, sorted by value unless `opts.unsorted` is given and true.
  *
  * @param {integer} oddLimit
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @param {Interval} [opts.lo] defaults to 1
  * @param {Interval} [opts.hi] defaults to 2
  * @param {boolean} [opts.unsorted] defaults to false
  * @yields {Fraction}
  */
function* newRatiosInOddLimit(oddLimit, opts) {
  if (oddLimit == undefined || oddLimit % 2 == 0 || oddLimit < 1) {
    throw new Error("Invalid argument to newRatiosInOddLimit: oddLimit = " + oddLimit);
  }
  if (opts == undefined) { opts = {}; }
  let {unsorted} = opts;
  const ropts = Object.assign({}, opts, {oddLimit: oddLimit, unsorted: undefined});
  let ret = [];
  // ratios with denominator = oddLimit
  for (const r of ratiosWithDenom(oddLimit, ropts)) {
    if (unsorted) {
      yield r;
    }
    else {
      ret.push(r);
    }
  }
  // ratios with numerator = oddLimit
  let i = 0;
  for (const r of ratiosWithNumer(oddLimit, ropts)) {
    // if oddLimit == 1, don't add 1/1 twice!
    if (r.equals(1)) {
      continue;
    }
    if (unsorted) {
      yield r;
    }
    else {
      let added = false;
      for (; !added && i < ret.length; i++) {
        if (r.compare(ret[i]) < 0) {
          ret.splice(i, 0, r);
          added = true;
        }
      }
      if (!added) {
        ret.push(r);
      }
    }
  }
  if (!unsorted) {
    for (const r of ret) {
      yield r;
    }
  }
}

/**
  * Generates all ratios in the given odd limit with values in the given range
  * [lo, hi], or between 1 and 2 if no range is given, sorted by minimum odd
  * limit.
  *
  * @param {integer} oddLimit
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @param {Interval} [opts.lo] defaults to 1
  * @param {Interval} [opts.hi] defaults to 2
  * @param {boolean} [opts.unsorted] whether or not to sort the intervals
                                     within each minimum odd limit (see
                                     `newRatiosInOddLimit`), defaults to false
  * @yields {Fraction}
  */
function* ratiosInOddLimit(oddLimit, opts) {
  if (opts == undefined) { opts = {}; }
  let {primeLimit, lo, hi} = opts;
  lo = Interval(lo == undefined ? 1 : lo);
  hi = Interval(hi == undefined ? 2 : hi);
  for (let o = 1; o <= oddLimit; o += 2) {
    for (const r of newRatiosInOddLimit(o, opts)) {
      yield r;
    }
  }
}

/**
  * Generates all ratios in the given odd limit with values in the given range
  * [lo, hi], or between 1 and 2 if no range is given, sorted by value.
  *
  * @param {integer} oddLimit
  * @param {Object} [opts]
  * @param {integer} [opts.primeLimit]
  * @param {Interval} [opts.lo] defaults to 1
  * @param {Interval} [opts.hi] defaults to 2
  * @yields {Fraction}
  */
function* ratiosInOddLimitSorted(oddLimit, opts) {
  if (opts == undefined) { opts = {}; }
  let {primeLimit, lo, hi} = opts;
  lo = Interval(lo == undefined ? 1 : lo);
  hi = Interval(hi == undefined ? 2 : hi);
  let ret = []
  for (let o = 1; o <= oddLimit; o += 2) {
    let i = 0;
    for (const r of newRatiosInOddLimit(o, Object.assign({}, opts, {unsorted: false}))) {
      let added = false;
      for (; !added && i < ret.length; i++) {
        if (r.compare(ret[i]) < 0) {
          ret.splice(i, 0, r);
          added = true;
        }
      }
      if (!added) {
        ret.push(r);
      }
    }
  }
  for (const r of ret) {
    yield r;
  }
}

module.exports.ratioPermsByNo2sHeight = ratioPermsByNo2sHeight;
module.exports.redRatiosByNo2sHeight = redRatiosByNo2sHeight;
module.exports.rebRatiosByNo2sHeight = rebRatiosByNo2sHeight;
module.exports.ratioPermsByHeight = ratioPermsByHeight;
module.exports.ratiosByHeight = ratiosByHeight;
module.exports.ratiosWithDenom = ratiosWithDenom;
module.exports.ratiosWithNumer = ratiosWithNumer;
module.exports.ratiosByDenom = ratiosByDenom;
module.exports.ratiosByNumer = ratiosByNumer;
module.exports.ratiosByDenomSorted = ratiosByDenomSorted;
module.exports.ratiosByNumerSorted = ratiosByNumerSorted;
module.exports.newRatiosInOddLimit = newRatiosInOddLimit;
module.exports.ratiosInOddLimit = ratiosInOddLimit;
module.exports.ratiosInOddLimitSorted = ratiosInOddLimitSorted;

},{"./interval.js":7,"./utils.js":13,"fraction.js":16}],13:[function(require,module,exports){

const pf = require('primes-and-factors');
const Fraction = require('fraction.js');

// a version of Math.sign which returns 1 for the input 0
function sign1(x) {
  return x == 0 ? 1 : Math.sign(x);
}

// a version of % where the result is always between 1 and n
function mod(a,n) {
  return ((a % n) + n) % n;
}

// get the fractional part (between -0.5 and 0.5) of a number
function fractionalPart(n) {
  const nSplit = (n+"").split(".");
  const decimalPlaces = nSplit.length > 1 ? nSplit[1].length : 0;
  return (n - Math.round(n)).toFixed(decimalPlaces);
}

let cached_logs = {}
function cachedLog2(i) {
  if (i % 1 != 0) {
    return Math.log2(i)
  }
  let entry = cached_logs[i];
  if (entry == undefined) {
    entry = Math.log2(i);
    cached_logs[i] = entry;
  }
  return entry;
}

function unBigFraction(fr) {
  return Fraction(Number(fr.s * fr.n), Number(fr.d));
}

function maxKey(a) {
  let max = -Infinity;
  for (const i in a) {
    max = Math.max(i, max);
  }
  return max;
}

function* keys(a, b) {
  for (const i in a) {
    yield i;
  }
  for (const i in b) {
    if (a[i] == undefined) {
      yield i;
    }
  }
}

function* primes() {
  yield* [2,3,5,7,11,13,17,19,23];
  for (let i = 29; true; i += 6) {
    if (pf.isPrime(i)) { yield i; }
    if (pf.isPrime(i + 2)) { yield (i + 2); }
  }
}

module.exports.sign1 = sign1;
module.exports.mod = mod;
module.exports.fractionalPart = fractionalPart;
module.exports.cachedLog2 = cachedLog2;
module.exports.unBigFraction = unBigFraction;
module.exports.maxKey = maxKey;
module.exports.keys = keys;
module.exports.primes = primes;

},{"fraction.js":16,"primes-and-factors":20}],14:[function(require,module,exports){
var bigInt = (function (undefined) {
    "use strict";

    var BASE = 1e7,
        LOG_BASE = 7,
        MAX_INT = 9007199254740992,
        MAX_INT_ARR = smallToArray(MAX_INT),
        DEFAULT_ALPHABET = "0123456789abcdefghijklmnopqrstuvwxyz";

    var supportsNativeBigInt = typeof BigInt === "function";

    function Integer(v, radix, alphabet, caseSensitive) {
        if (typeof v === "undefined") return Integer[0];
        if (typeof radix !== "undefined") return +radix === 10 && !alphabet ? parseValue(v) : parseBase(v, radix, alphabet, caseSensitive);
        return parseValue(v);
    }

    function BigInteger(value, sign) {
        this.value = value;
        this.sign = sign;
        this.isSmall = false;
    }
    BigInteger.prototype = Object.create(Integer.prototype);

    function SmallInteger(value) {
        this.value = value;
        this.sign = value < 0;
        this.isSmall = true;
    }
    SmallInteger.prototype = Object.create(Integer.prototype);

    function NativeBigInt(value) {
        this.value = value;
    }
    NativeBigInt.prototype = Object.create(Integer.prototype);

    function isPrecise(n) {
        return -MAX_INT < n && n < MAX_INT;
    }

    function smallToArray(n) { // For performance reasons doesn't reference BASE, need to change this function if BASE changes
        if (n < 1e7)
            return [n];
        if (n < 1e14)
            return [n % 1e7, Math.floor(n / 1e7)];
        return [n % 1e7, Math.floor(n / 1e7) % 1e7, Math.floor(n / 1e14)];
    }

    function arrayToSmall(arr) { // If BASE changes this function may need to change
        trim(arr);
        var length = arr.length;
        if (length < 4 && compareAbs(arr, MAX_INT_ARR) < 0) {
            switch (length) {
                case 0: return 0;
                case 1: return arr[0];
                case 2: return arr[0] + arr[1] * BASE;
                default: return arr[0] + (arr[1] + arr[2] * BASE) * BASE;
            }
        }
        return arr;
    }

    function trim(v) {
        var i = v.length;
        while (v[--i] === 0);
        v.length = i + 1;
    }

    function createArray(length) { // function shamelessly stolen from Yaffle's library https://github.com/Yaffle/BigInteger
        var x = new Array(length);
        var i = -1;
        while (++i < length) {
            x[i] = 0;
        }
        return x;
    }

    function truncate(n) {
        if (n > 0) return Math.floor(n);
        return Math.ceil(n);
    }

    function add(a, b) { // assumes a and b are arrays with a.length >= b.length
        var l_a = a.length,
            l_b = b.length,
            r = new Array(l_a),
            carry = 0,
            base = BASE,
            sum, i;
        for (i = 0; i < l_b; i++) {
            sum = a[i] + b[i] + carry;
            carry = sum >= base ? 1 : 0;
            r[i] = sum - carry * base;
        }
        while (i < l_a) {
            sum = a[i] + carry;
            carry = sum === base ? 1 : 0;
            r[i++] = sum - carry * base;
        }
        if (carry > 0) r.push(carry);
        return r;
    }

    function addAny(a, b) {
        if (a.length >= b.length) return add(a, b);
        return add(b, a);
    }

    function addSmall(a, carry) { // assumes a is array, carry is number with 0 <= carry < MAX_INT
        var l = a.length,
            r = new Array(l),
            base = BASE,
            sum, i;
        for (i = 0; i < l; i++) {
            sum = a[i] - base + carry;
            carry = Math.floor(sum / base);
            r[i] = sum - carry * base;
            carry += 1;
        }
        while (carry > 0) {
            r[i++] = carry % base;
            carry = Math.floor(carry / base);
        }
        return r;
    }

    BigInteger.prototype.add = function (v) {
        var n = parseValue(v);
        if (this.sign !== n.sign) {
            return this.subtract(n.negate());
        }
        var a = this.value, b = n.value;
        if (n.isSmall) {
            return new BigInteger(addSmall(a, Math.abs(b)), this.sign);
        }
        return new BigInteger(addAny(a, b), this.sign);
    };
    BigInteger.prototype.plus = BigInteger.prototype.add;

    SmallInteger.prototype.add = function (v) {
        var n = parseValue(v);
        var a = this.value;
        if (a < 0 !== n.sign) {
            return this.subtract(n.negate());
        }
        var b = n.value;
        if (n.isSmall) {
            if (isPrecise(a + b)) return new SmallInteger(a + b);
            b = smallToArray(Math.abs(b));
        }
        return new BigInteger(addSmall(b, Math.abs(a)), a < 0);
    };
    SmallInteger.prototype.plus = SmallInteger.prototype.add;

    NativeBigInt.prototype.add = function (v) {
        return new NativeBigInt(this.value + parseValue(v).value);
    }
    NativeBigInt.prototype.plus = NativeBigInt.prototype.add;

    function subtract(a, b) { // assumes a and b are arrays with a >= b
        var a_l = a.length,
            b_l = b.length,
            r = new Array(a_l),
            borrow = 0,
            base = BASE,
            i, difference;
        for (i = 0; i < b_l; i++) {
            difference = a[i] - borrow - b[i];
            if (difference < 0) {
                difference += base;
                borrow = 1;
            } else borrow = 0;
            r[i] = difference;
        }
        for (i = b_l; i < a_l; i++) {
            difference = a[i] - borrow;
            if (difference < 0) difference += base;
            else {
                r[i++] = difference;
                break;
            }
            r[i] = difference;
        }
        for (; i < a_l; i++) {
            r[i] = a[i];
        }
        trim(r);
        return r;
    }

    function subtractAny(a, b, sign) {
        var value;
        if (compareAbs(a, b) >= 0) {
            value = subtract(a, b);
        } else {
            value = subtract(b, a);
            sign = !sign;
        }
        value = arrayToSmall(value);
        if (typeof value === "number") {
            if (sign) value = -value;
            return new SmallInteger(value);
        }
        return new BigInteger(value, sign);
    }

    function subtractSmall(a, b, sign) { // assumes a is array, b is number with 0 <= b < MAX_INT
        var l = a.length,
            r = new Array(l),
            carry = -b,
            base = BASE,
            i, difference;
        for (i = 0; i < l; i++) {
            difference = a[i] + carry;
            carry = Math.floor(difference / base);
            difference %= base;
            r[i] = difference < 0 ? difference + base : difference;
        }
        r = arrayToSmall(r);
        if (typeof r === "number") {
            if (sign) r = -r;
            return new SmallInteger(r);
        } return new BigInteger(r, sign);
    }

    BigInteger.prototype.subtract = function (v) {
        var n = parseValue(v);
        if (this.sign !== n.sign) {
            return this.add(n.negate());
        }
        var a = this.value, b = n.value;
        if (n.isSmall)
            return subtractSmall(a, Math.abs(b), this.sign);
        return subtractAny(a, b, this.sign);
    };
    BigInteger.prototype.minus = BigInteger.prototype.subtract;

    SmallInteger.prototype.subtract = function (v) {
        var n = parseValue(v);
        var a = this.value;
        if (a < 0 !== n.sign) {
            return this.add(n.negate());
        }
        var b = n.value;
        if (n.isSmall) {
            return new SmallInteger(a - b);
        }
        return subtractSmall(b, Math.abs(a), a >= 0);
    };
    SmallInteger.prototype.minus = SmallInteger.prototype.subtract;

    NativeBigInt.prototype.subtract = function (v) {
        return new NativeBigInt(this.value - parseValue(v).value);
    }
    NativeBigInt.prototype.minus = NativeBigInt.prototype.subtract;

    BigInteger.prototype.negate = function () {
        return new BigInteger(this.value, !this.sign);
    };
    SmallInteger.prototype.negate = function () {
        var sign = this.sign;
        var small = new SmallInteger(-this.value);
        small.sign = !sign;
        return small;
    };
    NativeBigInt.prototype.negate = function () {
        return new NativeBigInt(-this.value);
    }

    BigInteger.prototype.abs = function () {
        return new BigInteger(this.value, false);
    };
    SmallInteger.prototype.abs = function () {
        return new SmallInteger(Math.abs(this.value));
    };
    NativeBigInt.prototype.abs = function () {
        return new NativeBigInt(this.value >= 0 ? this.value : -this.value);
    }


    function multiplyLong(a, b) {
        var a_l = a.length,
            b_l = b.length,
            l = a_l + b_l,
            r = createArray(l),
            base = BASE,
            product, carry, i, a_i, b_j;
        for (i = 0; i < a_l; ++i) {
            a_i = a[i];
            for (var j = 0; j < b_l; ++j) {
                b_j = b[j];
                product = a_i * b_j + r[i + j];
                carry = Math.floor(product / base);
                r[i + j] = product - carry * base;
                r[i + j + 1] += carry;
            }
        }
        trim(r);
        return r;
    }

    function multiplySmall(a, b) { // assumes a is array, b is number with |b| < BASE
        var l = a.length,
            r = new Array(l),
            base = BASE,
            carry = 0,
            product, i;
        for (i = 0; i < l; i++) {
            product = a[i] * b + carry;
            carry = Math.floor(product / base);
            r[i] = product - carry * base;
        }
        while (carry > 0) {
            r[i++] = carry % base;
            carry = Math.floor(carry / base);
        }
        return r;
    }

    function shiftLeft(x, n) {
        var r = [];
        while (n-- > 0) r.push(0);
        return r.concat(x);
    }

    function multiplyKaratsuba(x, y) {
        var n = Math.max(x.length, y.length);

        if (n <= 30) return multiplyLong(x, y);
        n = Math.ceil(n / 2);

        var b = x.slice(n),
            a = x.slice(0, n),
            d = y.slice(n),
            c = y.slice(0, n);

        var ac = multiplyKaratsuba(a, c),
            bd = multiplyKaratsuba(b, d),
            abcd = multiplyKaratsuba(addAny(a, b), addAny(c, d));

        var product = addAny(addAny(ac, shiftLeft(subtract(subtract(abcd, ac), bd), n)), shiftLeft(bd, 2 * n));
        trim(product);
        return product;
    }

    // The following function is derived from a surface fit of a graph plotting the performance difference
    // between long multiplication and karatsuba multiplication versus the lengths of the two arrays.
    function useKaratsuba(l1, l2) {
        return -0.012 * l1 - 0.012 * l2 + 0.000015 * l1 * l2 > 0;
    }

    BigInteger.prototype.multiply = function (v) {
        var n = parseValue(v),
            a = this.value, b = n.value,
            sign = this.sign !== n.sign,
            abs;
        if (n.isSmall) {
            if (b === 0) return Integer[0];
            if (b === 1) return this;
            if (b === -1) return this.negate();
            abs = Math.abs(b);
            if (abs < BASE) {
                return new BigInteger(multiplySmall(a, abs), sign);
            }
            b = smallToArray(abs);
        }
        if (useKaratsuba(a.length, b.length)) // Karatsuba is only faster for certain array sizes
            return new BigInteger(multiplyKaratsuba(a, b), sign);
        return new BigInteger(multiplyLong(a, b), sign);
    };

    BigInteger.prototype.times = BigInteger.prototype.multiply;

    function multiplySmallAndArray(a, b, sign) { // a >= 0
        if (a < BASE) {
            return new BigInteger(multiplySmall(b, a), sign);
        }
        return new BigInteger(multiplyLong(b, smallToArray(a)), sign);
    }
    SmallInteger.prototype._multiplyBySmall = function (a) {
        if (isPrecise(a.value * this.value)) {
            return new SmallInteger(a.value * this.value);
        }
        return multiplySmallAndArray(Math.abs(a.value), smallToArray(Math.abs(this.value)), this.sign !== a.sign);
    };
    BigInteger.prototype._multiplyBySmall = function (a) {
        if (a.value === 0) return Integer[0];
        if (a.value === 1) return this;
        if (a.value === -1) return this.negate();
        return multiplySmallAndArray(Math.abs(a.value), this.value, this.sign !== a.sign);
    };
    SmallInteger.prototype.multiply = function (v) {
        return parseValue(v)._multiplyBySmall(this);
    };
    SmallInteger.prototype.times = SmallInteger.prototype.multiply;

    NativeBigInt.prototype.multiply = function (v) {
        return new NativeBigInt(this.value * parseValue(v).value);
    }
    NativeBigInt.prototype.times = NativeBigInt.prototype.multiply;

    function square(a) {
        //console.assert(2 * BASE * BASE < MAX_INT);
        var l = a.length,
            r = createArray(l + l),
            base = BASE,
            product, carry, i, a_i, a_j;
        for (i = 0; i < l; i++) {
            a_i = a[i];
            carry = 0 - a_i * a_i;
            for (var j = i; j < l; j++) {
                a_j = a[j];
                product = 2 * (a_i * a_j) + r[i + j] + carry;
                carry = Math.floor(product / base);
                r[i + j] = product - carry * base;
            }
            r[i + l] = carry;
        }
        trim(r);
        return r;
    }

    BigInteger.prototype.square = function () {
        return new BigInteger(square(this.value), false);
    };

    SmallInteger.prototype.square = function () {
        var value = this.value * this.value;
        if (isPrecise(value)) return new SmallInteger(value);
        return new BigInteger(square(smallToArray(Math.abs(this.value))), false);
    };

    NativeBigInt.prototype.square = function (v) {
        return new NativeBigInt(this.value * this.value);
    }

    function divMod1(a, b) { // Left over from previous version. Performs faster than divMod2 on smaller input sizes.
        var a_l = a.length,
            b_l = b.length,
            base = BASE,
            result = createArray(b.length),
            divisorMostSignificantDigit = b[b_l - 1],
            // normalization
            lambda = Math.ceil(base / (2 * divisorMostSignificantDigit)),
            remainder = multiplySmall(a, lambda),
            divisor = multiplySmall(b, lambda),
            quotientDigit, shift, carry, borrow, i, l, q;
        if (remainder.length <= a_l) remainder.push(0);
        divisor.push(0);
        divisorMostSignificantDigit = divisor[b_l - 1];
        for (shift = a_l - b_l; shift >= 0; shift--) {
            quotientDigit = base - 1;
            if (remainder[shift + b_l] !== divisorMostSignificantDigit) {
                quotientDigit = Math.floor((remainder[shift + b_l] * base + remainder[shift + b_l - 1]) / divisorMostSignificantDigit);
            }
            // quotientDigit <= base - 1
            carry = 0;
            borrow = 0;
            l = divisor.length;
            for (i = 0; i < l; i++) {
                carry += quotientDigit * divisor[i];
                q = Math.floor(carry / base);
                borrow += remainder[shift + i] - (carry - q * base);
                carry = q;
                if (borrow < 0) {
                    remainder[shift + i] = borrow + base;
                    borrow = -1;
                } else {
                    remainder[shift + i] = borrow;
                    borrow = 0;
                }
            }
            while (borrow !== 0) {
                quotientDigit -= 1;
                carry = 0;
                for (i = 0; i < l; i++) {
                    carry += remainder[shift + i] - base + divisor[i];
                    if (carry < 0) {
                        remainder[shift + i] = carry + base;
                        carry = 0;
                    } else {
                        remainder[shift + i] = carry;
                        carry = 1;
                    }
                }
                borrow += carry;
            }
            result[shift] = quotientDigit;
        }
        // denormalization
        remainder = divModSmall(remainder, lambda)[0];
        return [arrayToSmall(result), arrayToSmall(remainder)];
    }

    function divMod2(a, b) { // Implementation idea shamelessly stolen from Silent Matt's library http://silentmatt.com/biginteger/
        // Performs faster than divMod1 on larger input sizes.
        var a_l = a.length,
            b_l = b.length,
            result = [],
            part = [],
            base = BASE,
            guess, xlen, highx, highy, check;
        while (a_l) {
            part.unshift(a[--a_l]);
            trim(part);
            if (compareAbs(part, b) < 0) {
                result.push(0);
                continue;
            }
            xlen = part.length;
            highx = part[xlen - 1] * base + part[xlen - 2];
            highy = b[b_l - 1] * base + b[b_l - 2];
            if (xlen > b_l) {
                highx = (highx + 1) * base;
            }
            guess = Math.ceil(highx / highy);
            do {
                check = multiplySmall(b, guess);
                if (compareAbs(check, part) <= 0) break;
                guess--;
            } while (guess);
            result.push(guess);
            part = subtract(part, check);
        }
        result.reverse();
        return [arrayToSmall(result), arrayToSmall(part)];
    }

    function divModSmall(value, lambda) {
        var length = value.length,
            quotient = createArray(length),
            base = BASE,
            i, q, remainder, divisor;
        remainder = 0;
        for (i = length - 1; i >= 0; --i) {
            divisor = remainder * base + value[i];
            q = truncate(divisor / lambda);
            remainder = divisor - q * lambda;
            quotient[i] = q | 0;
        }
        return [quotient, remainder | 0];
    }

    function divModAny(self, v) {
        var value, n = parseValue(v);
        if (supportsNativeBigInt) {
            return [new NativeBigInt(self.value / n.value), new NativeBigInt(self.value % n.value)];
        }
        var a = self.value, b = n.value;
        var quotient;
        if (b === 0) throw new Error("Cannot divide by zero");
        if (self.isSmall) {
            if (n.isSmall) {
                return [new SmallInteger(truncate(a / b)), new SmallInteger(a % b)];
            }
            return [Integer[0], self];
        }
        if (n.isSmall) {
            if (b === 1) return [self, Integer[0]];
            if (b == -1) return [self.negate(), Integer[0]];
            var abs = Math.abs(b);
            if (abs < BASE) {
                value = divModSmall(a, abs);
                quotient = arrayToSmall(value[0]);
                var remainder = value[1];
                if (self.sign) remainder = -remainder;
                if (typeof quotient === "number") {
                    if (self.sign !== n.sign) quotient = -quotient;
                    return [new SmallInteger(quotient), new SmallInteger(remainder)];
                }
                return [new BigInteger(quotient, self.sign !== n.sign), new SmallInteger(remainder)];
            }
            b = smallToArray(abs);
        }
        var comparison = compareAbs(a, b);
        if (comparison === -1) return [Integer[0], self];
        if (comparison === 0) return [Integer[self.sign === n.sign ? 1 : -1], Integer[0]];

        // divMod1 is faster on smaller input sizes
        if (a.length + b.length <= 200)
            value = divMod1(a, b);
        else value = divMod2(a, b);

        quotient = value[0];
        var qSign = self.sign !== n.sign,
            mod = value[1],
            mSign = self.sign;
        if (typeof quotient === "number") {
            if (qSign) quotient = -quotient;
            quotient = new SmallInteger(quotient);
        } else quotient = new BigInteger(quotient, qSign);
        if (typeof mod === "number") {
            if (mSign) mod = -mod;
            mod = new SmallInteger(mod);
        } else mod = new BigInteger(mod, mSign);
        return [quotient, mod];
    }

    BigInteger.prototype.divmod = function (v) {
        var result = divModAny(this, v);
        return {
            quotient: result[0],
            remainder: result[1]
        };
    };
    NativeBigInt.prototype.divmod = SmallInteger.prototype.divmod = BigInteger.prototype.divmod;


    BigInteger.prototype.divide = function (v) {
        return divModAny(this, v)[0];
    };
    NativeBigInt.prototype.over = NativeBigInt.prototype.divide = function (v) {
        return new NativeBigInt(this.value / parseValue(v).value);
    };
    SmallInteger.prototype.over = SmallInteger.prototype.divide = BigInteger.prototype.over = BigInteger.prototype.divide;

    BigInteger.prototype.mod = function (v) {
        return divModAny(this, v)[1];
    };
    NativeBigInt.prototype.mod = NativeBigInt.prototype.remainder = function (v) {
        return new NativeBigInt(this.value % parseValue(v).value);
    };
    SmallInteger.prototype.remainder = SmallInteger.prototype.mod = BigInteger.prototype.remainder = BigInteger.prototype.mod;

    BigInteger.prototype.pow = function (v) {
        var n = parseValue(v),
            a = this.value,
            b = n.value,
            value, x, y;
        if (b === 0) return Integer[1];
        if (a === 0) return Integer[0];
        if (a === 1) return Integer[1];
        if (a === -1) return n.isEven() ? Integer[1] : Integer[-1];
        if (n.sign) {
            return Integer[0];
        }
        if (!n.isSmall) throw new Error("The exponent " + n.toString() + " is too large.");
        if (this.isSmall) {
            if (isPrecise(value = Math.pow(a, b)))
                return new SmallInteger(truncate(value));
        }
        x = this;
        y = Integer[1];
        while (true) {
            if (b & 1 === 1) {
                y = y.times(x);
                --b;
            }
            if (b === 0) break;
            b /= 2;
            x = x.square();
        }
        return y;
    };
    SmallInteger.prototype.pow = BigInteger.prototype.pow;

    NativeBigInt.prototype.pow = function (v) {
        var n = parseValue(v);
        var a = this.value, b = n.value;
        var _0 = BigInt(0), _1 = BigInt(1), _2 = BigInt(2);
        if (b === _0) return Integer[1];
        if (a === _0) return Integer[0];
        if (a === _1) return Integer[1];
        if (a === BigInt(-1)) return n.isEven() ? Integer[1] : Integer[-1];
        if (n.isNegative()) return new NativeBigInt(_0);
        var x = this;
        var y = Integer[1];
        while (true) {
            if ((b & _1) === _1) {
                y = y.times(x);
                --b;
            }
            if (b === _0) break;
            b /= _2;
            x = x.square();
        }
        return y;
    }

    BigInteger.prototype.modPow = function (exp, mod) {
        exp = parseValue(exp);
        mod = parseValue(mod);
        if (mod.isZero()) throw new Error("Cannot take modPow with modulus 0");
        var r = Integer[1],
            base = this.mod(mod);
        if (exp.isNegative()) {
            exp = exp.multiply(Integer[-1]);
            base = base.modInv(mod);
        }
        while (exp.isPositive()) {
            if (base.isZero()) return Integer[0];
            if (exp.isOdd()) r = r.multiply(base).mod(mod);
            exp = exp.divide(2);
            base = base.square().mod(mod);
        }
        return r;
    };
    NativeBigInt.prototype.modPow = SmallInteger.prototype.modPow = BigInteger.prototype.modPow;

    function compareAbs(a, b) {
        if (a.length !== b.length) {
            return a.length > b.length ? 1 : -1;
        }
        for (var i = a.length - 1; i >= 0; i--) {
            if (a[i] !== b[i]) return a[i] > b[i] ? 1 : -1;
        }
        return 0;
    }

    BigInteger.prototype.compareAbs = function (v) {
        var n = parseValue(v),
            a = this.value,
            b = n.value;
        if (n.isSmall) return 1;
        return compareAbs(a, b);
    };
    SmallInteger.prototype.compareAbs = function (v) {
        var n = parseValue(v),
            a = Math.abs(this.value),
            b = n.value;
        if (n.isSmall) {
            b = Math.abs(b);
            return a === b ? 0 : a > b ? 1 : -1;
        }
        return -1;
    };
    NativeBigInt.prototype.compareAbs = function (v) {
        var a = this.value;
        var b = parseValue(v).value;
        a = a >= 0 ? a : -a;
        b = b >= 0 ? b : -b;
        return a === b ? 0 : a > b ? 1 : -1;
    }

    BigInteger.prototype.compare = function (v) {
        // See discussion about comparison with Infinity:
        // https://github.com/peterolson/BigInteger.js/issues/61
        if (v === Infinity) {
            return -1;
        }
        if (v === -Infinity) {
            return 1;
        }

        var n = parseValue(v),
            a = this.value,
            b = n.value;
        if (this.sign !== n.sign) {
            return n.sign ? 1 : -1;
        }
        if (n.isSmall) {
            return this.sign ? -1 : 1;
        }
        return compareAbs(a, b) * (this.sign ? -1 : 1);
    };
    BigInteger.prototype.compareTo = BigInteger.prototype.compare;

    SmallInteger.prototype.compare = function (v) {
        if (v === Infinity) {
            return -1;
        }
        if (v === -Infinity) {
            return 1;
        }

        var n = parseValue(v),
            a = this.value,
            b = n.value;
        if (n.isSmall) {
            return a == b ? 0 : a > b ? 1 : -1;
        }
        if (a < 0 !== n.sign) {
            return a < 0 ? -1 : 1;
        }
        return a < 0 ? 1 : -1;
    };
    SmallInteger.prototype.compareTo = SmallInteger.prototype.compare;

    NativeBigInt.prototype.compare = function (v) {
        if (v === Infinity) {
            return -1;
        }
        if (v === -Infinity) {
            return 1;
        }
        var a = this.value;
        var b = parseValue(v).value;
        return a === b ? 0 : a > b ? 1 : -1;
    }
    NativeBigInt.prototype.compareTo = NativeBigInt.prototype.compare;

    BigInteger.prototype.equals = function (v) {
        return this.compare(v) === 0;
    };
    NativeBigInt.prototype.eq = NativeBigInt.prototype.equals = SmallInteger.prototype.eq = SmallInteger.prototype.equals = BigInteger.prototype.eq = BigInteger.prototype.equals;

    BigInteger.prototype.notEquals = function (v) {
        return this.compare(v) !== 0;
    };
    NativeBigInt.prototype.neq = NativeBigInt.prototype.notEquals = SmallInteger.prototype.neq = SmallInteger.prototype.notEquals = BigInteger.prototype.neq = BigInteger.prototype.notEquals;

    BigInteger.prototype.greater = function (v) {
        return this.compare(v) > 0;
    };
    NativeBigInt.prototype.gt = NativeBigInt.prototype.greater = SmallInteger.prototype.gt = SmallInteger.prototype.greater = BigInteger.prototype.gt = BigInteger.prototype.greater;

    BigInteger.prototype.lesser = function (v) {
        return this.compare(v) < 0;
    };
    NativeBigInt.prototype.lt = NativeBigInt.prototype.lesser = SmallInteger.prototype.lt = SmallInteger.prototype.lesser = BigInteger.prototype.lt = BigInteger.prototype.lesser;

    BigInteger.prototype.greaterOrEquals = function (v) {
        return this.compare(v) >= 0;
    };
    NativeBigInt.prototype.geq = NativeBigInt.prototype.greaterOrEquals = SmallInteger.prototype.geq = SmallInteger.prototype.greaterOrEquals = BigInteger.prototype.geq = BigInteger.prototype.greaterOrEquals;

    BigInteger.prototype.lesserOrEquals = function (v) {
        return this.compare(v) <= 0;
    };
    NativeBigInt.prototype.leq = NativeBigInt.prototype.lesserOrEquals = SmallInteger.prototype.leq = SmallInteger.prototype.lesserOrEquals = BigInteger.prototype.leq = BigInteger.prototype.lesserOrEquals;

    BigInteger.prototype.isEven = function () {
        return (this.value[0] & 1) === 0;
    };
    SmallInteger.prototype.isEven = function () {
        return (this.value & 1) === 0;
    };
    NativeBigInt.prototype.isEven = function () {
        return (this.value & BigInt(1)) === BigInt(0);
    }

    BigInteger.prototype.isOdd = function () {
        return (this.value[0] & 1) === 1;
    };
    SmallInteger.prototype.isOdd = function () {
        return (this.value & 1) === 1;
    };
    NativeBigInt.prototype.isOdd = function () {
        return (this.value & BigInt(1)) === BigInt(1);
    }

    BigInteger.prototype.isPositive = function () {
        return !this.sign;
    };
    SmallInteger.prototype.isPositive = function () {
        return this.value > 0;
    };
    NativeBigInt.prototype.isPositive = SmallInteger.prototype.isPositive;

    BigInteger.prototype.isNegative = function () {
        return this.sign;
    };
    SmallInteger.prototype.isNegative = function () {
        return this.value < 0;
    };
    NativeBigInt.prototype.isNegative = SmallInteger.prototype.isNegative;

    BigInteger.prototype.isUnit = function () {
        return false;
    };
    SmallInteger.prototype.isUnit = function () {
        return Math.abs(this.value) === 1;
    };
    NativeBigInt.prototype.isUnit = function () {
        return this.abs().value === BigInt(1);
    }

    BigInteger.prototype.isZero = function () {
        return false;
    };
    SmallInteger.prototype.isZero = function () {
        return this.value === 0;
    };
    NativeBigInt.prototype.isZero = function () {
        return this.value === BigInt(0);
    }

    BigInteger.prototype.isDivisibleBy = function (v) {
        var n = parseValue(v);
        if (n.isZero()) return false;
        if (n.isUnit()) return true;
        if (n.compareAbs(2) === 0) return this.isEven();
        return this.mod(n).isZero();
    };
    NativeBigInt.prototype.isDivisibleBy = SmallInteger.prototype.isDivisibleBy = BigInteger.prototype.isDivisibleBy;

    function isBasicPrime(v) {
        var n = v.abs();
        if (n.isUnit()) return false;
        if (n.equals(2) || n.equals(3) || n.equals(5)) return true;
        if (n.isEven() || n.isDivisibleBy(3) || n.isDivisibleBy(5)) return false;
        if (n.lesser(49)) return true;
        // we don't know if it's prime: let the other functions figure it out
    }

    function millerRabinTest(n, a) {
        var nPrev = n.prev(),
            b = nPrev,
            r = 0,
            d, t, i, x;
        while (b.isEven()) b = b.divide(2), r++;
        next: for (i = 0; i < a.length; i++) {
            if (n.lesser(a[i])) continue;
            x = bigInt(a[i]).modPow(b, n);
            if (x.isUnit() || x.equals(nPrev)) continue;
            for (d = r - 1; d != 0; d--) {
                x = x.square().mod(n);
                if (x.isUnit()) return false;
                if (x.equals(nPrev)) continue next;
            }
            return false;
        }
        return true;
    }

    // Set "strict" to true to force GRH-supported lower bound of 2*log(N)^2
    BigInteger.prototype.isPrime = function (strict) {
        var isPrime = isBasicPrime(this);
        if (isPrime !== undefined) return isPrime;
        var n = this.abs();
        var bits = n.bitLength();
        if (bits <= 64)
            return millerRabinTest(n, [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]);
        var logN = Math.log(2) * bits.toJSNumber();
        var t = Math.ceil((strict === true) ? (2 * Math.pow(logN, 2)) : logN);
        for (var a = [], i = 0; i < t; i++) {
            a.push(bigInt(i + 2));
        }
        return millerRabinTest(n, a);
    };
    NativeBigInt.prototype.isPrime = SmallInteger.prototype.isPrime = BigInteger.prototype.isPrime;

    BigInteger.prototype.isProbablePrime = function (iterations, rng) {
        var isPrime = isBasicPrime(this);
        if (isPrime !== undefined) return isPrime;
        var n = this.abs();
        var t = iterations === undefined ? 5 : iterations;
        for (var a = [], i = 0; i < t; i++) {
            a.push(bigInt.randBetween(2, n.minus(2), rng));
        }
        return millerRabinTest(n, a);
    };
    NativeBigInt.prototype.isProbablePrime = SmallInteger.prototype.isProbablePrime = BigInteger.prototype.isProbablePrime;

    BigInteger.prototype.modInv = function (n) {
        var t = bigInt.zero, newT = bigInt.one, r = parseValue(n), newR = this.abs(), q, lastT, lastR;
        while (!newR.isZero()) {
            q = r.divide(newR);
            lastT = t;
            lastR = r;
            t = newT;
            r = newR;
            newT = lastT.subtract(q.multiply(newT));
            newR = lastR.subtract(q.multiply(newR));
        }
        if (!r.isUnit()) throw new Error(this.toString() + " and " + n.toString() + " are not co-prime");
        if (t.compare(0) === -1) {
            t = t.add(n);
        }
        if (this.isNegative()) {
            return t.negate();
        }
        return t;
    };

    NativeBigInt.prototype.modInv = SmallInteger.prototype.modInv = BigInteger.prototype.modInv;

    BigInteger.prototype.next = function () {
        var value = this.value;
        if (this.sign) {
            return subtractSmall(value, 1, this.sign);
        }
        return new BigInteger(addSmall(value, 1), this.sign);
    };
    SmallInteger.prototype.next = function () {
        var value = this.value;
        if (value + 1 < MAX_INT) return new SmallInteger(value + 1);
        return new BigInteger(MAX_INT_ARR, false);
    };
    NativeBigInt.prototype.next = function () {
        return new NativeBigInt(this.value + BigInt(1));
    }

    BigInteger.prototype.prev = function () {
        var value = this.value;
        if (this.sign) {
            return new BigInteger(addSmall(value, 1), true);
        }
        return subtractSmall(value, 1, this.sign);
    };
    SmallInteger.prototype.prev = function () {
        var value = this.value;
        if (value - 1 > -MAX_INT) return new SmallInteger(value - 1);
        return new BigInteger(MAX_INT_ARR, true);
    };
    NativeBigInt.prototype.prev = function () {
        return new NativeBigInt(this.value - BigInt(1));
    }

    var powersOfTwo = [1];
    while (2 * powersOfTwo[powersOfTwo.length - 1] <= BASE) powersOfTwo.push(2 * powersOfTwo[powersOfTwo.length - 1]);
    var powers2Length = powersOfTwo.length, highestPower2 = powersOfTwo[powers2Length - 1];

    function shift_isSmall(n) {
        return Math.abs(n) <= BASE;
    }

    BigInteger.prototype.shiftLeft = function (v) {
        var n = parseValue(v).toJSNumber();
        if (!shift_isSmall(n)) {
            throw new Error(String(n) + " is too large for shifting.");
        }
        if (n < 0) return this.shiftRight(-n);
        var result = this;
        if (result.isZero()) return result;
        while (n >= powers2Length) {
            result = result.multiply(highestPower2);
            n -= powers2Length - 1;
        }
        return result.multiply(powersOfTwo[n]);
    };
    NativeBigInt.prototype.shiftLeft = SmallInteger.prototype.shiftLeft = BigInteger.prototype.shiftLeft;

    BigInteger.prototype.shiftRight = function (v) {
        var remQuo;
        var n = parseValue(v).toJSNumber();
        if (!shift_isSmall(n)) {
            throw new Error(String(n) + " is too large for shifting.");
        }
        if (n < 0) return this.shiftLeft(-n);
        var result = this;
        while (n >= powers2Length) {
            if (result.isZero() || (result.isNegative() && result.isUnit())) return result;
            remQuo = divModAny(result, highestPower2);
            result = remQuo[1].isNegative() ? remQuo[0].prev() : remQuo[0];
            n -= powers2Length - 1;
        }
        remQuo = divModAny(result, powersOfTwo[n]);
        return remQuo[1].isNegative() ? remQuo[0].prev() : remQuo[0];
    };
    NativeBigInt.prototype.shiftRight = SmallInteger.prototype.shiftRight = BigInteger.prototype.shiftRight;

    function bitwise(x, y, fn) {
        y = parseValue(y);
        var xSign = x.isNegative(), ySign = y.isNegative();
        var xRem = xSign ? x.not() : x,
            yRem = ySign ? y.not() : y;
        var xDigit = 0, yDigit = 0;
        var xDivMod = null, yDivMod = null;
        var result = [];
        while (!xRem.isZero() || !yRem.isZero()) {
            xDivMod = divModAny(xRem, highestPower2);
            xDigit = xDivMod[1].toJSNumber();
            if (xSign) {
                xDigit = highestPower2 - 1 - xDigit; // two's complement for negative numbers
            }

            yDivMod = divModAny(yRem, highestPower2);
            yDigit = yDivMod[1].toJSNumber();
            if (ySign) {
                yDigit = highestPower2 - 1 - yDigit; // two's complement for negative numbers
            }

            xRem = xDivMod[0];
            yRem = yDivMod[0];
            result.push(fn(xDigit, yDigit));
        }
        var sum = fn(xSign ? 1 : 0, ySign ? 1 : 0) !== 0 ? bigInt(-1) : bigInt(0);
        for (var i = result.length - 1; i >= 0; i -= 1) {
            sum = sum.multiply(highestPower2).add(bigInt(result[i]));
        }
        return sum;
    }

    BigInteger.prototype.not = function () {
        return this.negate().prev();
    };
    NativeBigInt.prototype.not = SmallInteger.prototype.not = BigInteger.prototype.not;

    BigInteger.prototype.and = function (n) {
        return bitwise(this, n, function (a, b) { return a & b; });
    };
    NativeBigInt.prototype.and = SmallInteger.prototype.and = BigInteger.prototype.and;

    BigInteger.prototype.or = function (n) {
        return bitwise(this, n, function (a, b) { return a | b; });
    };
    NativeBigInt.prototype.or = SmallInteger.prototype.or = BigInteger.prototype.or;

    BigInteger.prototype.xor = function (n) {
        return bitwise(this, n, function (a, b) { return a ^ b; });
    };
    NativeBigInt.prototype.xor = SmallInteger.prototype.xor = BigInteger.prototype.xor;

    var LOBMASK_I = 1 << 30, LOBMASK_BI = (BASE & -BASE) * (BASE & -BASE) | LOBMASK_I;
    function roughLOB(n) { // get lowestOneBit (rough)
        // SmallInteger: return Min(lowestOneBit(n), 1 << 30)
        // BigInteger: return Min(lowestOneBit(n), 1 << 14) [BASE=1e7]
        var v = n.value,
            x = typeof v === "number" ? v | LOBMASK_I :
                typeof v === "bigint" ? v | BigInt(LOBMASK_I) :
                    v[0] + v[1] * BASE | LOBMASK_BI;
        return x & -x;
    }

    function integerLogarithm(value, base) {
        if (base.compareTo(value) <= 0) {
            var tmp = integerLogarithm(value, base.square(base));
            var p = tmp.p;
            var e = tmp.e;
            var t = p.multiply(base);
            return t.compareTo(value) <= 0 ? { p: t, e: e * 2 + 1 } : { p: p, e: e * 2 };
        }
        return { p: bigInt(1), e: 0 };
    }

    BigInteger.prototype.bitLength = function () {
        var n = this;
        if (n.compareTo(bigInt(0)) < 0) {
            n = n.negate().subtract(bigInt(1));
        }
        if (n.compareTo(bigInt(0)) === 0) {
            return bigInt(0);
        }
        return bigInt(integerLogarithm(n, bigInt(2)).e).add(bigInt(1));
    }
    NativeBigInt.prototype.bitLength = SmallInteger.prototype.bitLength = BigInteger.prototype.bitLength;

    function max(a, b) {
        a = parseValue(a);
        b = parseValue(b);
        return a.greater(b) ? a : b;
    }
    function min(a, b) {
        a = parseValue(a);
        b = parseValue(b);
        return a.lesser(b) ? a : b;
    }
    function gcd(a, b) {
        a = parseValue(a).abs();
        b = parseValue(b).abs();
        if (a.equals(b)) return a;
        if (a.isZero()) return b;
        if (b.isZero()) return a;
        var c = Integer[1], d, t;
        while (a.isEven() && b.isEven()) {
            d = min(roughLOB(a), roughLOB(b));
            a = a.divide(d);
            b = b.divide(d);
            c = c.multiply(d);
        }
        while (a.isEven()) {
            a = a.divide(roughLOB(a));
        }
        do {
            while (b.isEven()) {
                b = b.divide(roughLOB(b));
            }
            if (a.greater(b)) {
                t = b; b = a; a = t;
            }
            b = b.subtract(a);
        } while (!b.isZero());
        return c.isUnit() ? a : a.multiply(c);
    }
    function lcm(a, b) {
        a = parseValue(a).abs();
        b = parseValue(b).abs();
        return a.divide(gcd(a, b)).multiply(b);
    }
    function randBetween(a, b, rng) {
        a = parseValue(a);
        b = parseValue(b);
        var usedRNG = rng || Math.random;
        var low = min(a, b), high = max(a, b);
        var range = high.subtract(low).add(1);
        if (range.isSmall) return low.add(Math.floor(usedRNG() * range));
        var digits = toBase(range, BASE).value;
        var result = [], restricted = true;
        for (var i = 0; i < digits.length; i++) {
            var top = restricted ? digits[i] : BASE;
            var digit = truncate(usedRNG() * top);
            result.push(digit);
            if (digit < top) restricted = false;
        }
        return low.add(Integer.fromArray(result, BASE, false));
    }

    var parseBase = function (text, base, alphabet, caseSensitive) {
        alphabet = alphabet || DEFAULT_ALPHABET;
        text = String(text);
        if (!caseSensitive) {
            text = text.toLowerCase();
            alphabet = alphabet.toLowerCase();
        }
        var length = text.length;
        var i;
        var absBase = Math.abs(base);
        var alphabetValues = {};
        for (i = 0; i < alphabet.length; i++) {
            alphabetValues[alphabet[i]] = i;
        }
        for (i = 0; i < length; i++) {
            var c = text[i];
            if (c === "-") continue;
            if (c in alphabetValues) {
                if (alphabetValues[c] >= absBase) {
                    if (c === "1" && absBase === 1) continue;
                    throw new Error(c + " is not a valid digit in base " + base + ".");
                }
            }
        }
        base = parseValue(base);
        var digits = [];
        var isNegative = text[0] === "-";
        for (i = isNegative ? 1 : 0; i < text.length; i++) {
            var c = text[i];
            if (c in alphabetValues) digits.push(parseValue(alphabetValues[c]));
            else if (c === "<") {
                var start = i;
                do { i++; } while (text[i] !== ">" && i < text.length);
                digits.push(parseValue(text.slice(start + 1, i)));
            }
            else throw new Error(c + " is not a valid character");
        }
        return parseBaseFromArray(digits, base, isNegative);
    };

    function parseBaseFromArray(digits, base, isNegative) {
        var val = Integer[0], pow = Integer[1], i;
        for (i = digits.length - 1; i >= 0; i--) {
            val = val.add(digits[i].times(pow));
            pow = pow.times(base);
        }
        return isNegative ? val.negate() : val;
    }

    function stringify(digit, alphabet) {
        alphabet = alphabet || DEFAULT_ALPHABET;
        if (digit < alphabet.length) {
            return alphabet[digit];
        }
        return "<" + digit + ">";
    }

    function toBase(n, base) {
        base = bigInt(base);
        if (base.isZero()) {
            if (n.isZero()) return { value: [0], isNegative: false };
            throw new Error("Cannot convert nonzero numbers to base 0.");
        }
        if (base.equals(-1)) {
            if (n.isZero()) return { value: [0], isNegative: false };
            if (n.isNegative())
                return {
                    value: [].concat.apply([], Array.apply(null, Array(-n.toJSNumber()))
                        .map(Array.prototype.valueOf, [1, 0])
                    ),
                    isNegative: false
                };

            var arr = Array.apply(null, Array(n.toJSNumber() - 1))
                .map(Array.prototype.valueOf, [0, 1]);
            arr.unshift([1]);
            return {
                value: [].concat.apply([], arr),
                isNegative: false
            };
        }

        var neg = false;
        if (n.isNegative() && base.isPositive()) {
            neg = true;
            n = n.abs();
        }
        if (base.isUnit()) {
            if (n.isZero()) return { value: [0], isNegative: false };

            return {
                value: Array.apply(null, Array(n.toJSNumber()))
                    .map(Number.prototype.valueOf, 1),
                isNegative: neg
            };
        }
        var out = [];
        var left = n, divmod;
        while (left.isNegative() || left.compareAbs(base) >= 0) {
            divmod = left.divmod(base);
            left = divmod.quotient;
            var digit = divmod.remainder;
            if (digit.isNegative()) {
                digit = base.minus(digit).abs();
                left = left.next();
            }
            out.push(digit.toJSNumber());
        }
        out.push(left.toJSNumber());
        return { value: out.reverse(), isNegative: neg };
    }

    function toBaseString(n, base, alphabet) {
        var arr = toBase(n, base);
        return (arr.isNegative ? "-" : "") + arr.value.map(function (x) {
            return stringify(x, alphabet);
        }).join('');
    }

    BigInteger.prototype.toArray = function (radix) {
        return toBase(this, radix);
    };

    SmallInteger.prototype.toArray = function (radix) {
        return toBase(this, radix);
    };

    NativeBigInt.prototype.toArray = function (radix) {
        return toBase(this, radix);
    };

    BigInteger.prototype.toString = function (radix, alphabet) {
        if (radix === undefined) radix = 10;
        if (radix !== 10) return toBaseString(this, radix, alphabet);
        var v = this.value, l = v.length, str = String(v[--l]), zeros = "0000000", digit;
        while (--l >= 0) {
            digit = String(v[l]);
            str += zeros.slice(digit.length) + digit;
        }
        var sign = this.sign ? "-" : "";
        return sign + str;
    };

    SmallInteger.prototype.toString = function (radix, alphabet) {
        if (radix === undefined) radix = 10;
        if (radix != 10) return toBaseString(this, radix, alphabet);
        return String(this.value);
    };

    NativeBigInt.prototype.toString = SmallInteger.prototype.toString;

    NativeBigInt.prototype.toJSON = BigInteger.prototype.toJSON = SmallInteger.prototype.toJSON = function () { return this.toString(); }

    BigInteger.prototype.valueOf = function () {
        return parseInt(this.toString(), 10);
    };
    BigInteger.prototype.toJSNumber = BigInteger.prototype.valueOf;

    SmallInteger.prototype.valueOf = function () {
        return this.value;
    };
    SmallInteger.prototype.toJSNumber = SmallInteger.prototype.valueOf;
    NativeBigInt.prototype.valueOf = NativeBigInt.prototype.toJSNumber = function () {
        return parseInt(this.toString(), 10);
    }

    function parseStringValue(v) {
        if (isPrecise(+v)) {
            var x = +v;
            if (x === truncate(x))
                return supportsNativeBigInt ? new NativeBigInt(BigInt(x)) : new SmallInteger(x);
            throw new Error("Invalid integer: " + v);
        }
        var sign = v[0] === "-";
        if (sign) v = v.slice(1);
        var split = v.split(/e/i);
        if (split.length > 2) throw new Error("Invalid integer: " + split.join("e"));
        if (split.length === 2) {
            var exp = split[1];
            if (exp[0] === "+") exp = exp.slice(1);
            exp = +exp;
            if (exp !== truncate(exp) || !isPrecise(exp)) throw new Error("Invalid integer: " + exp + " is not a valid exponent.");
            var text = split[0];
            var decimalPlace = text.indexOf(".");
            if (decimalPlace >= 0) {
                exp -= text.length - decimalPlace - 1;
                text = text.slice(0, decimalPlace) + text.slice(decimalPlace + 1);
            }
            if (exp < 0) throw new Error("Cannot include negative exponent part for integers");
            text += (new Array(exp + 1)).join("0");
            v = text;
        }
        var isValid = /^([0-9][0-9]*)$/.test(v);
        if (!isValid) throw new Error("Invalid integer: " + v);
        if (supportsNativeBigInt) {
            return new NativeBigInt(BigInt(sign ? "-" + v : v));
        }
        var r = [], max = v.length, l = LOG_BASE, min = max - l;
        while (max > 0) {
            r.push(+v.slice(min, max));
            min -= l;
            if (min < 0) min = 0;
            max -= l;
        }
        trim(r);
        return new BigInteger(r, sign);
    }

    function parseNumberValue(v) {
        if (supportsNativeBigInt) {
            return new NativeBigInt(BigInt(v));
        }
        if (isPrecise(v)) {
            if (v !== truncate(v)) throw new Error(v + " is not an integer.");
            return new SmallInteger(v);
        }
        return parseStringValue(v.toString());
    }

    function parseValue(v) {
        if (typeof v === "number") {
            return parseNumberValue(v);
        }
        if (typeof v === "string") {
            return parseStringValue(v);
        }
        if (typeof v === "bigint") {
            return new NativeBigInt(v);
        }
        return v;
    }
    // Pre-define numbers in range [-999,999]
    for (var i = 0; i < 1000; i++) {
        Integer[i] = parseValue(i);
        if (i > 0) Integer[-i] = parseValue(-i);
    }
    // Backwards compatibility
    Integer.one = Integer[1];
    Integer.zero = Integer[0];
    Integer.minusOne = Integer[-1];
    Integer.max = max;
    Integer.min = min;
    Integer.gcd = gcd;
    Integer.lcm = lcm;
    Integer.isInstance = function (x) { return x instanceof BigInteger || x instanceof SmallInteger || x instanceof NativeBigInt; };
    Integer.randBetween = randBetween;

    Integer.fromArray = function (digits, base, isNegative) {
        return parseBaseFromArray(digits.map(parseValue), parseValue(base || 10), isNegative);
    };

    return Integer;
})();

// Node.js check
if (typeof module !== "undefined" && module.hasOwnProperty("exports")) {
    module.exports = bigInt;
}

//amd check
if (typeof define === "function" && define.amd) {
    define( function () {
        return bigInt;
    });
}

},{}],15:[function(require,module,exports){
/**
 * @license Fraction.js v4.0.12 09/09/2015
 * http://www.xarg.org/2014/03/rational-numbers-in-javascript/
 *
 * Copyright (c) 2015, Robert Eisele (robert@xarg.org)
 * Dual licensed under the MIT or GPL Version 2 licenses.
 **/


/**
 *
 * This class offers the possibility to calculate fractions.
 * You can pass a fraction in different formats. Either as array, as double, as string or as an integer.
 *
 * Array/Object form
 * [ 0 => <nominator>, 1 => <denominator> ]
 * [ n => <nominator>, d => <denominator> ]
 *
 * Integer form
 * - Single integer value
 *
 * Double form
 * - Single double value
 *
 * String form
 * 123.456 - a simple double
 * 123/456 - a string fraction
 * 123.'456' - a double with repeating decimal places
 * 123.(456) - synonym
 * 123.45'6' - a double with repeating last place
 * 123.45(6) - synonym
 *
 * Example:
 *
 * let f = new Fraction("9.4'31'");
 * f.mul([-4, 3]).div(4.9);
 *
 */

(function(root) {

  "use strict";

  // Set Identity function to downgrade BigInt to Number if needed
  if (!BigInt) BigInt = function(n) { return n; };

  const C_ONE = BigInt(1);
  const C_ZERO = BigInt(0);
  const C_TEN = BigInt(10);
  const C_TWO = BigInt(2);
  const C_FIVE = BigInt(5);

  // Maximum search depth for cyclic rational numbers. 2000 should be more than enough.
  // Example: 1/7 = 0.(142857) has 6 repeating decimal places.
  // If MAX_CYCLE_LEN gets reduced, long cycles will not be detected and toString() only gets the first 10 digits
  const MAX_CYCLE_LEN = BigInt(2000);

  // Parsed data to avoid calling "new" all the time
  const P = {
    "s": C_ONE,
    "n": C_ZERO,
    "d": C_ONE
  };

  function createError(name) {

    function errorConstructor() {
      const temp = Error.apply(this, arguments);
      temp['name'] = this['name'] = name;
      this['stack'] = temp['stack'];
      this['message'] = temp['message'];
    }

    /**
     * Error constructor
     *
     * @constructor
     */
    function IntermediateInheritor() { }
    IntermediateInheritor.prototype = Error.prototype;
    errorConstructor.prototype = new IntermediateInheritor();

    return errorConstructor;
  }

  const DivisionByZero = Fraction['DivisionByZero'] = createError('DivisionByZero');
  const InvalidParameter = Fraction['InvalidParameter'] = createError('InvalidParameter');

  function assign(n, s) {

    try {
      n = BigInt(n);
    } catch (e) {
      throw new InvalidParameter();
    }

    return n * s;
  }

  const parse = function(p1, p2) {

    let n = C_ZERO, d = C_ONE, s = C_ONE;

    if (p1 === undefined || p1 === null) {
      /* void */
    } else if (p2 !== undefined) {
      n = BigInt(p1);
      d = BigInt(p2);
      s = n * d;
    } else if (typeof p1 === "object") {
      if ("d" in p1 && "n" in p1) {
        n = BigInt(p1["n"]);
        d = BigInt(p1["d"]);
        if ("s" in p1)
          n *= BigInt(p1["s"]);
      } else if (0 in p1) {
        n = BigInt(p1[0]);
        if (1 in p1)
          d = BigInt(p1[1]);
      } else if (p1 instanceof BigInt) {
        n = BigInt(p1);
      } else {
        throw new InvalidParameter();
      }
      s = n * d;
    } else if (typeof p1 === "bigint") {
      n = p1;
      s = p1;
      d = BigInt(1);
    } else if (typeof p1 === "number") {

      if (isNaN(p1)) {
        throw new InvalidParameter();
      }

      if (p1 < 0) {
        s = -C_ONE;
        p1 = -p1;
      }

      if (p1 % 1 === 0) {
        n = BigInt(p1);
      } else if (p1 > 0) { // check for != 0, scale would become NaN (log(0)), which converges really slow

        let z = 1;

        let A = 0, B = 1;
        let C = 1, D = 1;

        let N = 10000000;

        if (p1 >= 1) {
          z = 10 ** Math.floor(1 + Math.log10(p1));
          p1 /= z;
        }

        // Using Farey Sequences

        while (B <= N && D <= N) {
          let M = (A + C) / (B + D);

          if (p1 === M) {
            if (B + D <= N) {
              n = A + C;
              d = B + D;
            } else if (D > B) {
              n = C;
              d = D;
            } else {
              n = A;
              d = B;
            }
            break;

          } else {

            if (p1 > M) {
              A += C;
              B += D;
            } else {
              C += A;
              D += B;
            }

            if (B > N) {
              n = C;
              d = D;
            } else {
              n = A;
              d = B;
            }
          }
        }
        n = BigInt(n) * BigInt(z);
        d = BigInt(d);

      } else if (isNaN(p1)) {
        d = n = NaN;
      }

    } else if (typeof p1 === "string") {

      let ndx = 0;

      let v = C_ZERO, w = C_ZERO, x = C_ZERO, y = C_ONE, z = C_ONE;

      let match = p1.match(/\d+|./g);

      if (match === null)
        throw new InvalidParameter()

      if (match[ndx] === '-') {// Check for minus sign at the beginning
        s = -C_ONE;
        ndx++;
      } else if (match[ndx] === '+') {// Check for plus sign at the beginning
        ndx++;
      }

      if (match.length === ndx + 1) { // Check if it's just a simple number "1234"
        w = assign(match[ndx++], s);
      } else if (match[ndx + 1] === '.' || match[ndx] === '.') { // Check if it's a decimal number

        if (match[ndx] !== '.') { // Handle 0.5 and .5
          v = assign(match[ndx++], s);
        }
        ndx++;

        // Check for decimal places
        if (ndx + 1 === match.length || match[ndx + 1] === '(' && match[ndx + 3] === ')' || match[ndx + 1] === "'" && match[ndx + 3] === "'") {
          w = assign(match[ndx], s);
          y = C_TEN ** BigInt(match[ndx].length);
          ndx++;
        }

        // Check for repeating places
        if (match[ndx] === '(' && match[ndx + 2] === ')' || match[ndx] === "'" && match[ndx + 2] === "'") {
          x = assign(match[ndx + 1], s);
          z = C_TEN ** BigInt(match[ndx + 1].length) - C_ONE;
          ndx += 3;
        }

      } else if (match[ndx + 1] === '/' || match[ndx + 1] === ':') { // Check for a simple fraction "123/456" or "123:456"
        w = assign(match[ndx], s);
        y = assign(match[ndx + 2], C_ONE);
        ndx += 3;
      } else if (match[ndx + 3] === '/' && match[ndx + 1] === ' ') { // Check for a complex fraction "123 1/2"
        v = assign(match[ndx], s);
        w = assign(match[ndx + 2], s);
        y = assign(match[ndx + 4], C_ONE);
        ndx += 5;
      }

      if (match.length <= ndx) { // Check for more tokens on the stack
        d = y * z;
        s = /* void */
        n = x + d * v + z * w;
      } else {
        throw new InvalidParameter();
      }

    } else {
      throw new InvalidParameter();
    }

    if (d === C_ZERO) {
      throw new DivisionByZero();
    }

    P["s"] = s < C_ZERO ? -C_ONE : C_ONE;
    P["n"] = n < C_ZERO ? -n : n;
    P["d"] = d < C_ZERO ? -d : d;

  };

  function modpow(b, e, m) {

    let r = C_ONE;
    for (; e > C_ZERO; b = (b * b) % m, e >>= C_ONE) {

      if (e & C_ONE) {
        r = (r * b) % m;
      }
    }
    return r;
  }

  function cycleLen(n, d) {

    for (; d % C_TWO === C_ZERO;
      d /= C_TWO) {
    }

    for (; d % C_FIVE === C_ZERO;
      d /= C_FIVE) {
    }

    if (d === C_ONE) // Catch non-cyclic numbers
      return C_ZERO;

    // If we would like to compute really large numbers quicker, we could make use of Fermat's little theorem:
    // 10^(d-1) % d == 1
    // However, we don't need such large numbers and MAX_CYCLE_LEN should be the capstone,
    // as we want to translate the numbers to strings.

    let rem = C_TEN % d;
    let t = C_ONE;

    for (; rem !== C_ONE; t++) {
      rem = rem * C_TEN % d;

      if (t > MAX_CYCLE_LEN)
        return C_ZERO; // Returning 0 here means that we don't print it as a cyclic number. It's likely that the answer is `d-1`
    }
    return t;
  }

  function cycleStart(n, d, len) {

    let rem1 = C_ONE;
    let rem2 = modpow(C_TEN, len, d);

    for (let t = 0; t < 300; t++) { // s < ~log10(Number.MAX_VALUE)
      // Solve 10^s == 10^(s+t) (mod d)

      if (rem1 === rem2)
        return BigInt(t);

      rem1 = rem1 * C_TEN % d;
      rem2 = rem2 * C_TEN % d;
    }
    return 0;
  }

  function gcd(a, b) {

    if (!a)
      return b;
    if (!b)
      return a;

    while (1) {
      a %= b;
      if (!a)
        return b;
      b %= a;
      if (!b)
        return a;
    }
  }

  /**
   * Module constructor
   *
   * @constructor
   * @param {number|Fraction=} a
   * @param {number=} b
   */
  function Fraction(a, b) {

    if (!(this instanceof Fraction)) {
      return new Fraction(a, b);
    }

    parse(a, b);

    a = gcd(P["d"], P["n"]); // Abuse a

    this["s"] = P["s"];
    this["n"] = P["n"] / a | C_ZERO;
    this["d"] = P["d"] / a | C_ZERO;
  }

  Fraction.prototype = {

    "s": C_ONE,
    "n": C_ZERO,
    "d": C_ONE,

    /**
     * Calculates the absolute value
     *
     * Ex: new Fraction(-4).abs() => 4
     **/
    "abs": function() {

      return new Fraction(this["n"], this["d"]);
    },

    /**
     * Inverts the sign of the current fraction
     *
     * Ex: new Fraction(-4).neg() => 4
     **/
    "neg": function() {

      return new Fraction(-this["s"] * this["n"], this["d"]);
    },

    /**
     * Adds two rational numbers
     *
     * Ex: new Fraction({n: 2, d: 3}).add("14.9") => 467 / 30
     **/
    "add": function(a, b) {

      parse(a, b);
      return new Fraction(
        this["s"] * this["n"] * P["d"] + P["s"] * this["d"] * P["n"],
        this["d"] * P["d"]
      );
    },

    /**
     * Subtracts two rational numbers
     *
     * Ex: new Fraction({n: 2, d: 3}).add("14.9") => -427 / 30
     **/
    "sub": function(a, b) {

      parse(a, b);
      return new Fraction(
        this["s"] * this["n"] * P["d"] - P["s"] * this["d"] * P["n"],
        this["d"] * P["d"]
      );
    },

    /**
     * Multiplies two rational numbers
     *
     * Ex: new Fraction("-17.(345)").mul(3) => 5776 / 111
     **/
    "mul": function(a, b) {

      parse(a, b);
      return new Fraction(
        this["s"] * P["s"] * this["n"] * P["n"],
        this["d"] * P["d"]
      );
    },

    /**
     * Divides two rational numbers
     *
     * Ex: new Fraction("-17.(345)").inverse().div(3)
     **/
    "div": function(a, b) {

      parse(a, b);
      return new Fraction(
        this["s"] * P["s"] * this["n"] * P["d"],
        this["d"] * P["n"]
      );
    },

    /**
     * Clones the actual object
     *
     * Ex: new Fraction("-17.(345)").clone()
     **/
    "clone": function() {
      return new Fraction(this);
    },

    /**
     * Calculates the modulo of two rational numbers - a more precise fmod
     *
     * Ex: new Fraction('4.(3)').mod([7, 8]) => (13/3) % (7/8) = (5/6)
     **/
    "mod": function(a, b) {

      if (a === undefined) {
        return new Fraction(this["s"] * this["n"] % this["d"], 1);
      }

      parse(a, b);
      if (0 === P["n"] && 0 === this["d"]) {
        Fraction(0, 0); // Throw DivisionByZero
      }

      /*
       * First silly attempt, kinda slow
       *
       return that["sub"]({
       "n": num["n"] * Math.floor((this.n / this.d) / (num.n / num.d)),
       "d": num["d"],
       "s": this["s"]
       });*/

      /*
       * New attempt: a1 / b1 = a2 / b2 * q + r
       * => b2 * a1 = a2 * b1 * q + b1 * b2 * r
       * => (b2 * a1 % a2 * b1) / (b1 * b2)
       */
      return new Fraction(
        this["s"] * (P["d"] * this["n"]) % (P["n"] * this["d"]),
        P["d"] * this["d"]
      );
    },

    /**
     * Calculates the fractional gcd of two rational numbers
     *
     * Ex: new Fraction(5,8).gcd(3,7) => 1/56
     */
    "gcd": function(a, b) {

      parse(a, b);

      // gcd(a / b, c / d) = gcd(a, c) / lcm(b, d)

      return new Fraction(gcd(P["n"], this["n"]) * gcd(P["d"], this["d"]), P["d"] * this["d"]);
    },

    /**
     * Calculates the fractional lcm of two rational numbers
     *
     * Ex: new Fraction(5,8).lcm(3,7) => 15
     */
    "lcm": function(a, b) {

      parse(a, b);

      // lcm(a / b, c / d) = lcm(a, c) / gcd(b, d)

      if (P["n"] === C_ZERO && this["n"] === C_ZERO) {
        return new Fraction;
      }
      return new Fraction(P["n"] * this["n"], gcd(P["n"], this["n"]) * gcd(P["d"], this["d"]));
    },

    /**
     * Gets the inverse of the fraction, means numerator and denominator are exchanged
     *
     * Ex: new Fraction([-3, 4]).inverse() => -4 / 3
     **/
    "inverse": function() {

      return new Fraction(this["s"] * this["d"], this["n"]);
    },

    /**
     * Calculates the fraction to some integer exponent
     *
     * Ex: new Fraction(-1,2).pow(-3) => -8
     */
    "pow": function(m) {

      if (m < 0) {
        return new Fraction((this['s'] * this["d"]) ** BigInt(-m), this["n"] ** BigInt(-m));
      } else {
        return new Fraction((this['s'] * this["n"]) ** BigInt(+m), this["d"] ** BigInt(+m));
      }
    },

    /**
     * Check if two rational numbers are the same
     *
     * Ex: new Fraction(19.6).equals([98, 5]);
     **/
    "equals": function(a, b) {

      parse(a, b);
      return this["s"] * this["n"] * P["d"] === P["s"] * P["n"] * this["d"]; // Same as compare() === 0
    },

    /**
     * Check if two rational numbers are the same
     *
     * Ex: new Fraction(19.6).equals([98, 5]);
     **/
    "compare": function(a, b) {

      parse(a, b);
      let t = (this["s"] * this["n"] * P["d"] - P["s"] * P["n"] * this["d"]);

      return (C_ZERO < t) - (t < C_ZERO);
    },

    /**
     * Calculates the ceil of a rational number
     *
     * Ex: new Fraction('4.(3)').ceil() => (5 / 1)
     **/
    "ceil": function(places) {

      places = 10 ** Number(places || 0);

      return new Fraction(Math.ceil(places * Number(this["s"] * this["n"]) / Number(this["d"])), places);
    },

    /**
     * Calculates the floor of a rational number
     *
     * Ex: new Fraction('4.(3)').floor() => (4 / 1)
     **/
    "floor": function(places) {

      places = 10 ** Number(places || 0);

      return new Fraction(Math.floor(places * Number(this["s"] * this["n"]) / Number(this["d"])), places);
    },

    /**
     * Rounds a rational numbers
     *
     * Ex: new Fraction('4.(3)').round() => (4 / 1)
     **/
    "round": function(places) {

      places = 10 ** Number(places || 0);

      return new Fraction(Math.round(places * Number(this["s"] * this["n"]) / Number(this["d"])), places);
    },

    /**
     * Check if two rational numbers are divisible
     *
     * Ex: new Fraction(19.6).divisible(1.5);
     */
    "divisible": function(a, b) {

      parse(a, b);
      return !(!(P["n"] * this["d"]) || ((this["n"] * P["d"]) % (P["n"] * this["d"])));
    },

    /**
     * Returns a decimal representation of the fraction
     *
     * Ex: new Fraction("100.'91823'").valueOf() => 100.91823918239183
     **/
    'valueOf': function() {
      // Best we can do so far
      return Number(this["s"] * this["n"]) / Number(this["d"]);
    },

    /**
     * Creates a string representation of a fraction with all digits
     *
     * Ex: new Fraction("100.'91823'").toString() => "100.(91823)"
     **/
    'toString': function(dec) {

      let g;
      let N = this["n"];
      let D = this["d"];

      dec = dec || 15; // 15 = decimal places when no repitation

      let cycLen = cycleLen(N, D); // Cycle length
      let cycOff = cycleStart(N, D, cycLen); // Cycle start

      let str = this['s'] < C_ZERO ? "-" : "";

      // Append integer part
      str += N / D | C_ZERO;

      N %= D;
      N *= C_TEN;

      if (N)
        str += ".";

      if (cycLen) {

        for (let i = cycOff; i--;) {
          str += N / D | C_ZERO;
          N %= D;
          N *= C_TEN;
        }
        str += "(";
        for (let i = cycLen; i--;) {
          str += N / D | C_ZERO;
          N %= D;
          N *= C_TEN;
        }
        str += ")";
      } else {
        for (let i = dec; N && i--;) {
          str += N / D | C_ZERO;
          N %= D;
          N *= C_TEN;
        }
      }
      return str;
    },

    /**
     * Returns a string-fraction representation of a Fraction object
     *
     * Ex: new Fraction("1.'3'").toFraction() => "4 1/3"
     **/
    'toFraction': function(excludeWhole) {

      let n = this["n"];
      let d = this["d"];
      let str = this['s'] < C_ZERO ? "-" : "";

      if (d === C_ONE) {
        str += n;
      } else {
        let whole = n / d | C_ZERO;
        if (excludeWhole && whole > C_ZERO) {
          str += whole;
          str += " ";
          n %= d;
        }

        str += n;
        str += '/';
        str += d;
      }
      return str;
    },

    /**
     * Returns a latex representation of a Fraction object
     *
     * Ex: new Fraction("1.'3'").toLatex() => "\frac{4}{3}"
     **/
    'toLatex': function(excludeWhole) {

      let n = this["n"];
      let d = this["d"];
      let str = this['s'] < C_ZERO ? "-" : "";

      if (d === C_ONE) {
        str += n;
      } else {
        let whole = n / d | C_ZERO;
        if (excludeWhole && whole > C_ZERO) {
          str += whole;
          n %= d;
        }

        str += "\\frac{";
        str += n;
        str += '}{';
        str += d;
        str += '}';
      }
      return str;
    },

    /**
     * Returns an array of continued fraction elements
     *
     * Ex: new Fraction("7/8").toContinued() => [0,1,7]
     */
    'toContinued': function() {

      let a = this['n'];
      let b = this['d'];
      let res = [];

      do {
        res.push(a / b | C_ZERO);
        let t = a % b;
        a = b;
        b = t;
      } while (a !== C_ONE);

      return res;
    },

    "simplify": function(eps) {

      // First naive implementation, needs improvement

      let cont = this['abs']()['toContinued']();

      eps = eps || 0.001;

      function rec(a) {
        if (a.length === 1)
          return new Fraction(a[0]);
        return rec(a.slice(1))['inverse']()['add'](a[0]);
      }

      for (let i = 0; i < cont.length; i++) {
        let tmp = rec(cont.slice(0, i + 1));
        if (tmp['sub'](this['abs']())['abs']().valueOf() < eps) {
          return tmp['mul'](this['s']);
        }
      }
      return this;
    }
  };

  if (typeof define === "function" && define["amd"]) {
    define([], function() {
      return Fraction;
    });
  } else if (typeof exports === "object") {
    Object.defineProperty(exports, "__esModule", { 'value': true });
    Fraction['default'] = Fraction;
    Fraction['Fraction'] = Fraction;
    module['exports'] = Fraction;
  } else {
    root['Fraction'] = Fraction;
  }

})(this);

},{}],16:[function(require,module,exports){
/**
 * @license Fraction.js v4.0.12 09/09/2015
 * http://www.xarg.org/2014/03/rational-numbers-in-javascript/
 *
 * Copyright (c) 2015, Robert Eisele (robert@xarg.org)
 * Dual licensed under the MIT or GPL Version 2 licenses.
 **/


/**
 *
 * This class offers the possibility to calculate fractions.
 * You can pass a fraction in different formats. Either as array, as double, as string or as an integer.
 *
 * Array/Object form
 * [ 0 => <nominator>, 1 => <denominator> ]
 * [ n => <nominator>, d => <denominator> ]
 *
 * Integer form
 * - Single integer value
 *
 * Double form
 * - Single double value
 *
 * String form
 * 123.456 - a simple double
 * 123/456 - a string fraction
 * 123.'456' - a double with repeating decimal places
 * 123.(456) - synonym
 * 123.45'6' - a double with repeating last place
 * 123.45(6) - synonym
 *
 * Example:
 *
 * var f = new Fraction("9.4'31'");
 * f.mul([-4, 3]).div(4.9);
 *
 */

(function(root) {

  "use strict";

  // Maximum search depth for cyclic rational numbers. 2000 should be more than enough.
  // Example: 1/7 = 0.(142857) has 6 repeating decimal places.
  // If MAX_CYCLE_LEN gets reduced, long cycles will not be detected and toString() only gets the first 10 digits
  var MAX_CYCLE_LEN = 2000;

  // Parsed data to avoid calling "new" all the time
  var P = {
    "s": 1,
    "n": 0,
    "d": 1
  };

  function createError(name) {

    function errorConstructor() {
      var temp = Error.apply(this, arguments);
      temp['name'] = this['name'] = name;
      this['stack'] = temp['stack'];
      this['message'] = temp['message'];
    }

    /**
     * Error constructor
     *
     * @constructor
     */
    function IntermediateInheritor() { }
    IntermediateInheritor.prototype = Error.prototype;
    errorConstructor.prototype = new IntermediateInheritor();

    return errorConstructor;
  }

  var DivisionByZero = Fraction['DivisionByZero'] = createError('DivisionByZero');
  var InvalidParameter = Fraction['InvalidParameter'] = createError('InvalidParameter');

  function assign(n, s) {

    if (isNaN(n = parseInt(n, 10))) {
      throwInvalidParam();
    }
    return n * s;
  }

  function throwInvalidParam() {
    throw new InvalidParameter();
  }

  var parse = function(p1, p2) {

    var n = 0, d = 1, s = 1;
    var v = 0, w = 0, x = 0, y = 1, z = 1;

    var A = 0, B = 1;
    var C = 1, D = 1;

    var N = 10000000;
    var M;

    if (p1 === undefined || p1 === null) {
      /* void */
    } else if (p2 !== undefined) {
      n = p1;
      d = p2;
      s = n * d;
    } else
      switch (typeof p1) {

        case "object":
          {
            if ("d" in p1 && "n" in p1) {
              n = p1["n"];
              d = p1["d"];
              if ("s" in p1)
                n *= p1["s"];
            } else if (0 in p1) {
              n = p1[0];
              if (1 in p1)
                d = p1[1];
            } else {
              throwInvalidParam();
            }
            s = n * d;
            break;
          }
        case "number":
          {
            if (p1 < 0) {
              s = p1;
              p1 = -p1;
            }

            if (p1 % 1 === 0) {
              n = p1;
            } else if (p1 > 0) { // check for != 0, scale would become NaN (log(0)), which converges really slow

              if (p1 >= 1) {
                z = Math.pow(10, Math.floor(1 + Math.log(p1) / Math.LN10));
                p1 /= z;
              }

              // Using Farey Sequences
              // http://www.johndcook.com/blog/2010/10/20/best-rational-approximation/

              while (B <= N && D <= N) {
                M = (A + C) / (B + D);

                if (p1 === M) {
                  if (B + D <= N) {
                    n = A + C;
                    d = B + D;
                  } else if (D > B) {
                    n = C;
                    d = D;
                  } else {
                    n = A;
                    d = B;
                  }
                  break;

                } else {

                  if (p1 > M) {
                    A += C;
                    B += D;
                  } else {
                    C += A;
                    D += B;
                  }

                  if (B > N) {
                    n = C;
                    d = D;
                  } else {
                    n = A;
                    d = B;
                  }
                }
              }
              n *= z;
            } else if (isNaN(p1) || isNaN(p2)) {
              d = n = NaN;
            }
            break;
          }
        case "string":
          {
            B = p1.match(/\d+|./g);

            if (B === null)
              throwInvalidParam();

            if (B[A] === '-') {// Check for minus sign at the beginning
              s = -1;
              A++;
            } else if (B[A] === '+') {// Check for plus sign at the beginning
              A++;
            }

            if (B.length === A + 1) { // Check if it's just a simple number "1234"
              w = assign(B[A++], s);
            } else if (B[A + 1] === '.' || B[A] === '.') { // Check if it's a decimal number

              if (B[A] !== '.') { // Handle 0.5 and .5
                v = assign(B[A++], s);
              }
              A++;

              // Check for decimal places
              if (A + 1 === B.length || B[A + 1] === '(' && B[A + 3] === ')' || B[A + 1] === "'" && B[A + 3] === "'") {
                w = assign(B[A], s);
                y = Math.pow(10, B[A].length);
                A++;
              }

              // Check for repeating places
              if (B[A] === '(' && B[A + 2] === ')' || B[A] === "'" && B[A + 2] === "'") {
                x = assign(B[A + 1], s);
                z = Math.pow(10, B[A + 1].length) - 1;
                A += 3;
              }

            } else if (B[A + 1] === '/' || B[A + 1] === ':') { // Check for a simple fraction "123/456" or "123:456"
              w = assign(B[A], s);
              y = assign(B[A + 2], 1);
              A += 3;
            } else if (B[A + 3] === '/' && B[A + 1] === ' ') { // Check for a complex fraction "123 1/2"
              v = assign(B[A], s);
              w = assign(B[A + 2], s);
              y = assign(B[A + 4], 1);
              A += 5;
            }

            if (B.length <= A) { // Check for more tokens on the stack
              d = y * z;
              s = /* void */
              n = x + d * v + z * w;
              break;
            }

            /* Fall through on error */
          }
        default:
          throwInvalidParam();
      }

    if (d === 0) {
      throw new DivisionByZero();
    }

    P["s"] = s < 0 ? -1 : 1;
    P["n"] = Math.abs(n);
    P["d"] = Math.abs(d);
  };

  function modpow(b, e, m) {

    var r = 1;
    for (; e > 0; b = (b * b) % m, e >>= 1) {

      if (e & 1) {
        r = (r * b) % m;
      }
    }
    return r;
  }


  function cycleLen(n, d) {

    for (; d % 2 === 0;
      d /= 2) {
    }

    for (; d % 5 === 0;
      d /= 5) {
    }

    if (d === 1) // Catch non-cyclic numbers
      return 0;

    // If we would like to compute really large numbers quicker, we could make use of Fermat's little theorem:
    // 10^(d-1) % d == 1
    // However, we don't need such large numbers and MAX_CYCLE_LEN should be the capstone,
    // as we want to translate the numbers to strings.

    var rem = 10 % d;
    var t = 1;

    for (; rem !== 1; t++) {
      rem = rem * 10 % d;

      if (t > MAX_CYCLE_LEN)
        return 0; // Returning 0 here means that we don't print it as a cyclic number. It's likely that the answer is `d-1`
    }
    return t;
  }


  function cycleStart(n, d, len) {

    var rem1 = 1;
    var rem2 = modpow(10, len, d);

    for (var t = 0; t < 300; t++) { // s < ~log10(Number.MAX_VALUE)
      // Solve 10^s == 10^(s+t) (mod d)

      if (rem1 === rem2)
        return t;

      rem1 = rem1 * 10 % d;
      rem2 = rem2 * 10 % d;
    }
    return 0;
  }

  function gcd(a, b) {

    if (!a)
      return b;
    if (!b)
      return a;

    while (1) {
      a %= b;
      if (!a)
        return b;
      b %= a;
      if (!b)
        return a;
    }
  };

  /**
   * Module constructor
   *
   * @constructor
   * @param {number|Fraction=} a
   * @param {number=} b
   */
  function Fraction(a, b) {

    if (!(this instanceof Fraction)) {
      return new Fraction(a, b);
    }

    parse(a, b);

    if (Fraction['REDUCE']) {
      a = gcd(P["d"], P["n"]); // Abuse a
    } else {
      a = 1;
    }

    this["s"] = P["s"];
    this["n"] = P["n"] / a;
    this["d"] = P["d"] / a;
  }

  /**
   * Boolean global variable to be able to disable automatic reduction of the fraction
   *
   */
  Fraction['REDUCE'] = 1;

  Fraction.prototype = {

    "s": 1,
    "n": 0,
    "d": 1,

    /**
     * Calculates the absolute value
     *
     * Ex: new Fraction(-4).abs() => 4
     **/
    "abs": function() {

      return new Fraction(this["n"], this["d"]);
    },

    /**
     * Inverts the sign of the current fraction
     *
     * Ex: new Fraction(-4).neg() => 4
     **/
    "neg": function() {

      return new Fraction(-this["s"] * this["n"], this["d"]);
    },

    /**
     * Adds two rational numbers
     *
     * Ex: new Fraction({n: 2, d: 3}).add("14.9") => 467 / 30
     **/
    "add": function(a, b) {

      parse(a, b);
      return new Fraction(
        this["s"] * this["n"] * P["d"] + P["s"] * this["d"] * P["n"],
        this["d"] * P["d"]
      );
    },

    /**
     * Subtracts two rational numbers
     *
     * Ex: new Fraction({n: 2, d: 3}).add("14.9") => -427 / 30
     **/
    "sub": function(a, b) {

      parse(a, b);
      return new Fraction(
        this["s"] * this["n"] * P["d"] - P["s"] * this["d"] * P["n"],
        this["d"] * P["d"]
      );
    },

    /**
     * Multiplies two rational numbers
     *
     * Ex: new Fraction("-17.(345)").mul(3) => 5776 / 111
     **/
    "mul": function(a, b) {

      parse(a, b);
      return new Fraction(
        this["s"] * P["s"] * this["n"] * P["n"],
        this["d"] * P["d"]
      );
    },

    /**
     * Divides two rational numbers
     *
     * Ex: new Fraction("-17.(345)").inverse().div(3)
     **/
    "div": function(a, b) {

      parse(a, b);
      return new Fraction(
        this["s"] * P["s"] * this["n"] * P["d"],
        this["d"] * P["n"]
      );
    },

    /**
     * Clones the actual object
     *
     * Ex: new Fraction("-17.(345)").clone()
     **/
    "clone": function() {
      return new Fraction(this);
    },

    /**
     * Calculates the modulo of two rational numbers - a more precise fmod
     *
     * Ex: new Fraction('4.(3)').mod([7, 8]) => (13/3) % (7/8) = (5/6)
     **/
    "mod": function(a, b) {

      if (isNaN(this['n']) || isNaN(this['d'])) {
        return new Fraction(NaN);
      }

      if (a === undefined) {
        return new Fraction(this["s"] * this["n"] % this["d"], 1);
      }

      parse(a, b);
      if (0 === P["n"] && 0 === this["d"]) {
        Fraction(0, 0); // Throw DivisionByZero
      }

      /*
       * First silly attempt, kinda slow
       *
       return that["sub"]({
       "n": num["n"] * Math.floor((this.n / this.d) / (num.n / num.d)),
       "d": num["d"],
       "s": this["s"]
       });*/

      /*
       * New attempt: a1 / b1 = a2 / b2 * q + r
       * => b2 * a1 = a2 * b1 * q + b1 * b2 * r
       * => (b2 * a1 % a2 * b1) / (b1 * b2)
       */
      return new Fraction(
        this["s"] * (P["d"] * this["n"]) % (P["n"] * this["d"]),
        P["d"] * this["d"]
      );
    },

    /**
     * Calculates the fractional gcd of two rational numbers
     *
     * Ex: new Fraction(5,8).gcd(3,7) => 1/56
     */
    "gcd": function(a, b) {

      parse(a, b);

      // gcd(a / b, c / d) = gcd(a, c) / lcm(b, d)

      return new Fraction(gcd(P["n"], this["n"]) * gcd(P["d"], this["d"]), P["d"] * this["d"]);
    },

    /**
     * Calculates the fractional lcm of two rational numbers
     *
     * Ex: new Fraction(5,8).lcm(3,7) => 15
     */
    "lcm": function(a, b) {

      parse(a, b);

      // lcm(a / b, c / d) = lcm(a, c) / gcd(b, d)

      if (P["n"] === 0 && this["n"] === 0) {
        return new Fraction;
      }
      return new Fraction(P["n"] * this["n"], gcd(P["n"], this["n"]) * gcd(P["d"], this["d"]));
    },

    /**
     * Calculates the ceil of a rational number
     *
     * Ex: new Fraction('4.(3)').ceil() => (5 / 1)
     **/
    "ceil": function(places) {

      places = Math.pow(10, places || 0);

      if (isNaN(this["n"]) || isNaN(this["d"])) {
        return new Fraction(NaN);
      }
      return new Fraction(Math.ceil(places * this["s"] * this["n"] / this["d"]), places);
    },

    /**
     * Calculates the floor of a rational number
     *
     * Ex: new Fraction('4.(3)').floor() => (4 / 1)
     **/
    "floor": function(places) {

      places = Math.pow(10, places || 0);

      if (isNaN(this["n"]) || isNaN(this["d"])) {
        return new Fraction(NaN);
      }
      return new Fraction(Math.floor(places * this["s"] * this["n"] / this["d"]), places);
    },

    /**
     * Rounds a rational numbers
     *
     * Ex: new Fraction('4.(3)').round() => (4 / 1)
     **/
    "round": function(places) {

      places = Math.pow(10, places || 0);

      if (isNaN(this["n"]) || isNaN(this["d"])) {
        return new Fraction(NaN);
      }
      return new Fraction(Math.round(places * this["s"] * this["n"] / this["d"]), places);
    },

    /**
     * Gets the inverse of the fraction, means numerator and denominator are exchanged
     *
     * Ex: new Fraction([-3, 4]).inverse() => -4 / 3
     **/
    "inverse": function() {

      return new Fraction(this["s"] * this["d"], this["n"]);
    },

    /**
     * Calculates the fraction to some integer exponent
     *
     * Ex: new Fraction(-1,2).pow(-3) => -8
     */
    "pow": function(m) {

      if (m < 0) {
        return new Fraction(Math.pow(this['s'] * this["d"], -m), Math.pow(this["n"], -m));
      } else {
        return new Fraction(Math.pow(this['s'] * this["n"], m), Math.pow(this["d"], m));
      }
    },

    /**
     * Check if two rational numbers are the same
     *
     * Ex: new Fraction(19.6).equals([98, 5]);
     **/
    "equals": function(a, b) {

      parse(a, b);
      return this["s"] * this["n"] * P["d"] === P["s"] * P["n"] * this["d"]; // Same as compare() === 0
    },

    /**
     * Check if two rational numbers are the same
     *
     * Ex: new Fraction(19.6).equals([98, 5]);
     **/
    "compare": function(a, b) {

      parse(a, b);
      var t = (this["s"] * this["n"] * P["d"] - P["s"] * P["n"] * this["d"]);
      return (0 < t) - (t < 0);
    },

    "simplify": function(eps) {

      // First naive implementation, needs improvement

      if (isNaN(this['n']) || isNaN(this['d'])) {
        return this;
      }

      var cont = this['abs']()['toContinued']();

      eps = eps || 0.001;

      function rec(a) {
        if (a.length === 1)
          return new Fraction(a[0]);
        return rec(a.slice(1))['inverse']()['add'](a[0]);
      }

      for (var i = 0; i < cont.length; i++) {
        var tmp = rec(cont.slice(0, i + 1));
        if (tmp['sub'](this['abs']())['abs']().valueOf() < eps) {
          return tmp['mul'](this['s']);
        }
      }
      return this;
    },

    /**
     * Check if two rational numbers are divisible
     *
     * Ex: new Fraction(19.6).divisible(1.5);
     */
    "divisible": function(a, b) {

      parse(a, b);
      return !(!(P["n"] * this["d"]) || ((this["n"] * P["d"]) % (P["n"] * this["d"])));
    },

    /**
     * Returns a decimal representation of the fraction
     *
     * Ex: new Fraction("100.'91823'").valueOf() => 100.91823918239183
     **/
    'valueOf': function() {

      return this["s"] * this["n"] / this["d"];
    },

    /**
     * Returns a string-fraction representation of a Fraction object
     *
     * Ex: new Fraction("1.'3'").toFraction() => "4 1/3"
     **/
    'toFraction': function(excludeWhole) {

      var whole, str = "";
      var n = this["n"];
      var d = this["d"];
      if (this["s"] < 0) {
        str += '-';
      }

      if (d === 1) {
        str += n;
      } else {

        if (excludeWhole && (whole = Math.floor(n / d)) > 0) {
          str += whole;
          str += " ";
          n %= d;
        }

        str += n;
        str += '/';
        str += d;
      }
      return str;
    },

    /**
     * Returns a latex representation of a Fraction object
     *
     * Ex: new Fraction("1.'3'").toLatex() => "\frac{4}{3}"
     **/
    'toLatex': function(excludeWhole) {

      var whole, str = "";
      var n = this["n"];
      var d = this["d"];
      if (this["s"] < 0) {
        str += '-';
      }

      if (d === 1) {
        str += n;
      } else {

        if (excludeWhole && (whole = Math.floor(n / d)) > 0) {
          str += whole;
          n %= d;
        }

        str += "\\frac{";
        str += n;
        str += '}{';
        str += d;
        str += '}';
      }
      return str;
    },

    /**
     * Returns an array of continued fraction elements
     *
     * Ex: new Fraction("7/8").toContinued() => [0,1,7]
     */
    'toContinued': function() {

      var t;
      var a = this['n'];
      var b = this['d'];
      var res = [];

      if (isNaN(a) || isNaN(b)) {
        return res;
      }

      do {
        res.push(Math.floor(a / b));
        t = a % b;
        a = b;
        b = t;
      } while (a !== 1);

      return res;
    },

    /**
     * Creates a string representation of a fraction with all digits
     *
     * Ex: new Fraction("100.'91823'").toString() => "100.(91823)"
     **/
    'toString': function(dec) {

      var g;
      var N = this["n"];
      var D = this["d"];

      if (isNaN(N) || isNaN(D)) {
        return "NaN";
      }

      if (!Fraction['REDUCE']) {
        g = gcd(N, D);
        N /= g;
        D /= g;
      }

      dec = dec || 15; // 15 = decimal places when no repitation

      var cycLen = cycleLen(N, D); // Cycle length
      var cycOff = cycleStart(N, D, cycLen); // Cycle start

      var str = this['s'] === -1 ? "-" : "";

      str += N / D | 0;

      N %= D;
      N *= 10;

      if (N)
        str += ".";

      if (cycLen) {

        for (var i = cycOff; i--;) {
          str += N / D | 0;
          N %= D;
          N *= 10;
        }
        str += "(";
        for (var i = cycLen; i--;) {
          str += N / D | 0;
          N %= D;
          N *= 10;
        }
        str += ")";
      } else {
        for (var i = dec; N && i--;) {
          str += N / D | 0;
          N %= D;
          N *= 10;
        }
      }
      return str;
    }
  };

  if (typeof define === "function" && define["amd"]) {
    define([], function() {
      return Fraction;
    });
  } else if (typeof exports === "object") {
    Object.defineProperty(Fraction, "__esModule", { 'value': true });
    Fraction['default'] = Fraction;
    Fraction['Fraction'] = Fraction;
    module['exports'] = Fraction;
  } else {
    root['Fraction'] = Fraction;
  }

})(this);

},{}],17:[function(require,module,exports){
var MathUtils = module.exports = {
	isOdd: function(num){
		return num & 1 === 1;
	},
	isEven: function(num){
		return num & 1 === 0;
	},

	powermod: function powermod(num, exp, mod){
		if(exp === 1) return num % mod;
		if(MathUtils.isOdd(exp)){
			return (num * powermod(num, exp-1, mod)) % mod;
		}
		return Math.pow(powermod(num, exp/2, mod), 2) % mod;
	},

	isPrime: function(num){
		return MathUtils.fastIsPrime(num) && MathUtils.slowIsPrime(num);
	},
	slowIsPrime: function(num){
		if(MathUtils.isEven(num)) return false;
		for(var i = 3, max = Math.sqrt(num); i < max; i += 2){
			if(num % i === 0) return false;
		}
		return true;
	},
	fastIsPrime: function(num){
		return MathUtils.powermod(3, num-1, num) === 1;
	},

	randomPrime: function(len){
		var num = Math.floor(Math.pow(10, len || 3) * Math.random());
		if(MathUtils.isEven(num)) num++;
		while(!MathUtils.isPrime(num)) num += 2;
		return num;
	},

	gcd: function gcd(a, b){
		if(b === 0) return a;
		return gcd(b, a % b);
	},
	egcd: function eea(a, b){
		if(b === 0) return [a, 1, 0];
		var tmp = eea(b, a % b);
		var ss = tmp[1],
			ts = tmp[2];
		return [tmp[0], ts, ss - Math.floor(a/b) * ts];
	},

	modularInverse: function(a, b){
		var arr = MathUtils.egcd(a, b);
		//if(arr[1] * a + arr[2] * b !== arr[0]) throw Error("Wrong EGCD: " + sum);
		return arr[1];
	}
};
},{}],18:[function(require,module,exports){
(function(root, factory) {
    if (typeof module === 'object' && module.exports) {
        module.exports = factory();
    } else {
        root.nearley = factory();
    }
}(this, function() {

    function Rule(name, symbols, postprocess) {
        this.id = ++Rule.highestId;
        this.name = name;
        this.symbols = symbols;        // a list of literal | regex class | nonterminal
        this.postprocess = postprocess;
        return this;
    }
    Rule.highestId = 0;

    Rule.prototype.toString = function(withCursorAt) {
        var symbolSequence = (typeof withCursorAt === "undefined")
                             ? this.symbols.map(getSymbolShortDisplay).join(' ')
                             : (   this.symbols.slice(0, withCursorAt).map(getSymbolShortDisplay).join(' ')
                                 + " ● "
                                 + this.symbols.slice(withCursorAt).map(getSymbolShortDisplay).join(' ')     );
        return this.name + " → " + symbolSequence;
    }


    // a State is a rule at a position from a given starting point in the input stream (reference)
    function State(rule, dot, reference, wantedBy) {
        this.rule = rule;
        this.dot = dot;
        this.reference = reference;
        this.data = [];
        this.wantedBy = wantedBy;
        this.isComplete = this.dot === rule.symbols.length;
    }

    State.prototype.toString = function() {
        return "{" + this.rule.toString(this.dot) + "}, from: " + (this.reference || 0);
    };

    State.prototype.nextState = function(child) {
        var state = new State(this.rule, this.dot + 1, this.reference, this.wantedBy);
        state.left = this;
        state.right = child;
        if (state.isComplete) {
            state.data = state.build();
            // Having right set here will prevent the right state and its children
            // form being garbage collected
            state.right = undefined;
        }
        return state;
    };

    State.prototype.build = function() {
        var children = [];
        var node = this;
        do {
            children.push(node.right.data);
            node = node.left;
        } while (node.left);
        children.reverse();
        return children;
    };

    State.prototype.finish = function() {
        if (this.rule.postprocess) {
            this.data = this.rule.postprocess(this.data, this.reference, Parser.fail);
        }
    };


    function Column(grammar, index) {
        this.grammar = grammar;
        this.index = index;
        this.states = [];
        this.wants = {}; // states indexed by the non-terminal they expect
        this.scannable = []; // list of states that expect a token
        this.completed = {}; // states that are nullable
    }


    Column.prototype.process = function(nextColumn) {
        var states = this.states;
        var wants = this.wants;
        var completed = this.completed;

        for (var w = 0; w < states.length; w++) { // nb. we push() during iteration
            var state = states[w];

            if (state.isComplete) {
                state.finish();
                if (state.data !== Parser.fail) {
                    // complete
                    var wantedBy = state.wantedBy;
                    for (var i = wantedBy.length; i--; ) { // this line is hot
                        var left = wantedBy[i];
                        this.complete(left, state);
                    }

                    // special-case nullables
                    if (state.reference === this.index) {
                        // make sure future predictors of this rule get completed.
                        var exp = state.rule.name;
                        (this.completed[exp] = this.completed[exp] || []).push(state);
                    }
                }

            } else {
                // queue scannable states
                var exp = state.rule.symbols[state.dot];
                if (typeof exp !== 'string') {
                    this.scannable.push(state);
                    continue;
                }

                // predict
                if (wants[exp]) {
                    wants[exp].push(state);

                    if (completed.hasOwnProperty(exp)) {
                        var nulls = completed[exp];
                        for (var i = 0; i < nulls.length; i++) {
                            var right = nulls[i];
                            this.complete(state, right);
                        }
                    }
                } else {
                    wants[exp] = [state];
                    this.predict(exp);
                }
            }
        }
    }

    Column.prototype.predict = function(exp) {
        var rules = this.grammar.byName[exp] || [];

        for (var i = 0; i < rules.length; i++) {
            var r = rules[i];
            var wantedBy = this.wants[exp];
            var s = new State(r, 0, this.index, wantedBy);
            this.states.push(s);
        }
    }

    Column.prototype.complete = function(left, right) {
        var copy = left.nextState(right);
        this.states.push(copy);
    }


    function Grammar(rules, start) {
        this.rules = rules;
        this.start = start || this.rules[0].name;
        var byName = this.byName = {};
        this.rules.forEach(function(rule) {
            if (!byName.hasOwnProperty(rule.name)) {
                byName[rule.name] = [];
            }
            byName[rule.name].push(rule);
        });
    }

    // So we can allow passing (rules, start) directly to Parser for backwards compatibility
    Grammar.fromCompiled = function(rules, start) {
        var lexer = rules.Lexer;
        if (rules.ParserStart) {
          start = rules.ParserStart;
          rules = rules.ParserRules;
        }
        var rules = rules.map(function (r) { return (new Rule(r.name, r.symbols, r.postprocess)); });
        var g = new Grammar(rules, start);
        g.lexer = lexer; // nb. storing lexer on Grammar is iffy, but unavoidable
        return g;
    }


    function StreamLexer() {
      this.reset("");
    }

    StreamLexer.prototype.reset = function(data, state) {
        this.buffer = data;
        this.index = 0;
        this.line = state ? state.line : 1;
        this.lastLineBreak = state ? -state.col : 0;
    }

    StreamLexer.prototype.next = function() {
        if (this.index < this.buffer.length) {
            var ch = this.buffer[this.index++];
            if (ch === '\n') {
              this.line += 1;
              this.lastLineBreak = this.index;
            }
            return {value: ch};
        }
    }

    StreamLexer.prototype.save = function() {
      return {
        line: this.line,
        col: this.index - this.lastLineBreak,
      }
    }

    StreamLexer.prototype.formatError = function(token, message) {
        // nb. this gets called after consuming the offending token,
        // so the culprit is index-1
        var buffer = this.buffer;
        if (typeof buffer === 'string') {
            var lines = buffer
                .split("\n")
                .slice(
                    Math.max(0, this.line - 5), 
                    this.line
                );

            var nextLineBreak = buffer.indexOf('\n', this.index);
            if (nextLineBreak === -1) nextLineBreak = buffer.length;
            var col = this.index - this.lastLineBreak;
            var lastLineDigits = String(this.line).length;
            message += " at line " + this.line + " col " + col + ":\n\n";
            message += lines
                .map(function(line, i) {
                    return pad(this.line - lines.length + i + 1, lastLineDigits) + " " + line;
                }, this)
                .join("\n");
            message += "\n" + pad("", lastLineDigits + col) + "^\n";
            return message;
        } else {
            return message + " at index " + (this.index - 1);
        }

        function pad(n, length) {
            var s = String(n);
            return Array(length - s.length + 1).join(" ") + s;
        }
    }

    function Parser(rules, start, options) {
        if (rules instanceof Grammar) {
            var grammar = rules;
            var options = start;
        } else {
            var grammar = Grammar.fromCompiled(rules, start);
        }
        this.grammar = grammar;

        // Read options
        this.options = {
            keepHistory: false,
            lexer: grammar.lexer || new StreamLexer,
        };
        for (var key in (options || {})) {
            this.options[key] = options[key];
        }

        // Setup lexer
        this.lexer = this.options.lexer;
        this.lexerState = undefined;

        // Setup a table
        var column = new Column(grammar, 0);
        var table = this.table = [column];

        // I could be expecting anything.
        column.wants[grammar.start] = [];
        column.predict(grammar.start);
        // TODO what if start rule is nullable?
        column.process();
        this.current = 0; // token index
    }

    // create a reserved token for indicating a parse fail
    Parser.fail = {};

    Parser.prototype.feed = function(chunk) {
        var lexer = this.lexer;
        lexer.reset(chunk, this.lexerState);

        var token;
        while (true) {
            try {
                token = lexer.next();
                if (!token) {
                    break;
                }
            } catch (e) {
                // Create the next column so that the error reporter
                // can display the correctly predicted states.
                var nextColumn = new Column(this.grammar, this.current + 1);
                this.table.push(nextColumn);
                var err = new Error(this.reportLexerError(e));
                err.offset = this.current;
                err.token = e.token;
                throw err;
            }
            // We add new states to table[current+1]
            var column = this.table[this.current];

            // GC unused states
            if (!this.options.keepHistory) {
                delete this.table[this.current - 1];
            }

            var n = this.current + 1;
            var nextColumn = new Column(this.grammar, n);
            this.table.push(nextColumn);

            // Advance all tokens that expect the symbol
            var literal = token.text !== undefined ? token.text : token.value;
            var value = lexer.constructor === StreamLexer ? token.value : token;
            var scannable = column.scannable;
            for (var w = scannable.length; w--; ) {
                var state = scannable[w];
                var expect = state.rule.symbols[state.dot];
                // Try to consume the token
                // either regex or literal
                if (expect.test ? expect.test(value) :
                    expect.type ? expect.type === token.type
                                : expect.literal === literal) {
                    // Add it
                    var next = state.nextState({data: value, token: token, isToken: true, reference: n - 1});
                    nextColumn.states.push(next);
                }
            }

            // Next, for each of the rules, we either
            // (a) complete it, and try to see if the reference row expected that
            //     rule
            // (b) predict the next nonterminal it expects by adding that
            //     nonterminal's start state
            // To prevent duplication, we also keep track of rules we have already
            // added

            nextColumn.process();

            // If needed, throw an error:
            if (nextColumn.states.length === 0) {
                // No states at all! This is not good.
                var err = new Error(this.reportError(token));
                err.offset = this.current;
                err.token = token;
                throw err;
            }

            // maybe save lexer state
            if (this.options.keepHistory) {
              column.lexerState = lexer.save()
            }

            this.current++;
        }
        if (column) {
          this.lexerState = lexer.save()
        }

        // Incrementally keep track of results
        this.results = this.finish();

        // Allow chaining, for whatever it's worth
        return this;
    };

    Parser.prototype.reportLexerError = function(lexerError) {
        var tokenDisplay, lexerMessage;
        // Planning to add a token property to moo's thrown error
        // even on erroring tokens to be used in error display below
        var token = lexerError.token;
        if (token) {
            tokenDisplay = "input " + JSON.stringify(token.text[0]) + " (lexer error)";
            lexerMessage = this.lexer.formatError(token, "Syntax error");
        } else {
            tokenDisplay = "input (lexer error)";
            lexerMessage = lexerError.message;
        }
        return this.reportErrorCommon(lexerMessage, tokenDisplay);
    };

    Parser.prototype.reportError = function(token) {
        var tokenDisplay = (token.type ? token.type + " token: " : "") + JSON.stringify(token.value !== undefined ? token.value : token);
        var lexerMessage = this.lexer.formatError(token, "Syntax error");
        return this.reportErrorCommon(lexerMessage, tokenDisplay);
    };

    Parser.prototype.reportErrorCommon = function(lexerMessage, tokenDisplay) {
        var lines = [];
        lines.push(lexerMessage);
        var lastColumnIndex = this.table.length - 2;
        var lastColumn = this.table[lastColumnIndex];
        var expectantStates = lastColumn.states
            .filter(function(state) {
                var nextSymbol = state.rule.symbols[state.dot];
                return nextSymbol && typeof nextSymbol !== "string";
            });

        if (expectantStates.length === 0) {
            lines.push('Unexpected ' + tokenDisplay + '. I did not expect any more input. Here is the state of my parse table:\n');
            this.displayStateStack(lastColumn.states, lines);
        } else {
            lines.push('Unexpected ' + tokenDisplay + '. Instead, I was expecting to see one of the following:\n');
            // Display a "state stack" for each expectant state
            // - which shows you how this state came to be, step by step.
            // If there is more than one derivation, we only display the first one.
            var stateStacks = expectantStates
                .map(function(state) {
                    return this.buildFirstStateStack(state, []) || [state];
                }, this);
            // Display each state that is expecting a terminal symbol next.
            stateStacks.forEach(function(stateStack) {
                var state = stateStack[0];
                var nextSymbol = state.rule.symbols[state.dot];
                var symbolDisplay = this.getSymbolDisplay(nextSymbol);
                lines.push('A ' + symbolDisplay + ' based on:');
                this.displayStateStack(stateStack, lines);
            }, this);
        }
        lines.push("");
        return lines.join("\n");
    }
    
    Parser.prototype.displayStateStack = function(stateStack, lines) {
        var lastDisplay;
        var sameDisplayCount = 0;
        for (var j = 0; j < stateStack.length; j++) {
            var state = stateStack[j];
            var display = state.rule.toString(state.dot);
            if (display === lastDisplay) {
                sameDisplayCount++;
            } else {
                if (sameDisplayCount > 0) {
                    lines.push('    ^ ' + sameDisplayCount + ' more lines identical to this');
                }
                sameDisplayCount = 0;
                lines.push('    ' + display);
            }
            lastDisplay = display;
        }
    };

    Parser.prototype.getSymbolDisplay = function(symbol) {
        return getSymbolLongDisplay(symbol);
    };

    /*
    Builds a the first state stack. You can think of a state stack as the call stack
    of the recursive-descent parser which the Nearley parse algorithm simulates.
    A state stack is represented as an array of state objects. Within a
    state stack, the first item of the array will be the starting
    state, with each successive item in the array going further back into history.

    This function needs to be given a starting state and an empty array representing
    the visited states, and it returns an single state stack.

    */
    Parser.prototype.buildFirstStateStack = function(state, visited) {
        if (visited.indexOf(state) !== -1) {
            // Found cycle, return null
            // to eliminate this path from the results, because
            // we don't know how to display it meaningfully
            return null;
        }
        if (state.wantedBy.length === 0) {
            return [state];
        }
        var prevState = state.wantedBy[0];
        var childVisited = [state].concat(visited);
        var childResult = this.buildFirstStateStack(prevState, childVisited);
        if (childResult === null) {
            return null;
        }
        return [state].concat(childResult);
    };

    Parser.prototype.save = function() {
        var column = this.table[this.current];
        column.lexerState = this.lexerState;
        return column;
    };

    Parser.prototype.restore = function(column) {
        var index = column.index;
        this.current = index;
        this.table[index] = column;
        this.table.splice(index + 1);
        this.lexerState = column.lexerState;

        // Incrementally keep track of results
        this.results = this.finish();
    };

    // nb. deprecated: use save/restore instead!
    Parser.prototype.rewind = function(index) {
        if (!this.options.keepHistory) {
            throw new Error('set option `keepHistory` to enable rewinding')
        }
        // nb. recall column (table) indicies fall between token indicies.
        //        col 0   --   token 0   --   col 1
        this.restore(this.table[index]);
    };

    Parser.prototype.finish = function() {
        // Return the possible parsings
        var considerations = [];
        var start = this.grammar.start;
        var column = this.table[this.table.length - 1]
        column.states.forEach(function (t) {
            if (t.rule.name === start
                    && t.dot === t.rule.symbols.length
                    && t.reference === 0
                    && t.data !== Parser.fail) {
                considerations.push(t);
            }
        });
        return considerations.map(function(c) {return c.data; });
    };

    function getSymbolLongDisplay(symbol) {
        var type = typeof symbol;
        if (type === "string") {
            return symbol;
        } else if (type === "object") {
            if (symbol.literal) {
                return JSON.stringify(symbol.literal);
            } else if (symbol instanceof RegExp) {
                return 'character matching ' + symbol;
            } else if (symbol.type) {
                return symbol.type + ' token';
            } else if (symbol.test) {
                return 'token matching ' + String(symbol.test);
            } else {
                throw new Error('Unknown symbol type: ' + symbol);
            }
        }
    }

    function getSymbolShortDisplay(symbol) {
        var type = typeof symbol;
        if (type === "string") {
            return symbol;
        } else if (type === "object") {
            if (symbol.literal) {
                return JSON.stringify(symbol.literal);
            } else if (symbol instanceof RegExp) {
                return symbol.toString();
            } else if (symbol.type) {
                return '%' + symbol.type;
            } else if (symbol.test) {
                return '<' + String(symbol.test) + '>';
            } else {
                throw new Error('Unknown symbol type: ' + symbol);
            }
        }
    }

    return {
        Parser: Parser,
        Grammar: Grammar,
        Rule: Rule,
    };

}));

},{}],19:[function(require,module,exports){
(function (global){(function (){
/*!
 * Number-To-Words util
 * @version v1.2.4
 * @link https://github.com/marlun78/number-to-words
 * @author Martin Eneqvist (https://github.com/marlun78)
 * @contributors Aleksey Pilyugin (https://github.com/pilyugin),Jeremiah Hall (https://github.com/jeremiahrhall),Adriano Melo (https://github.com/adrianomelo),dmrzn (https://github.com/dmrzn)
 * @license MIT
 */
!function(){"use strict";var e="object"==typeof self&&self.self===self&&self||"object"==typeof global&&global.global===global&&global||this,t=9007199254740991;function f(e){return!("number"!=typeof e||e!=e||e===1/0||e===-1/0)}function l(e){return"number"==typeof e&&Math.abs(e)<=t}var n=/(hundred|thousand|(m|b|tr|quadr)illion)$/,r=/teen$/,o=/y$/,i=/(zero|one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve)$/,s={zero:"zeroth",one:"first",two:"second",three:"third",four:"fourth",five:"fifth",six:"sixth",seven:"seventh",eight:"eighth",nine:"ninth",ten:"tenth",eleven:"eleventh",twelve:"twelfth"};function h(e){return n.test(e)||r.test(e)?e+"th":o.test(e)?e.replace(o,"ieth"):i.test(e)?e.replace(i,a):e}function a(e,t){return s[t]}var u=10,d=100,p=1e3,v=1e6,b=1e9,y=1e12,c=1e15,g=9007199254740992,m=["zero","one","two","three","four","five","six","seven","eight","nine","ten","eleven","twelve","thirteen","fourteen","fifteen","sixteen","seventeen","eighteen","nineteen"],w=["zero","ten","twenty","thirty","forty","fifty","sixty","seventy","eighty","ninety"];function x(e,t){var n,r=parseInt(e,10);if(!f(r))throw new TypeError("Not a finite number: "+e+" ("+typeof e+")");if(!l(r))throw new RangeError("Input is not a safe number, it’s either too large or too small.");return n=function e(t){var n,r,o=arguments[1];if(0===t)return o?o.join(" ").replace(/,$/,""):"zero";o||(o=[]);t<0&&(o.push("minus"),t=Math.abs(t));t<20?(n=0,r=m[t]):t<d?(n=t%u,r=w[Math.floor(t/u)],n&&(r+="-"+m[n],n=0)):t<p?(n=t%d,r=e(Math.floor(t/d))+" hundred"):t<v?(n=t%p,r=e(Math.floor(t/p))+" thousand,"):t<b?(n=t%v,r=e(Math.floor(t/v))+" million,"):t<y?(n=t%b,r=e(Math.floor(t/b))+" billion,"):t<c?(n=t%y,r=e(Math.floor(t/y))+" trillion,"):t<=g&&(n=t%c,r=e(Math.floor(t/c))+" quadrillion,");o.push(r);return e(n,o)}(r),t?h(n):n}var M={toOrdinal:function(e){var t=parseInt(e,10);if(!f(t))throw new TypeError("Not a finite number: "+e+" ("+typeof e+")");if(!l(t))throw new RangeError("Input is not a safe number, it’s either too large or too small.");var n=String(t),r=Math.abs(t%100),o=11<=r&&r<=13,i=n.charAt(n.length-1);return n+(o?"th":"1"===i?"st":"2"===i?"nd":"3"===i?"rd":"th")},toWords:x,toWordsOrdinal:function(e){return h(x(e))}};"undefined"!=typeof exports?("undefined"!=typeof module&&module.exports&&(exports=module.exports=M),exports.numberToWords=M):e.numberToWords=M}();
}).call(this)}).call(this,typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {})

},{}],20:[function(require,module,exports){
"use strict";

var primeFactor = {

  isPrime: function isPrime(num) {
    // Non integer or any number less than 2 is not prime
    if (!Number.isInteger(num) || num < 2) return false;
    // Even number: only prime if it is 2
    if (num % 2 === 0) return num === 2;
    // Odd number divisible by 3: only prime if it is 3
    if (num % 3 === 0) return num === 3;
    // Search for factor 5, 7, 11, 13, 17, 19, 23, 25, 29, 31, 35, 37...
    // up to and including square root of input number
    var floorSqrt = Math.floor(Math.sqrt(num));
    for (var i = 5; i <= floorSqrt; i += 6) {
      if (num % i === 0 || num % (i + 2) === 0) return false;
    }
    return true;
  },

  calculate: function calculate(inputNum) {
    var result = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : [];
    var repeat = arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : true;

    if (!Number.isInteger(inputNum)) return result;
    var num = Math.abs(inputNum);
    if (num < 2) return result;
    var theSqrt = Math.sqrt(num);
    var x = 2;
    if (num % x) {
      x = 3;
      if (num % x) {
        x = 5;
        var add = 2;
        while (num % x && x < theSqrt) {
          // search numbers: 5, 7, 11, 13, 17, 19, 23...
          x += add;
          // add each time: 2, 4, 2, 4, 2, 4, 2...
          add = 6 - add;
        }
      }
    }

    x = x <= theSqrt ? x : num;

    if (!repeat) {
      var index = result.indexOf(x);
      if (index < 0) result.push(x);
    } else result.push(x);

    return x === num ? result : this.calculate(num / x, result, repeat);
  },

  getFactors: function getFactors(num) {
    return this.calculate(num, [], true);
  },

  getUniqueFactors: function getUniqueFactors(num) {
    return this.calculate(num, [], false);
  },

  getPrimeExponentObject: function getPrimeExponentObject(num) {
    var factors = this.calculate(num);
    var countObject = {};
    var _iteratorNormalCompletion = true;
    var _didIteratorError = false;
    var _iteratorError = undefined;

    try {
      for (var _iterator = factors[Symbol.iterator](), _step; !(_iteratorNormalCompletion = (_step = _iterator.next()).done); _iteratorNormalCompletion = true) {
        var factor = _step.value;

        if (Number.isFinite(countObject[factor])) {
          countObject[factor] += 1;
        } else {
          countObject[factor] = 1;
        }
      }
    } catch (err) {
      _didIteratorError = true;
      _iteratorError = err;
    } finally {
      try {
        if (!_iteratorNormalCompletion && _iterator.return) {
          _iterator.return();
        }
      } finally {
        if (_didIteratorError) {
          throw _iteratorError;
        }
      }
    }

    return countObject;
  },

  getFrequency: function getFrequency(num) {
    var countObject = this.getPrimeExponentObject(num);
    var result = [];

    for (var key in countObject) {
      if ({}.hasOwnProperty.call(countObject, key)) {
        var obj = {
          factor: Number(key),
          times: countObject[key]
        };
        result.push(obj);
      }
    }
    return result;
  }

};

module.exports = primeFactor;
},{}]},{},[6])(6)
});
//# sourceMappingURL=microtonal-utils.js.map
