
// ================================================================
// Utility functions
// ================================================================

function tryParseInt(x) {
  return isNaN(x) ? x : parseInt(x);
}

function toRatioStr(fr) {
  return (fr.s * fr.n) + "/" + fr.d;
}

// From: https://stackoverflow.com/a/44957114
function range(start, stop, step = 1) {
  return Array(Math.ceil((stop - start) / step)).fill(start).map((x, y) => x + y * step);
}

function xenWikiPageExists(title) {
  const xenAPI = "https://en.xen.wiki/api.php?origin=*";
  const params = "&action=query&format=json&titles=";
  const url = xenAPI + params + encodeURIComponent(title);
  try {
    return fetch(url).then(function(res) { return res.json(); })
                     .then(function(res) {
                       const results = Object.values(res.query.pages);
                       return results[0].missing !== "";
                     })
  } catch (e) {}
}

// Focuses '#expr' and adds the given string at the current cursor position
function insertAtCursor(str) {
  $('#expr').focus();
  const caret = $('#expr')[0].selectionStart;
  const curr_val = $('#expr').val();
  $('#expr').val(curr_val.slice(0,caret) + str + curr_val.slice(caret));
  $('#expr')[0].selectionStart = caret + str.length;
  $('#expr')[0].selectionEnd   = caret + str.length;
}

// Empty the given `<select>` then fill it with the given options, setting the
// given value as selected
function updateDropdown(dropdown, opts, selected) {
  dropdown.empty();
  for (const str of opts) {
    let opt = $('<option>').attr('value', str).text(str);
    if (str == selected) { opt.attr("selected", true); }
    dropdown.append(opt);
  }
}

// Update the page's title based on the current value of $('#expr')
function updateTitle() {
  if ($('#expr').val()) {
    document.title = "xen-calc: " + $('#expr').val();
  }
  else {
    document.title = "xen-calc";
  }
}

function reformatURL(str) {
  // encode a couple more characters from RFC 3986
  // (adapted from: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/encodeURIComponent)
  str = str.replaceAll(/[!']/g, function(c) {
    return '%' + c.charCodeAt(0).toString(16);
  });
  // encode spaces as "+"s
  str = str.replaceAll(/%20/gi, "+");
  // un-encode some characters for nicer-to-read URLs
  ['/','-','^',','/*,'[',']','|','<','>'*/].forEach(function (c) {
    const pat = new RegExp('%' + c.charCodeAt(0).toString(16), 'gi');
    str = str.replaceAll(pat, c);
  })
  return str;
}

// ================================================================
// State variables
// ================================================================

const defaultPrimeLimit = 13;
const primeLimitOpts =
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, "–"];

const defaultOddLimit = 81;
function oddLimitOpts(sortRat) {
  let opts = range(3, 100, 2); // all odd numbers from 3 to 99
  if (sortRat !== "difference") { opts.push("–"); }
  return opts;
}

const defaultSortRat = "No-2s Tenney height";
function sortRatOpts(oddLimit) {
  let opts = ["Tenney height", "No-2s Tenney height", "denominator"];
  if (oddLimit !== "–") { opts.push("difference"); }
  return opts;
}

const defaultLoEDO = 5;
function loEDOOpts(hiEDO) {
  return range(1, hiEDO); // all numbers from 1 to hiEDO-1
}

const defaultHiEDO = 60;
function hiEDOOpts(loEDO) {
  return range(loEDO+1, 121); // all numbers from loEDO+1 to 120
}

const defaultSortEDO = "EDO";
function sortEDOOpts() {
  return ["EDO", "difference"];
}

var moreRat;
const defaultMoreRat = 1;

var moreEDO;
const defaultMoreEDO = 1;

const defaultEDOPrimeLimit = 17;
const edoPrimeLimitOpts = primeLimitOpts.slice(0,-1);

const defaultEDORelCutoff = "33.3%";
const edoRelCutoffOpts = ["10%", "20%", "25%", "33.3%", "40%", "50%"];
const edoRelCutoffVals = [1/10, 1/5, 1/4, 1/3, 2/5, 1/2];

const defaultEDOBaseNote = "D";
const edoBaseNoteOpts = ["C", "C♯", "D♭", "D", "D♯", "E♭", "E", "F", "F♯", "G♭", "G", "G♯", "A♭", "A", "A♯", "B♭", "B"];

const defaultEDOOddLimit = 81;
const edoOddLimitOpts = oddLimitOpts();

const defaultEDOApproxsPrimeLimit = defaultPrimeLimit;
const edoApproxsPrimeLimitOpts = primeLimitOpts;

const defaultEDOApproxsOddLimit = 15;
const edoApproxsOddLimitOpts = oddLimitOpts("difference");

var moreEDOIntv;
const defaultMoreEDOIntv = 1;

var moreEDORat;
const defaultMoreEDORat = 1;

var res = {};

const synth = new XenCalcSynth();

// ================================================================
// Formatting functions
// ================================================================

// Given an array `[n, edo]` returns the string "n\edo"
function fmtEDOStep(step) {
  return step[0] + "\\" + step[1];
}
// Given a value in cents, a number of decimal places, and a boolean indicating
//  whether to add trailing zeros, return the value truncated to the given
//  number of decimal places followed by trailing zeros if the boolean is set
//  and the letter "c".
function fmtCents(cents, decimalPlaces, trailingZeros) {
  if (decimalPlaces == undefined) { return cents + "c"; }
  if (trailingZeros) { return  cents.toFixed(decimalPlaces) + "c"; }
  else               { return +cents.toFixed(decimalPlaces) + "c"; }
}
// Given a value in hertz, a number of decimal places, and a boolean indicating
//  whether to add trailing zeros, return the value truncated to the given
//  number of decimal places followed by trailing zeros if the boolean is set
//  and the letters "Hz".
function fmtHertz(hertz, decimalPlaces, trailingZeros) {
  if (decimalPlaces == undefined) { return hertz + "Hz"; }
  if (trailingZeros) { return  hertz.toFixed(decimalPlaces) + "Hz"; }
  else               { return +hertz.toFixed(decimalPlaces) + "Hz"; }
}
// Given an interval, returns its factorization as a string
function fmtFactorization(intv) {
  let [fact_off, fact_on] = [[], []];
  for (const [p,e] of intv.factors()) {
    if (e.equals(1)) {
      fact_off.push(p);
      fact_on.push(p);
    }
    else if (e.d == 1) {
      fact_off.push(p + "<sup>" + (e.s*e.n) + "</sup>");
      fact_on.push(p + "^" + (e.s*e.n));
    }
    else {
      fact_off.push(p + "<sup>" + e.toFraction() + "</sup>")
      fact_on.push(p + "^(" + e.toFraction() + ")");
    }
  }
  return [fact_off.join(" * "), fact_on.join(" * ")];
}
// Given an interval, returns it formatted as a ratio if it's a ratio, an
//  nth root if its an nth root for n <= 6 or n equal to the second argument, or
//  otherwise its factorization
function fmtExpression(intv, prefEDO) {
  try {
    if (intv.toNthRoot().n <= 6) {
      const nthRootStr = intv.toNthRootString();
      return [nthRootStr, nthRootStr];
    }
  } catch (err) {}
  if (intv.hasFactors()) {
    return fmtFactorization(intv);
  }
  const cents = intv.toCents();
  const k = findCentsDecPlaces(intv, cents);
  return [fmtCents(cents, k), fmtCents(cents, k)];
}
// Given a string and a ratio, places the string and a question mark in the
//  appropriate places (based on the given ratio) in an isoharmonic chord
//  starting at 1
function fmtIso(str, n, d) {
  const [min,max] = [Math.min(0, n, d), Math.max(n, d)];
  let items = [];
  for (let i = min; i <= max; i++) {
    if      (i == 0) { items.push("1") }
    else if (i == n) { items.push("?"); }
    else if (i == d) { items.push(str); }
    else             { items.push("-"); }
  }
  return items.join(" : ");
}
// Wrap a given string in an <a> tag formatted with the `expr` class
function fmtExtExprLink(str, linkstr) {
  if (linkstr === undefined) {
    linkstr = str
  }
  const queryStr = reformatURL(encodeURIComponent(linkstr));
  let link = $('<a>').attr("href", "./?q=" + queryStr)
                     .attr("style", "vertical-align: top;")
                     .html(str);
  return link;
}
// Wrap a given string in an <a> tag with the default class
function fmtInlineLink(str, url, sameTab) {
  const a = $('<a>').attr("href", url).html(str);
  if (sameTab) { return a.prop('outerHTML'); }
  else { return a//.attr("target", "_blank")
                 .prop('outerHTML'); }
}

// find the smallest k >= 5 such that the interval's cents value truncated
//  to k decimal places is interpreted as the same as the original interval
function findCentsDecPlaces(intv, cents) {
  if (cents == undefined) { cents = intv.toCents(); }
  let [k, found_k] = [5, false];
  for (; !found_k && k < 15; k++) {
    const i = microtonal_utils.Interval(2 ** (+cents.toFixed(k) / 1200));
    if (intv.hasFactors() || i.hasFactors()) {
      found_k |= intv.equals(i);
    }
    else {
      const [res_val, i_val] = [intv.valueOf(), i.valueOf()];
      found_k |= Math.abs(res_val - i_val) / Math.max(res_val, i_val) < 1e-15;
    }
  }
  return k;
}

// ================================================================
// Filling in the results section
// ================================================================

// Sets the `res` variable to the results of calling `parseCvt` on the current
// expression and returns a pair whose first element should be the header of
// the results section and whose second element is a list of pairs which
// should be the contents of the results table
function getResults() {
  res = microtonal_utils.parseCvt($('#expr').val());
  // The EDO case
  if (res.type == "EDO") {
    return ["EDO", [], range(1,res.edo).map(i => i + "\\" + res.edo).join("%0A")];
  }
  const intv = res.type == "interval" ? res.intv : res.intvToRef.mul(res.ref.intvToA4);
  let [typeStr, rows, scaleWorkshopData] = ["", [], ""];
  // Add interval-specific rows
  if (res.type === "interval") {
    res.hertz = res.intv.mul(res.ref.hertz).valueOf();
    typeStr = "Interval";
    const centsLink = fmtInlineLink("Size in cents", "https://en.wikipedia.org/wiki/Cent_(music)");
    const k = findCentsDecPlaces(res.intv, res.cents);
    rows.push([centsLink, fmtExtExprLink(fmtCents(res.cents, k))]);
    if (res.ratio) {
      const ratioLink = fmtInlineLink("Ratio", "https://en.wikipedia.org/wiki/Just_intonation");
      rows.push([ratioLink, fmtExtExprLink(toRatioStr(res.ratio))]);
    }
    else {
      try {
        if (res.intv.toNthRoot().n <= 6) {
          rows.push(["Expression", fmtExtExprLink(res.intv.toNthRootString())]);
        }
      }
      catch (err) {}
    }
    if (res.intv.hasFactors()) {
      const [fact_off, fact_on] = fmtFactorization(res.intv);
      if (fact_off.length > 0) {
        if (fact_off !== fact_on) {
          rows.push(["Prime factorization", { hoverSwap_off: fmtExtExprLink(fact_off, fact_on)
                                            , hoverSwap_on : fmtExtExprLink(fact_on) }]);
        }
        else {
          rows.push(["Prime factorization", fmtExtExprLink(fact_on)]);
        }
        let monzo = res.intv.toMonzo();
        if (monzo.length <= 18*7) {
          if (res.intv.isFrac()) {
            const monzoLink = fmtInlineLink("Monzo", "https://en.xen.wiki/w/Monzo");
            const str = "|" + monzo.join(" ") + "⟩";
            rows.push([monzoLink, fmtExtExprLink(str)]);
          }
          else {
            monzo = monzo.map(x => x.toFraction());
            const monzoLink = fmtInlineLink("Fractional monzo", "https://en.xen.wiki/w/Fractional_monzo");
            const str = "|" + monzo.join('<span class="bigspace"></span>') + "⟩";
            const linkStr = "|" + monzo.join(" ") + "⟩";
            rows.push([monzoLink, fmtExtExprLink(str, linkStr)]);
          }
        }
      }
    }
    if (res.iso) {
      const isoLink = fmtInlineLink("Isoharmonic", "https://en.xen.wiki/w/Isoharmonic_chords") + "/" +
                      fmtInlineLink("linear", "https://en.xen.wiki/w/Linear_chord") + " expression";
      const [expr_off, expr_on] = fmtExpression(res.iso[0]);
      const [n,d] = res.iso[0].compare(1) < 0 ? [res.iso[1].n, res.iso[1].s * res.iso[1].d]
                                              : [res.iso[1].s * res.iso[1].n, res.iso[1].d];
      const [iso_off, iso_on] = [fmtIso(expr_off, n, d), fmtIso(expr_on, n, d)];
      rows.push([isoLink, { hoverSwap_off: fmtExtExprLink(iso_off, iso_on)
                          , hoverSwap_on : fmtExtExprLink(iso_on) }]);
    }
    if (res.ratio) {
      const benedettiLink = fmtInlineLink("Benedetti height", "https://en.xen.wiki/w/Benedetti_height");
      const tenneyLink    = fmtInlineLink("Tenney height",    "https://en.xen.wiki/w/Tenney_height");
      const no2Benedetti = microtonal_utils.Interval(res.height.benedetti).factorOut(2)[1].valueOf();
      if (res.height.tenney < 50) {
        rows.push([benedettiLink, res.height.benedetti + " (no-2s: " + no2Benedetti + ")"]);
      }
      rows.push([tenneyLink, +res.height.tenney.toFixed(5) + " (no-2s: " + +Math.log2(no2Benedetti).toFixed(5) + ")"]);
    }
    if (res.edoSteps) {
      const edoLink = fmtInlineLink("EDO", "https://en.wikipedia.org/wiki/Equal_temperament");
      rows.push([edoLink + " steps", fmtExtExprLink(fmtEDOStep(res.edoSteps))]);
    }
  }
  // Add note-specific rows
  if (res.type === "note") {
    typeStr = "Note";
    const hertzLink = fmtInlineLink("Frequency in hertz", "https://en.wikipedia.org/wiki/Hertz");
    rows.push([hertzLink, fmtExtExprLink(fmtHertz(res.hertz, 5))]);
    rows.push(["Tuning meter read-out", res.tuningMeter]);
  }
  let did_merged_FJS_color = false;
  // Special case for "colorless" notes - the Pythagorean, FJS, and color notations are the same!
  if (res.type == "note" && res.symb && res.symb.py && res.symb.color
                                     && res.symb.py == res.symb.color) {
    const linkStr = fmtInlineLink("Pythagorean", "https://en.wikipedia.org/wiki/Pythagorean_tuning")
                    + "/" +
                    fmtInlineLink("FJS", "https://en.xen.wiki/w/Functional_Just_System")
                    + "/" +
                    fmtInlineLink("color", "https://en.xen.wiki/w/Color_notation")
                    + " name";
    rows.push([linkStr + "", fmtExtExprLink(res.symb.py)]);
    did_merged_FJS_color = true;
  }
  // Add any symbols
  if (res.symb) {
    if (res.symb.py && !did_merged_FJS_color) {
      const link = fmtInlineLink("Pythagorean", "https://en.wikipedia.org/wiki/Pythagorean_tuning")
                   + "/" +
                   fmtInlineLink("FJS", "https://en.xen.wiki/w/Functional_Just_System")
                   + " name";
      let str = fmtExtExprLink(res.symb.py).prop('outerHTML');
      if (res.symb.py_verbose) {
        str = fmtExtExprLink(res.symb.py_verbose).prop('outerHTML') + ", " + str;
      }
      rows.push([link, str]);
    }
    if (res.symb.FJS && !did_merged_FJS_color &&
        // for now we only have integer accidentals, since I'm not sure how
        //  useful showing non-integer accidentals actually is
        !(res.symb.FJS.includes("root") || res.symb.FJS.includes("sqrt"))) {
      const fjsLink = fmtInlineLink("FJS name", "https://en.xen.wiki/w/Functional_Just_System");
      const {otos, utos, pyi} = microtonal_utils.fjsAccidentals(intv);
      if (otos.length != 0 || utos.length != 0) {
        const otoStr = otos.length == 0 ? "" : "<sup>" + otos.join(",") + "</sup>";
        const utoStr = utos.length == 0 ? "" : "<sub>" + utos.join(",") + "</sub>";
        const withSupsSubs = (res.type == "interval" ? microtonal_utils.pySymb(pyi)
                                                     : microtonal_utils.pyNote(pyi))
                             + '<span class="supsub">' + otoStr + utoStr + '</span>';
        rows.push([fjsLink, { hoverSwap_off: fmtExtExprLink(withSupsSubs, res.symb.FJS)
                            , hoverSwap_on : fmtExtExprLink(res.symb.FJS) }]);
      }
      else {
        rows.push([fjsLink, fmtExtExprLink(res.symb.FJS)]);
      }
    }
    if (res.symb.NFJS &&
        // for now we only have integer accidentals, since I'm not sure how
        //  useful showing non-integer accidentals actually is
        !(res.symb.NFJS.includes("root") || res.symb.NFJS.includes("sqrt"))) {
      const nfjsLink = fmtInlineLink("Neutral FJS name", "https://en.xen.wiki/w/User:M-yac/Neutral_Intervals_and_the_FJS");
      let linkStr = res.symb.NFJS;
      if (res.symb.NFJS !== microtonal_utils.parseCvt(res.symb.NFJS).symb.NFJS) {
        linkStr = "NFJS(" + res.symb.NFJS + ")";
      }
      const {otos, utos, pyi} = microtonal_utils.fjsAccidentals(intv, microtonal_utils.nfjsSpec);
      if (otos.length != 0 || utos.length != 0) {
        const otoStr = otos.length == 0 ? "" : "<sup>" + otos.join(",") + "</sup>";
        const utoStr = utos.length == 0 ? "" : "<sub>" + utos.join(",") + "</sub>";
        const withSupsSubs = (res.type == "interval" ? microtonal_utils.pySymb(pyi)
                                                     : microtonal_utils.pyNote(pyi))
                             + '<span class="supsub">' + otoStr + utoStr + '</span>';
        rows.push([nfjsLink, { hoverSwap_off: fmtExtExprLink(withSupsSubs, linkStr)
                             , hoverSwap_on : fmtExtExprLink(res.symb.NFJS, linkStr) }]);
      }
      else {
        rows.push([nfjsLink, fmtExtExprLink(res.symb.NFJS, linkStr)]);
      }
    }
    if (res.symb.ups_and_downs) {
      const [steps, edo] = res.type == "interval" ? res.edoSteps : [res.edoStepsToRef[0] + res.ref.edoStepsToA4[0], res.edoStepsToRef[1]];
      const updnsLink = fmtInlineLink("Ups-and-downs notation", "https://en.xen.wiki/w/Ups_and_Downs_Notation");
      const fn = (res.type == "interval" ? microtonal_utils.updnsSymb : microtonal_utils.updnsNote);
      const offSymbs = fn(edo, steps, {useWordDesc:1, useExps:1, useHTMLExps:1});
      let [str_on, str_off] = ["", ""];
      for (let i = 0; i < res.symb.ups_and_downs.length; i++) {
        str_on  += fmtExtExprLink(res.symb.ups_and_downs[i]).prop('outerHTML');
        str_off += fmtExtExprLink(offSymbs[i] + "\\" + edo, res.symb.ups_and_downs[i]).prop('outerHTML');
        if (res.symb.ups_and_downs_verbose && i < res.symb.ups_and_downs_verbose.length) {
          str_on  += " (" + fmtExtExprLink(res.symb.ups_and_downs_verbose[i]).prop('outerHTML') + ")";
          str_off += " (" + fmtExtExprLink(res.symb.ups_and_downs_verbose[i]).prop('outerHTML') + ")";
        }
        if (i < res.symb.ups_and_downs.length - 1) {
          str_on  += "<br>";
          str_off += "<br>";
        }
      }
      rows.push([updnsLink, { hoverSwap_off: str_off, hoverSwap_on: str_on }]);
    }
  }
  if (res.english && res.english.length > 0){
    let link = "(Possible) English name" + (res.english.length > 1 ? "s" : "");
    link += $('<sup>').html($('<a>').addClass("alt").text("?")
                                    .prop("href","about.html#englishNames"))
                      .prop("outerHTML");
    rows.push([link, res.english.join("<br>")]);
  }
  // Add any color name
  if (res.symb && res.symb.color && !did_merged_FJS_color) {
    const colorLink = fmtInlineLink("Color notation", "https://en.xen.wiki/w/Color_notation");
    let str = "";
    const symbFn = res.type == "interval" ? microtonal_utils.colorSymb
                                          : microtonal_utils.colorNote;
    if (res.symb.color_verbose) {
      const name = symbFn(intv, {verbosity: 1});
      const dispName = symbFn(intv, {verbosity: 1, useWordNegative: true})
                         .replace(" 1sn", " unison")
                         .replace(" 8ve", " octave");
      str += fmtExtExprLink(dispName, name).prop('outerHTML') + ", ";
    }
    const abbrevName = symbFn(intv, {useExps: true});
    const withSupsSubs = symbFn(intv, {useHTMLExps: true});
    if (withSupsSubs !== abbrevName) {
      const str_off = str + fmtExtExprLink(withSupsSubs, abbrevName).prop("outerHTML");
      const str_on  = str + fmtExtExprLink(abbrevName).prop("outerHTML");
      rows.push([colorLink, { hoverSwap_off: str_off, hoverSwap_on: str_on }]);
    }
    else {
      str += fmtExtExprLink(res.symb.color).prop("outerHTML");
      rows.push([colorLink, str])
    }
  }
  if (res.edoSteps) { rows.push(["xen-calc page for EDO", fmtExtExprLink(res.edoSteps[1] + "-EDO")]) }
  if (res.edoStepsToRef) { rows.push(["xen-calc page for EDO", fmtExtExprLink(res.edoStepsToRef[1] + "-EDO")]) }
  // Add a note's interval reference
  if (res.type === "note" && !res.intvToRef.equals(1)) {
    rows.push([]);
    const refSymb = microtonal_utils.pyNote(res.ref.intvToA4);
    if (res.edoStepsToRef) {
      rows.push(["Interval from reference note",
                fmtExtExprLink(fmtEDOStep(res.edoStepsToRef))]);
    }
    else {
      const [expr_off, expr_on] = fmtExpression(res.intvToRef);
      rows.push(["Interval from reference note", { hoverSwap_off: fmtExtExprLink(expr_off, expr_on)
                                                 , hoverSwap_on : fmtExtExprLink(expr_on) }]);
    }
    rows.push(["Reference note and frequency", refSymb + " = " + fmtHertz(res.ref.hertz, 2)])
  }
  // Format the interval for use in Scale Workshop
  if (res.type == "interval") {
    if (res.edoSteps) { scaleWorkshopData = fmtEDOStep(res.edoSteps); }
    else if (res.ratio) { scaleWorkshopData = toRatioStr(res.ratio); }
    else { scaleWorkshopData = res.cents; }
  }
  if (res.type == "note") {
    if (res.edoStepsToRef) { scaleWorkshopData = fmtEDOStep(res.edoStepsToRef); }
    else if (res.intvToRef.isFrac()) { scaleWorkshopData = toRatioStr(res.intvToRef.toFrac()); }
    else { scaleWorkshopData = res.intvToRef.toCents().toFixed(13); }
  }
  return [typeStr, rows, scaleWorkshopData];
}

// Updates the entire results section based on the current expression
function updateResults() {
  const exprVal = $('#expr').val().trim();
  if (exprVal === "") {
    $('#errors').addClass("hidden");
    $('#didYouMeanDiv').addClass("hidden");
    $('#results').addClass("hidden");
    return;
  }
  try {
    $('#errors').addClass("hidden");
    $('#didYouMeanDiv').addClass("hidden");
    $('#results').removeClass("hidden");
    const [typeStr, rows, scaleWorkshopData] = getResults();
    if (res.symbolType === "color") {
      const s = exprVal.replace("descending", "desc.");
      const ref = res.type == "interval" ? microtonal_utils.colorSymb(res.intv, {useExps: 1})
                                         : microtonal_utils.colorNote(res.intvToRef.mul(res.ref.intvToA4), {useExps: 1});
      if (s != ref) {
        $('#didYouMeanDiv').removeClass("hidden");
        const refHTML = res.type == "interval" ? microtonal_utils.colorSymb(res.intv, {useHTMLExps: 1})
                                               : microtonal_utils.colorNote(res.intvToRef.mul(res.ref.intvToA4), {useHTMLExps: 1});
        if (ref != refHTML) {
          $('#didYouMeanDiv').addClass("hoverSwap");
          $('#didYouMean').html($('<span>').addClass("hoverSwap_off")
                                           .html(fmtExtExprLink(refHTML, ref).addClass("alt2")));
          $('#didYouMean').append($('<span>').addClass("hoverSwap_on")
                                             .html(fmtExtExprLink(ref).addClass("alt2")));
        }
        else {
          $('#didYouMeanDiv').removeClass("hoverSwap");
          $('#didYouMean').html(fmtExtExprLink(ref).addClass("alt2"));
        }
      }
    }
    else if (res.symbolType === "color (verbose)" && res.type == "interval") {
      const s = exprVal.replace("desc.", "descending")
                       .replace("unison", "1sn")
                       .replace("octave", "8ve");
      const ref = microtonal_utils.colorSymb(res.intv, {verbosity: 1});
      if (s != ref) {
        $('#didYouMeanDiv').removeClass("hidden");
        $('#didYouMean').html(fmtExtExprLink(ref).addClass("alt2"));
      }
    }
    else if (res.symbolType == "Pythagorean (verbose)" && res.type == "interval") {
      const s = exprVal.replace("desc.", "descending")
                       .replace("unison", "1sn")
                       .replace("octave", "8ve");
      const ref = microtonal_utils.pySymb(res.intv, {verbosity: 1});
      if (s != ref) {
        $('#didYouMeanDiv').removeClass("hidden");
        $('#didYouMean').html(fmtExtExprLink(ref).addClass("alt2"));
      }
    }
    else if (res.symbolType == "ups-and-downs" && res.type == "interval") {
      const [sD,edo] = exprVal.replace("descending", "desc.")
                              .split("\\").map(s => s.trim());
      const sDs = sD.split("desc. ");
      const [isDesc, s] = sDs.length == 1 ? [false, sDs[0]] : [true, sDs[1]];
      const pRes = microtonal_utils.parseFromRule(s, "upsDnsIntvAb")[0];
      const pyi = pRes[0] == "!updnsSymb" && pRes[2][0] != "!perfPyIntv"
                    ? microtonal_utils.evalExpr(pRes[2], microtonal_utils.Interval(1)).val
                    : microtonal_utils.pyInterval(pRes[2][1] || pRes[2], 0);
      const usePerfEDONotation = edo % 7 == 0 && ((pRes[0] == "!updnsSymb" && pRes[2][0] == "!perfPyIntv")
                                                  || pRes[0] == "!updnsPerfSymb");
      const ref = (isDesc ? "desc. " : "") +
                  microtonal_utils.fmtUpdnsSymb(pRes[1], pyi, {usePerfEDONotation: usePerfEDONotation});
      if (sD != ref) {
        $('#didYouMeanDiv').removeClass("hidden");
        $('#didYouMean').html(fmtExtExprLink(ref + "\\" + edo).addClass("alt2"));
      }
    }
    else if (res.symbolType == "ups-and-downs (verbose)" && res.type == "interval") {
      let [sD,edo] = exprVal.replace("desc.", "descending")
                            .replace("unison", "1sn")
                            .replace("octave", "8ve")
                            .split("\\").map(s => s.trim());
      const sDs = sD.split("descending ");
      const [isDesc, s] = sDs.length == 1 ? [false, sDs[0]] : [true, sDs[1]];
      const pRes = microtonal_utils.parseFromRule(s, "upsDnsIntvVb")[0];
      const pyi = pRes[0] == "!updnsSymb" && pRes[2][0] != "!perfPyIntv"
                    ? microtonal_utils.evalExpr(pRes[2], microtonal_utils.Interval(1)).val
                    : microtonal_utils.pyInterval(pRes[2][1] || pRes[2], 0);
      const usePerfEDONotation = edo % 7 == 0 && ((pRes[0] == "!updnsSymb" && pRes[2][0] == "!perfPyIntv")
                                                  || pRes[0] == "!updnsPerfSymb");
      const ref = (isDesc ? "descending " : "") +
                  microtonal_utils.fmtUpdnsSymb(pRes[1], pyi, {verbosity: 1, usePerfEDONotation: usePerfEDONotation});
      // we won't correct you if you say "neutral" instead of "mid" if there are no ups or downs
      if (pRes[1] == 0) { sD = sD.replace("neutral", "mid"); }
      // we won't correct you for omitting "perfect" in a perfect EDO
      if (sD != ref && (edo % 7 != 0 || pRes[0] != "!updnsPerfSymb" || sD != ref.replace("perfect ", ""))) {
        $('#didYouMeanDiv').removeClass("hidden");
        $('#didYouMean').html(fmtExtExprLink(ref + " \\ " + edo).addClass("alt2"));
      }
    }
    $('#resHeader').html(typeStr + " results");
    $('#resTable').empty();
    for (const [n,v] of rows) {
      let row = $('<tr>');
      row.append($('<td>').addClass("resLeftColumn").html(n ? n + ":" : n));
      if (v && (v.hoverSwap_off || v.hoverSwap_on)) {
        row.addClass("hoverSwap");
        const cell = $('<td>').addClass("resRightColumn");
        cell.append($('<span>').addClass('hoverSwap_off').html(v.hoverSwap_off || ""));
        cell.append($('<span>').addClass('hoverSwap_on').html(v.hoverSwap_on || ""));
        row.append(cell);
      }
      else {
        row.append($('<td>').addClass("resRightColumn").html(v));
      }
      $('#resTable').append(row);
    }
    addXenWikiLink();
    $('#resAudioHeader').html(typeStr + " audio");
    let scaleWorkshopLink = "http://sevish.com/scaleworkshop/";
    scaleWorkshopLink += "?waveform=sine&ampenv=perc-medium";
    scaleWorkshopLink += "&data=" + scaleWorkshopData;
    if (res.type == "EDO") {
      $('#resAudio').addClass("hidden");
      $('#resApproxs').addClass("hidden");
      $('#resEDO').removeClass("hidden");
      const baseHertz = updateEDOResults();
      scaleWorkshopLink += "&freq=" + baseHertz;
      $('#edoScaleWorkshopLink').attr("href", scaleWorkshopLink);
    }
    else if (res.type === "interval") {
      $('#intervalAudioButtons').removeClass("hidden");
      $('#noteAudioButtons').addClass("hidden");
      $('#resAudio').removeClass("hidden");
      $('#resApproxs').removeClass("hidden");
      $('#resEDO').addClass("hidden");
      updateRatApproxs();
      updateEDOApproxs();
      scaleWorkshopLink += "&freq=" + res.ref.hertz;
      $('#scaleWorkshopLink').attr("href", scaleWorkshopLink);
    }
    else {
      $('#intervalAudioButtons').addClass("hidden");
      $('#noteAudioButtons').removeClass("hidden");
      $('#resAudio').removeClass("hidden");
      $('#resApproxs').addClass("hidden");
      $('#resEDO').addClass("hidden");
      scaleWorkshopLink += "&freq=" + res.ref.hertz;
      $('#scaleWorkshopLink').attr("href", scaleWorkshopLink);
    }
  }
  catch (err) {
    const showAddMulTip = err.kind == "Parse error" &&
                          "*/^+-xc".indexOf(err.srcStr[err.offset]) > -1;
    if (err.kind == undefined) {
      newErr = new Error(err.name + (err.message ? "\n" + err.message : ""));
      newErr.stack = err.stack;
      err = newErr;
      console.error(err);
      logStrs(["e u " + err.name]);
    }
    else {
      logStrs(["e l " + (showAddMulTip ? "add/mul " : "") + err.kind]);
    }
    $('#errors').removeClass("hidden");
    $('#didYouMeanDiv').addClass("hidden");
    $('#results').addClass("hidden");
    const errStr = err.toString().replace("\n","<br>").replace("\\\\","\\");
    $('#errors').html($('<pre>').addClass("parseError").html(errStr));
    if (showAddMulTip) {
      let nb = $('<p>').attr("style", "font-size: 95%; text-align: left;");
      nb.append("Perhaps you're trying to mix multiplicative and additive "
                + "expressions? See ");
      nb.append($('<a>').addClass("alt").attr("href", "about.html#tipMulAddExprs")
                        .html("this tip"));
      nb.append(".");
      $('#errors').append(nb);
    }
  }
}

// Asynchronously add a Xenharmonic wiki link (if it exists) to the results
// table
function addXenWikiLink() {
  let xenPageName = "";
  if (res.edo) {
    xenPageName = res.edo + "edo";
  }
  else if (res.intv && res.intv.equals(microtonal_utils.Interval.phi)) {
    xenPageName = "Acoustic_phi";
  }
  else if (res.ratio) {
    xenPageName = toRatioStr(res.ratio);
  }
  else if (res.edoSteps) {
    xenPageName = res.edoSteps[1] + "edo";
  }
  else {
    return;
  }
  const xenURL = "https://en.xen.wiki/w/" + xenPageName;
  const pageExists = xenWikiPageExists(xenPageName);
  if (pageExists) {
    pageExists.then(function(exists) {
      if (exists) {
        let link = $('<a>')//.attr("target", "_blank")
                           .attr("href", xenURL)
                           .append(xenURL.replace("https://",""));
        let row = $('<tr id="xenWikiLinkRow">');
        row.append($('<td>').addClass("resLeftColumn").html("Xenharmonic wiki page:"));
        row.append($('<td>').addClass("resRightColumn").html(link));
        if (!document.getElementById("xenWikiLinkRow")) {
          $('#resTable').append(row);
        }
      }
    });
  }
}

// Update the best rational approximations dropdowns and table based on the
// current value of the dropdowns, and call `updateURLWithParams` on the
// given argument, if an argument is given
function updateRatApproxs(toUpdate) {
  if (moreRat < 1 || (toUpdate && toUpdate !== "moreRat")) {
    moreRat = defaultMoreRat;
  }

  const primeLimit = tryParseInt($('#primeLimit').val());
  const oddLimit   = tryParseInt($('#oddLimit')  .val());
  const sortRat    = $('#sortRat').val();
  updateDropdown($('#primeLimit'), primeLimitOpts, primeLimit);
  updateDropdown($('#oddLimit')  , oddLimitOpts(sortRat), oddLimit);
  updateDropdown($('#sortRat')   , sortRatOpts(oddLimit), sortRat);

  const cutoffDenom = res.edoSteps ? res.edoSteps[1] : 12;
  $('#cutoffRat').html("±" + fmtCents(600/cutoffDenom, 1));

  const params = { cutoff: microtonal_utils.Interval(2).pow(1, 2*cutoffDenom)
                 , primeLimit: isNaN(primeLimit) ? undefined : primeLimit
                 , oddLimit  : isNaN(oddLimit)   ? undefined : oddLimit
                 , numIterations: moreRat };
  const fn = sortRat === "difference"    ? microtonal_utils.bestRationalApproxsByDiff :
             sortRat === "denominator"   ? microtonal_utils.bestRationalApproxsByDenom :
             sortRat === "Tenney height" ? microtonal_utils.bestRationalApproxsByHeight
                                         : microtonal_utils.bestRationalApproxsByNo2sHeight;
  const ratApproxsOut = fn(res.intv, params);
  const ratApproxs = sortRat === "difference" ? ratApproxsOut.slice(0,10*moreRat)
                                              : ratApproxsOut[1];
  $('#ratTable').empty();
  for (const {ratio, diff} of ratApproxs) {
    let row = $('<tr>');
    const lhs = fmtExtExprLink(toRatioStr(ratio));
    row.append($('<td>').addClass("approxsLeftColumn").html(lhs));
    let diffStr = "exact";
    if (diff != 0) {
      diffStr = (diff > 0 ? "+" : "-") + fmtCents(Math.abs(diff), 3, true);
    }
    row.append($('<td>').addClass("approxsRightColumn").html(diffStr));
    $('#ratTable').append(row);
  }

  if (sortRat === "difference" && ratApproxsOut.length > 10*moreRat) {
    let link = $('<a>').attr("href", "javascript:void(0)")
                       .attr("id", "ratTableMoreLink")
                       .html("show more");
    link.click(function() { moreRat++; updateRatApproxs("moreRat"); });
    $('#ratTableMore').html(link);
  }
  else if (sortRat !== "difference" && !ratApproxsOut[0]) {
    const bnd = sortRat === "denominator"   ? moreRat*100 :
                sortRat === "Tenney height" ? Math.log2(moreRat*microtonal_utils.bestRationalApproxsByHeightIterationSize(params.primeLimit)).toFixed(2)
                                            : Math.log2(2*moreRat*microtonal_utils.bestRationalApproxsByNo2sHeightIterationSize(params.primeLimit) + 1).toFixed(2);
    const abbr = sortRat === "denominator"   ? "d" :
                 sortRat === "Tenney height" ? "TH"
                                             : "no-2s TH";
    let link = $('<a>').attr("href", "javascript:void(0)")
                       .attr("id", "ratTableMoreLink")
                       .html("show more (" + abbr + " > " + bnd + ")");
    link.click(function() { moreRat++; updateRatApproxs("moreRat"); });
    $('#ratTableMore').html(link);
  }
  else {
    const text = "no " + (ratApproxs.length > 0 ? "more " : "") + "results";
    $('#ratTableMore').html(text);
  }

  if (toUpdate) {
    let params = {"moreRat": moreRat == defaultMoreRat ? "" : moreRat};
    if ($('#' + toUpdate).val()) { params[toUpdate] = $('#' + toUpdate).val(); }
    updateURLWithParams(params, moreRat != defaultMoreRat);
  }
}

// Update the best EDO approximations dropdowns and table based on the
// current value of the dropdowns, and call `updateURLWithParams` on the
// given argument, if an argument is given
function updateEDOApproxs(toUpdate) {
  if (moreEDO < 1 || (toUpdate && toUpdate !== "moreEDO")) {
    moreEDO = defaultMoreEDO;
  }

  const loEDO   = parseInt($('#loEDO').val());
  const hiEDO   = parseInt($('#hiEDO').val());
  const sortEDO = $('#sortEDO').val();
  updateDropdown($('#loEDO')  , loEDOOpts(hiEDO), loEDO);
  updateDropdown($('#hiEDO')  , hiEDOOpts(loEDO), hiEDO);
  updateDropdown($('#sortEDO'), sortEDOOpts(), sortEDO);

  if (sortEDO === "difference") {
    $('#cutoffEDOSpan').addClass("hidden");
  }
  else {
    $('#cutoffEDOSpan').removeClass("hidden");
    $('#cutoffEDO').html("±50c");
  }

  const params = { startEDO: loEDO, endEDO: hiEDO };
  const fn = sortEDO === "difference" ? microtonal_utils.bestEDOApproxsByDiff
                                      : microtonal_utils.bestEDOApproxsByEDO;
  const edoApproxs = fn(res.intv, params);

  $('#edoTable').empty();
  for (let {steps, diff} of edoApproxs.slice(0,10*moreEDO)) {
    let row = $('<tr>');
    let firstNonZero = steps.findIndex(step => step[0] != 0);
    if (firstNonZero == -1) { firstNonZero = steps.length; }
    let stepStrs = steps.map(step => fmtExtExprLink(fmtEDOStep(step)).prop("outerHTML"));
    if (firstNonZero >= 4) {
      stepStrs = stepStrs.slice(0,2).concat(["..."]).concat(stepStrs.slice(firstNonZero-1));
    }
    const lhs = stepStrs.join(", ");
    row.append($('<td>').addClass("approxsLeftColumn").html(lhs));
    let diffStr = diff == 0 ? "exact" : (diff < 0 ? "-" : "+") +
                                        fmtCents(Math.abs(diff), 3, true);
    row.append($('<td>').addClass("approxsRightColumn").html(diffStr));
    $("#edoTable").append(row);
  }

  if (edoApproxs.length > 10*moreEDO) {
    let link = $('<a>').attr("href", "javascript:void(0)")
                       .attr("id", "edoTableMoreLink")
                       .html("show more");
    link.click(function() { moreEDO++; updateEDOApproxs("moreEDO"); });
    $('#edoTableMore').html(link);
  }
  else {
    const text = "no " + (edoApproxs.length > 0 ? "more " : "") + "results";
    $('#edoTableMore').html(text);
  }

  if (toUpdate) {
    let params = {"moreEDO": moreEDO == defaultMoreEDO ? "" : moreEDO};
    if ($('#' + toUpdate).val()) { params[toUpdate] = $('#' + toUpdate).val(); }
    updateURLWithParams(params, moreEDO != defaultMoreEDO);
  }
}

// Update all EDO result tables
function updateEDOResults(toUpdate) {
  if (moreEDORat < 1 || (toUpdate && toUpdate !== "moreEDORat")) {
    moreEDORat = defaultMoreEDORat;
  }
  if (moreEDOIntv < 1 || (toUpdate && toUpdate !== "moreEDOIntv")) {
    moreEDOIntv = defaultMoreEDORat;
  }

  const edoPrimeLimit        = tryParseInt($('#edoPrimeLimit').val());
  const edoRelCutoff         = $('#edoRelCutoff').val();
  const edoBaseNote          = $('#edoBaseNote').val();
  const edoOddLimit          = tryParseInt($('#edoOddLimit').val());
  const edoApproxsPrimeLimit = tryParseInt($('#edoApproxsPrimeLimit').val());
  const edoApproxsOddLimit   = tryParseInt($('#edoApproxsOddLimit').val());
  updateDropdown($('#edoPrimeLimit')       , edoPrimeLimitOpts, edoPrimeLimit);
  updateDropdown($('#edoRelCutoff')        , edoRelCutoffOpts, edoRelCutoff);
  updateDropdown($('#edoBaseNote')         , edoBaseNoteOpts, edoBaseNote);
  updateDropdown($('#edoOddLimit')         , edoOddLimitOpts, edoOddLimit);
  updateDropdown($('#edoApproxsPrimeLimit'), edoApproxsPrimeLimitOpts, edoApproxsPrimeLimit);
  updateDropdown($('#edoApproxsOddLimit')  , edoApproxsOddLimitOpts, edoApproxsOddLimit);

  const edoRelCutoffVal = edoRelCutoffVals[edoRelCutoffOpts.indexOf(edoRelCutoff)];
  const edoBaseNoteVal = microtonal_utils.parsePyNote(edoBaseNote);
  let [noteOffset, refIntvToA4] = [microtonal_utils.edoPy(res.edo, edoBaseNoteVal), undefined];
  if (res.edo % 7 == 0 && (edoBaseNote.includes("♯") || edoBaseNote.includes("♭"))) {
    noteOffset = 0;
    refIntvToA4 = edoBaseNoteVal;
  }
  const baseHertz = microtonal_utils.parseCvt(edoBaseNote + "\\" + res.edo + " where " + microtonal_utils.pyNote(res.ref.intvToA4) + " = " + res.ref.hertz + "Hz").hertz;

  // EDO prime mappings
  $('#edoPrimesTable').empty();
  const primesHeaders = ["Prime",
                         "Error (" + $('<a>').attr("href", "https://en.wikipedia.org/wiki/Cent_(music)")
                                             .text("cents").prop("outerHTML") + ")",
                         $('<a>').attr("href", "https://en.xen.wiki/w/Relative_interval_error")
                                 .text("Error (relative)"),
                         "Mapping",
                         $('<a>').attr("href", "https://en.xen.wiki/w/Octave_reduction")
                                 .text("Red.").prop("outerHTML") + " mapping",
                         "Highest power allowed in approxs. below" + $('#edoRelCutoffExplQ').prop("outerHTML")];
  let primesDat = [];
  for (const p of microtonal_utils.primes()) {
    if (p == 2) { continue; }
    if (p > edoPrimeLimit) { break; }
    const [n, err] = microtonal_utils.edoPrimeApprox(res.edo, p);
    const relErr = err.valueOf_log() * res.edo;
    let col = [p];
    const errC = err.toCents();
    col.push((errC < 0 ? "-" : "+") + fmtCents(Math.abs(errC), 2, true));
    col.push((relErr < 0 ? "-" : "+") + (Math.abs(100*relErr).toFixed(1)) + "%");
    col.push(fmtExtExprLink(n, n + "\\" + res.edo));
    const nRed = microtonal_utils.mod(n, res.edo);
    col.push(fmtExtExprLink(nRed, nRed + "\\" + res.edo));
    col.push(Math.floor(edoRelCutoffVal / Math.abs(relErr)));
    primesDat.push(col);
  }
  for (let j = 0; j < primesDat[0].length; j++) {
    if (res.edo == 12 && j == 2) { continue; }
    let row = $('<tr>');
    row.append($('<th>').html(primesHeaders[j]).addClass("edoPrimesTableLeftHeader"));
    for (let i = 0; i < primesDat.length; i++) {
      row.append((j == 0 ? $('<th>') : $('<td>')).html(primesDat[i][j]));
    }
    $('#edoPrimesTable').append(row);
  }

  // EDO intervals
  let opts = { primeLimit: edoPrimeLimit,
               oddLimit: isNaN(edoOddLimit) ? undefined : edoOddLimit,
               primeRelErrCutoff: 2*edoRelCutoffVal,
               numIterations: moreEDOIntv };
  let approxs = microtonal_utils.bestRationalApproxsOfEDOByStep(res.edo, opts);
  $('#edoIntvsTable').empty();
  let header = $('<tr>');
  header.append($('<th>').html("Steps"));
  header.append($('<th>').html("Cents"));
  header.append($('<th>').html("Ups-and-downs notation").attr("colspan", 3));
  header.append($('<th>').html($('<a>').attr("href", "https://en.xen.wiki/w/Consistent")
                                       .text("Consistent").prop("outerHTML")
                               + " rational approximations")
                         .addClass("edoIntvsTableRightHeader"));
  header.append($('<th>').html("Audio"));
  $('#edoIntvsTable').append(header);
  for (let {steps, cents, ups_and_downs, ups_and_downs_verbose} of res.intvs) {
    let row = $('<tr>').addClass("hoverSwap");
    row.append($('<td>').html(fmtExtExprLink(steps, steps + "\\" + res.edo)));
    row.append($('<td>').html(fmtExtExprLink(fmtCents(cents, 2), cents + "c")));
    if (res.edo % 7 == 0) { ups_and_downs_verbose = ups_and_downs_verbose.map(x => x.replace("perfect", "")); }
    row.append($('<td>').html(ups_and_downs_verbose.map(x => fmtExtExprLink(x, x + " \\ " + res.edo).prop("outerHTML")).join(",<br>")));
    const uds_on = ups_and_downs.map(x => fmtExtExprLink(x, x + "\\" + res.edo).prop("outerHTML")).join(",<br>");
    const uds_off = microtonal_utils.updnsSymb(res.edo, steps, {useExps:1, useHTMLExps:1})
                                    .map((x,i) => fmtExtExprLink(x, ups_and_downs[i] + "\\" + res.edo).prop("outerHTML")).join(",<br>");
    const udsCell = $('<td>');
    udsCell.append($('<span>').addClass("hoverSwap_on").html(uds_on));
    udsCell.append($('<span>').addClass("hoverSwap_off").html(uds_off));
    row.append(udsCell);
    let udsNotes_on = microtonal_utils.updnsNote(res.edo, steps + noteOffset, {refIntvToA4: refIntvToA4, ignoreOctave: 1, useExps: 1});
    let udsNotes_off = microtonal_utils.updnsNote(res.edo, steps + noteOffset, {refIntvToA4: refIntvToA4, ignoreOctave: 1, useExps: 1, useHTMLExps: 1});
    if (res.edo % 5 == 0) {
      udsNotes_on = udsNotes_on.filter(s => edoBaseNote.includes("♯") ? s.includes("♯") :
                                            edoBaseNote.includes("♭") ? s.includes("♭")
                                              : !s.includes("♯") && !s.includes("♭"));
      udsNotes_off = udsNotes_off.filter(s => edoBaseNote.includes("♯") ? s.includes("♯") :
                                              edoBaseNote.includes("♭") ? s.includes("♭")
                                                : !s.includes("♯") && !s.includes("♭"));
    }
    const udsNote_on = udsNotes_on.map(x => fmtExtExprLink(x, x + "\\" + res.edo).prop("outerHTML")).join(",<br>");
    const udsNote_off = udsNotes_off.map((x,i) => fmtExtExprLink(x, udsNotes_on[i] + "\\" + res.edo).prop("outerHTML")).join(",<br>");
    const udsNoteCell = $('<td>');
    udsNoteCell.append($('<span>').addClass("hoverSwap_on").html(udsNote_on));
    udsNoteCell.append($('<span>').addClass("hoverSwap_off").html(udsNote_off));
    row.append(udsNoteCell);
    const apxCell = $('<td>').html(approxs[steps].map(x => fmtExtExprLink(x.ratio.toFraction()).prop("outerHTML")).join(", "));
    apxCell.addClass("edoIntvsTableRightColumn");
    row.append(apxCell);
    const audioCell = $('<td>');
    const topHertz = baseHertz * Math.pow(2, steps / res.edo);
    const melButton = $('<button>').addClass("edoAudioButton").text("M");
    melButton.click(function () {
      synth.playFreq(9, baseHertz, percussive(1.75));
      synth.stopFreqAfter(9, 10);
      setTimeout(function() {
        synth.playFreq(10+steps, topHertz, percussive(1.75));
        synth.stopFreqAfter(10+steps, 10);
      }, 700);
    });
    audioCell.append($('<div>').addClass("buttonContainer").html(melButton));
    const harmButton = $('<button>').addClass("edoAudioButton").text("H");
    harmButton.click(function () {
      synth.playFreq(9, baseHertz, percussive(1.75));
      synth.playFreq(10+steps, topHertz, percussive(1.75));
      synth.stopFreqAfter(9, 10);
      synth.stopFreqAfter(10+steps, 10);
    });
    audioCell.append($('<div>').addClass("buttonContainer").html(harmButton));
    row.append(audioCell);
    $('#edoIntvsTable').append(row);
  }
  const linkExtra = moreEDOIntv > 1 ? " (x" + moreEDOIntv + ")" : "";
  let link = $('<a>').attr("href", "javascript:void(0)")
                     .attr("id", "edoIntvsMoreLink")
                     .html("load more approximations" + linkExtra);
  link.click(function() { moreEDOIntv++; updateEDOResults("moreEDOIntv"); });
  $('#edoIntvsMore').html(link);

  // EDO best rational approximations
  opts = { primeLimit: isNaN(edoApproxsPrimeLimit) ? undefined : edoApproxsPrimeLimit,
           oddLimit: edoApproxsOddLimit,
           primeRelErrCutoff: 2*edoRelCutoffVal };
  const approxsOut = microtonal_utils.bestRationalApproxsOfEDOByDist(res.edo, opts);
  approxs = approxsOut.slice(0,10*moreEDORat)
  $('#edoApproxsTable').empty();
  for (const {inconsistent, overErr, ratios, dist} of approxs) {
    let row = $('<tr>');
    const note = inconsistent && overErr ? "(p) (i)" : inconsistent ? "(i)" : overErr ? "(p)" : "";
    row.append($('<td>').html(note));
    const lhs = ratios.map(x => fmtExtExprLink(toRatioStr(x)).prop("outerHTML")).join(", ");
    row.append($('<td>').addClass("approxsLeftColumn").html(lhs));
    let distStr = "exact";
    if (dist != 0) {
      distStr = fmtCents(Math.abs(dist), 3, true);
    }
    row.append($('<td>').addClass("approxsRightColumn").html(distStr));
    $('#edoApproxsTable').append(row);
  }

  if (approxsOut.length > 10*moreEDORat) {
    let link = $('<a>').attr("href", "javascript:void(0)")
                       .attr("id", "edoApproxsTableMoreLink")
                       .html("show more");
    link.click(function() { moreEDORat++; updateEDOResults("moreEDORat"); });
    $('#edoApproxsTableMore').html(link);
  }
  else {
    const text = "no " + (approxs.length > 0 ? "more " : "") + "results";
    $('#edoApproxsTableMore').html(text);
  }

  if (toUpdate) {
    let params = {"moreEDORat": moreEDORat == defaultMoreEDORat ? "" : moreEDORat,
                  "moreEDOIntv": moreEDOIntv == defaultMoreEDOIntv ? "" : moreEDOIntv};
    if ($('#' + toUpdate).val()) { params[toUpdate] = $('#' + toUpdate).val(); }
    updateURLWithParams(params, moreRat != defaultMoreEDORat);
  }
  return baseHertz;
}

// The function to be called if the "Play/pause note" button is clicked
function toggleNote() {
  if ($('#playNoteToggle').html()[0] == "▶") {
    synth.playFreq(0, res.hertz, organ);
    $('#playNoteToggle').html("■ Stop note");
  }
  else {
    stopNoteIfActive();
  }
}
function stopNoteIfActive() {
  if ($('#playNoteToggle').html()[0] != "▶") {
    synth.stopFreqAfter(0, 0);
    $('#playNoteToggle').html("▶ Play note");
  }
}

// Play the melodic interval between res.ref.hertz and res.hertz
function playMelodic() {
  stopNoteIfActive();
  synth.playFreq(1, res.ref.hertz, percussive(1.75));
  synth.stopFreqAfter(1, 10);
  setTimeout(function() {
    synth.playFreq(2, res.hertz, percussive(1.75));
    synth.stopFreqAfter(2, 10);
  }, 700);
}

// Play the harmonic interval between res.ref.hertz and res.hertz
function playHarmonic() {
  stopNoteIfActive();
  synth.playFreq(3, res.ref.hertz, percussive(1.75));
  synth.playFreq(4, res.hertz    , percussive(1.75));
  synth.stopFreqAfter(3, 10);
  synth.stopFreqAfter(4, 10);
}

// ================================================================
// Handling the URL and browser state
// ================================================================

function updateURLWithParams(paramsToUpdate, doReplace) {
  const url = new URL(window.location);
  for (const [param, val] of Object.entries(paramsToUpdate)) {
    if (val != undefined && (!val.trim || val.trim() !== "")) {
      url.searchParams.set(param, val);
    }
    else {
      url.searchParams.delete(param);
    }
  }
  updateURLTo(url, doReplace);
}

function updateURLTo(newURL, doReplace) {
  const newURLStr = reformatURL(newURL.toString());
  const st = { html: $("#output").prop("outerHTML"), res: res };
  if (doReplace) {
    console.log(Date.now() + " [replaced] " + newURL.searchParams);
    console.log(res);
    history.replaceState(st, $("#expr").val(), newURLStr);
  }
  else {
    console.log(Date.now() + " [pushed] " + newURL.searchParams);
    console.log(res);
    history.pushState(st, $("#expr").val(), newURLStr);
  }
}

function initState() {
  const url = new URL(window.location);
  // On my machine firefox has weird behavior on refresh, so I always pushState
  // when refreshing on firefox on a non-blank page (which still gives weird
  // behavior, but at least it's better)
  // const doReplace =
  //   [...url.searchParams.entries()].length == 0;
  //   || !navigator.userAgent.toLowerCase().includes("firefox")
  //   || (performance && performance.getEntriesByType("navigation")[0].type != "reload");
  // ^ Commenting out this "fix" for now, because I can't replicate it (7/7/21)
  updateURLTo(url, true); // doReplace);
}

window.onpopstate = function(e) {
  const url = new URL(window.location);
  console.log(Date.now() + " [popped] " + url.searchParams);
  if (e && e.state && e.state.res) { console.log(e.state.res); }
  else if (e) { console.warn("bad state!!"); console.warn(e); }
  setStateFromURL(e);
};

function setStateFromURL(e) {
  const urlParams = new URLSearchParams(window.location.search);
  setStateFromParams(urlParams, e);
}

function setStateFromParams(urlParams, e) {
  function getWithDefault(urlParams, param, deflt) {
    return urlParams.has(param) ? urlParams.get(param) : deflt;
  }
  // pull everything from urlParams
  let expr = getWithDefault(urlParams, 'q', "");
  if (urlParams.has('expr')) {
    expr = urlParams.get('expr');
    updateURLWithParams({q: expr, expr: ""}, true);
  }
  const primeLimit = getWithDefault(urlParams, 'primeLimit', defaultPrimeLimit);
  const oddLimit   = getWithDefault(urlParams, 'oddLimit'  , defaultOddLimit);
  const sortRat    = getWithDefault(urlParams, 'sortRat'   , defaultSortRat);
  const loEDO      = getWithDefault(urlParams, 'loEDO'     , defaultLoEDO);
  const hiEDO      = getWithDefault(urlParams, 'hiEDO'     , defaultHiEDO);
  const sortEDO    = getWithDefault(urlParams, 'sortEDO'   , defaultSortEDO);
  moreRat          = getWithDefault(urlParams, 'moreRat'   , defaultMoreRat);
  moreEDO          = getWithDefault(urlParams, 'moreEDO'   , defaultMoreEDO);
  const edoPrimeLimit        = getWithDefault(urlParams, 'edoPrimeLimit'       , defaultEDOPrimeLimit);
  const edoRelCutoff         = getWithDefault(urlParams, 'edoRelCutoff'        , defaultEDORelCutoff);
  const edoBaseNote          = getWithDefault(urlParams, 'edoBaseNote'         , defaultEDOBaseNote);
  const edoOddLimit          = getWithDefault(urlParams, 'edoOddLimit'         , defaultEDOOddLimit);
  const edoApproxsPrimeLimit = getWithDefault(urlParams, 'edoApproxsPrimeLimit', defaultEDOApproxsPrimeLimit);
  const edoApproxsOddLimit   = getWithDefault(urlParams, 'edoApproxsOddLimit'  , defaultEDOApproxsOddLimit);
  moreEDORat                 = getWithDefault(urlParams, 'moreEDORat'          , defaultMoreEDORat);
  moreEDOIntv                = getWithDefault(urlParams, 'moreEDOIntv'         , defaultMoreEDOIntv);
  // update the expr fields and all the dropdowns based on the above
  $('#expr').val(expr);
  updateDropdown($('#primeLimit'), primeLimitOpts, primeLimit);
  updateDropdown($('#oddLimit')  , oddLimitOpts(sortRat), oddLimit);
  updateDropdown($('#sortRat')   , sortRatOpts(oddLimit), sortRat);
  updateDropdown($('#loEDO')     , loEDOOpts(hiEDO), loEDO);
  updateDropdown($('#hiEDO')     , hiEDOOpts(loEDO), hiEDO);
  updateDropdown($('#sortEDO')   , sortEDOOpts(), sortEDO);
  updateDropdown($('#edoPrimeLimit')       , edoPrimeLimitOpts, edoPrimeLimit);
  updateDropdown($('#edoRelCutoff')        , edoRelCutoffOpts, edoRelCutoff);
  updateDropdown($('#edoBaseNote')         , edoBaseNoteOpts, edoBaseNote);
  updateDropdown($('#edoOddLimit')         , edoOddLimitOpts, edoOddLimit);
  updateDropdown($('#edoApproxsPrimeLimit'), edoApproxsPrimeLimitOpts, edoApproxsPrimeLimit);
  updateDropdown($('#edoApproxsOddLimit')  , edoApproxsOddLimitOpts, edoApproxsOddLimit);
  updateTitle();
  // either directly set the output div html if we have a valid state, or
  // call updateResults to generate it
  if (e && e.state && e.state.html && e.state.html.trim() !== "") {
    $('#output').replaceWith(e.state.html);
    res = e.state.res;
    addXenWikiLink();
  }
  else {
    updateResults();
  }
  // set (or refresh) the click/change events for all the interactables in the
  // output div
  $('#playIntvMelodic') .click(() => playMelodic());
  $('#playNoteMelodic') .click(() => playMelodic());
  $('#playIntvHarmonic').click(() => playHarmonic());
  $('#playNoteHarmonic').click(() => playHarmonic());
  $('#playNoteToggle')  .click(() => toggleNote());
  $('#primeLimit').change(() => updateRatApproxs('primeLimit'));
  $('#oddLimit')  .change(() => updateRatApproxs('oddLimit'));
  $('#sortRat')   .change(() => updateRatApproxs('sortRat'));
  $('#loEDO')     .change(() => updateEDOApproxs('loEDO'));
  $('#hiEDO')     .change(() => updateEDOApproxs('hiEDO'));
  $('#sortEDO')   .change(() => updateEDOApproxs('sortEDO'));
  $('#ratTableMoreLink').click(function() { moreRat++; updateRatApproxs("moreRat"); });
  $('#edoTableMoreLink').click(function() { moreEdo++; updateRatApproxs("moreEDO"); });
  $('#edoPrimeLimit')       .change(() => updateEDOResults('edoPrimeLimit'));
  $('#edoRelCutoff')        .change(() => updateEDOResults('edoRelCutoff'));
  $('#edoBaseNote')         .change(() => updateEDOResults('edoBaseNote'));
  $('#edoOddLimit')         .change(() => updateEDOResults('edoOddLimit'));
  $('#edoApproxsPrimeLimit').change(() => updateEDOResults('edoApproxsPrimeLimit'));
  $('#edoApproxsOddLimit')  .change(() => updateEDOResults('edoApproxsOddLimit'));
  $('#edoIntvsMoreLink')       .click(function() { moreEDOIntv++; updateRatApproxs("moreEDOIntv"); });
  $('#edoApproxsTableMoreLink').click(function() { moreEDORat++; updateRatApproxs("moreEDORat"); });
}

// ================================================================
// Initalizing
// ================================================================

$(document).ready(function() {
  setStateFromURL();
  initState();

  // log if we're coming from a new load
  if (performance.navigation.type == 0) {
    let xs = ["new load"];
    if (document.referrer) {
      const referrerURL = new URL(document.referrer);
      if (referrerURL.hostname.includes("yacavone.net") &&
          referrerURL.pathname.substr(0,9) === "/xen-calc") {
        xs[0] += " (rel)";
      }
      else {
        xs.push("z " + referrerURL.hostname);
      }
    }
    if ($('#expr').val()) { logResultTypes(res, xs); }
    else { logStrs(xs); }
  }

  // reset button
  $('#reset').click(function () {
    setStateFromParams(new URLSearchParams());
    const url = new URL(window.location);
    for (const [param,_] of [...url.searchParams.entries()]) {
      url.searchParams.delete(param);
    }
    url.hash = "";
    updateURLTo(url);
  });

  // accidental buttons
  $('#add_dbl_flat') .click(function() { insertAtCursor("𝄫"); });
  $('#add_flat')     .click(function() { insertAtCursor("♭"); });
  $('#add_nat')      .click(function() { insertAtCursor("♮"); });
  $('#add_sharp')    .click(function() { insertAtCursor("♯"); });
  $('#add_dbl_sharp').click(function() { insertAtCursor("𝄪"); });

  // pressing enter while in the text box clicks the enter button
  $('#expr').keydown(function(event) {
    if (event.which === 13) {
      event.preventDefault();
      $('#enter').addClass('buttonActive');
    }
  });
  $('#expr').keyup(function(event) {
    if (event.which === 13) {
      $('#enter').removeClass('buttonActive');
      $('#enter').click();
    }
  });

  // pressing enter!
  $('#enter').click(function() {
    moreRat = defaultMoreRat; moreEDO = defaultMoreEDO;
    moreEDORat = defaultMoreEDORat; moreEDOIntv = defaultMoreEDOIntv;
    updateTitle();
    updateResults();
    let params = {q: $('#expr').val()};
    params["moreRat"] = ""; params["moreEDO"] = "";
    params["moreEDORat"] = ""; params["moreEDOIntv"] = "";
    if (res.type == "interval" || res.type == "note") {
      params["edoPrimeLimit"] = "";
      params["edoRelCutoff"] = "";
      params["edoBaseNote"] = "";
      params["edoOddLimit"] = "";
      params["edoApproxsPrimeLimit"] = "";
      params["edoApproxsOddLimit"] = "";
    }
    else {
      params["primeLimit"] = "";
      params["oddLimit"] = "";
      params["sortRat"] = "";
      params["loEDO"] = "";
      params["hiEDO"] = "";
      params["sortEDO"] = "";
    }
    updateURLWithParams(params);
    logResultTypes(res);
  });
});
