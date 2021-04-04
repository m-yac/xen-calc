
// ================================================================
// Utility functions
// ================================================================

function tryParseInt(x) {
  return isNaN(x) ? x : parseInt(x);
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

// ================================================================
// State variables
// ================================================================

const defaultPrimeLimit = 13;
function primeLimitOpts() {
  return [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, "–"];
}

const defaultOddLimit = 81;
function oddLimitOpts(sortRat) {
  let opts = range(3, 100, 2); // all odd numbers from 3 to 99
  if (sortRat !== "difference") { opts.push("-"); }
  return opts;
}

const defaultSortRat = "Tenney height";
function sortRatOpts(oddLimit) {
  let opts = ["Tenney height"];
  if (oddLimit !== "-") { opts.push("difference"); }
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

var res = {};

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
  if (trailingZeros) { return  cents.toFixed(decimalPlaces) + "c"; }
  else               { return +cents.toFixed(decimalPlaces) + "c"; }
}
// Given a value in hertz, a number of decimal places, and a boolean indicating
//  whether to add trailing zeros, return the value truncated to the given
//  number of decimal places followed by trailing zeros if the boolean is set
//  and the letters "Hz".
function fmtHertz(cents, decimalPlaces, trailingZeros) {
  if (trailingZeros) { return  cents.toFixed(decimalPlaces) + "Hz"; }
  else               { return +cents.toFixed(decimalPlaces) + "Hz"; }
}
// Given an interval, returns its factorization as a string
function fmtFactorization(intv) {
  let fact = [];
  for (const [p,e] of Object.entries(intv)) {
    fact.push(p + "^" + (e.d == 1 ? e.s*e.n : "(" + e.toFraction() + ")"));
  }
  return fact.join(" * ");
}
// Given an interval, returns it formatted as a ratio if it's a ratio, an
//  nth root if its an nth root for n <= 6 or n equal to the second argument, or
//  otherwise its factorization
function fmtExpression(intv, prefEDO) {
  try {
    if (intv.toNthRoot().n <= 6) {
      return intv.toNthRootString();
    }
  }
  catch (err) {}
  return fmtFactorization(intv);
}
// Wrap a given string in an <a> tag which when clicked, opens the calculator
//  in a new window/tab with the given expression
function fmtExtExprLink(str, newTab) {
  let link = $('<a>').attr("href", "?expr=" + encodeURIComponent(str)).html(str);
  if (newTab) {
    link.attr("target", "_blank");
  }
  return link;
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
  let [typeStr, ret] = ["", []];
  // Add interval-specific rows
  if (res.type === "interval") {
    typeStr = "Interval results";
    ret.push(["Size in cents:", fmtExtExprLink(fmtCents(res.cents, 5))]);
    if (res.ratio) {
      ret.push(["Ratio:", fmtExtExprLink(res.ratio.toFraction())]);
    }
    else {
      try {
        if (res.intv.toNthRoot().n <= 6) {
          ret.push(["Expression:", fmtExtExprLink(res.intv.toNthRootString())]);
        }
      }
      catch (err) {}
    }
    const fact = fmtFactorization(res.intv);
    if (fact.length > 0) {
      ret.push(["Factorization:", fmtExtExprLink(fact)]);
      let monzo = res.intv.toMonzo();
      if (res.intv.isFrac()) {
        ret.push(["Monzo:", "|" + monzo.join(", ") + "⟩"]);
      }
      else {
        monzo = monzo.map(x => x.toFraction());
        ret.push(["Fractional monzo:", "|" + monzo.join(", ") + "⟩"]);
      }
    }
    if (res.ratio) {
      ret.push(["Tenney height:", +res.height.tenney.toFixed(5) + " (log2(" + res.height.benedetti + "))"])
    }
    if (res.edoSteps) {
      ret.push(["EDO steps:", fmtExtExprLink(fmtEDOStep(res.edoSteps))]);
    }
  }
  // Add note-specific rows
  if (res.type === "note") {
    typeStr = "Note results";
    ret.push(["Frequency in hertz:", fmtExtExprLink(fmtHertz(res.hertz, 5))]);
    ret.push(["Tuning meter read-out:", res.tuningMeter]);
  }
  // Add any symbols
  if (res.symb) {
    if (res.symb["FJS"] &&
        // for now we only have integer accidentals, since I'm not sure how
        //  useful showing non-integer accidentals actually is
        !(res.symb["FJS"].includes("root") || res.symb["FJS"].includes("sqrt"))) {
      ret.push(["FJS name:", fmtExtExprLink(res.symb["FJS"])]);
    }
    if (res.symb["NFJS"] &&
        // for now we only have integer accidentals, since I'm not sure how
        //  useful showing non-integer accidentals actually is
        !(res.symb["NFJS"].includes("root") || res.symb["NFJS"].includes("sqrt"))) {
      ret.push(["Neutral FJS name:", fmtExtExprLink(res.symb["NFJS"])]);
      // TODO fix the above link if the base interval is not neutral ^
    }
    if (res.symb["ups-and-downs"]) {
      const symbs = res.symb["ups-and-downs"].map(symb => fmtExtExprLink(symb).prop('outerHTML'));
      ret.push(["Ups-and-downs notation:", symbs.join(", ")]);
    }
  }
  const addS = res.english && res.english.length > 1 ? "(s):" : ":";
  if (res.english && res.english.length > 0){
    const end = res.english.length > 1 ? "(s):" : ":";
    ret.push(["(Possible) English name" + end, res.english.join("<br>")]);
  }
  // Add a note's interval reference
  if (res.type === "note" && !res.intvToRef.equals(1)) {
    ret.push([]);
    const refSymb = microtonal_utils.pyNote(res.ref.intvToA4);
    if (res.edoStepsToRef) {
      ret.push(["Interval to reference note:",
                fmtExtExprLink(fmtEDOStep(res.edoStepsToRef))]);
    }
    else {
      ret.push(["Interval to reference note:",
                fmtExtExprLink(fmtExpression(res.intvToRef))]);
    }
    ret.push(["Reference note and frequency:", refSymb + " = " + fmtHertz(res.ref.hertz, 2)])
  }
  return [typeStr, ret];
}

// Updates the entire results section based on the current expression
function updateResults() {
  if ($('#expr').val().trim() === "") {
    $('#errors').addClass("hidden");
    $('#results').addClass("hidden");
    return;
  }
  try {
    $('#errors').addClass("hidden");
    $('#results').removeClass("hidden");
    const [typeStr, rows] = getResults();
    $('#resHeader').html(typeStr);
    $('#resTable').empty();
    for (const [n,v] of rows) {
      let row = $('<tr>');
      row.append($('<td>').addClass("resLeftColumn").html(n));
      row.append($('<td>').addClass("resRightColumn").html(v));
      $('#resTable').append(row);
    }
    if (res.ratio) {
      addXenWikiLink(res.ratio.toFraction());
    }
    if (res.type === "interval") {
      $('#resApproxs').removeClass("hidden");
      const cutoff = res.edoSteps ? 600/res.edoSteps[1] : 50;
      $('#cutoffRat').html("±" + fmtCents(cutoff,1));
      updateRatApproxs();
      $('#cutoffEDO').html("±50c");
      updateEDOApproxs();
    }
    else {
      $('#resApproxs').addClass("hidden");
    }
  }
  catch (err) {
    $('#errors').removeClass("hidden");
    $('#results').addClass("hidden");
    $('#errors').html($('<pre>').addClass("parseError")
                                .html(err.toString().replace("\n","<br>")));
  }
}

// Asynchronously add a Xenharmonic wiki link (if it exists) to the results
// table
function addXenWikiLink(xenPageName) {
  const xenURL = "https://en.xen.wiki/w/" + xenPageName;
  const pageExists = xenWikiPageExists(xenPageName);
  if (pageExists) {
    pageExists.then(function(exists) {
      if (exists) {
        let link = $('<a>').attr("target", "_blank")
                           .attr("href", xenURL)
                           .append(xenURL);
        let row = $('<tr>');
        row.append($('<td>').addClass("resLeftColumn").html("Xenharmonic wiki page:"));
        row.append($('<td>').addClass("resRightColumn").html(link));
        $('#resTable').append(row);
      }
    });
  }
}

// Update the best rational approximations dropdowns and table based on the
// current value of the dropdowns, and call `updateURLWithParams` on the
// given argument, if an argument is given
function updateRatApproxs(toUpdate) {

  const primeLimit = tryParseInt($('#primeLimit').val());
  const oddLimit   = tryParseInt($('#oddLimit')  .val());
  const sortRat = $('#sortRat').val();
  updateDropdown($('#primeLimit'), primeLimitOpts(), primeLimit);
  updateDropdown($('#oddLimit')  , oddLimitOpts(sortRat), oddLimit);
  updateDropdown($('#sortRat')   , sortRatOpts(oddLimit), sortRat);

  const cutoff = res.edoSteps ? microtonal_utils.Interval(2).pow(1,2*res.edoSteps[1])
                              : undefined;
  const params = { cutoff: cutoff
                 , primeLimit: isNaN(primeLimit) ? undefined : primeLimit
                 , oddLimit  : isNaN(oddLimit)   ? undefined : oddLimit };
  const fn = sortRat === "difference" ? microtonal_utils.bestRationalApproxsByDiff
                                      : microtonal_utils.bestRationalApproxsByHeight;
  const ratApproxsOut = fn(res.intv, params);
  const ratApproxs = sortRat === "difference" ? ratApproxsOut.slice(0,10)
                                              : ratApproxsOut[1];
  $('#ratTable').empty();
  for (const {ratio, diff} of ratApproxs) {
    let row = $('<tr>');
    const lhs = fmtExtExprLink(ratio.toFraction());
    row.append($('<td>').addClass("approxsLeftColumn").html(lhs));
    let diffStr = "exact";
    if (diff != 0) {
      diffStr = (diff > 0 ? "+" : "-") + fmtCents(Math.abs(diff), 3, true);
    }
    row.append($('<td>').addClass("approxsRightColumn").html(diffStr));
    $('#ratTable').append(row);
  }

  let moreText = "";
  if (sortRat === "difference" && ratApproxsOut.length > 10) {
    moreText = "show more";
  }
  if (sortRat !== "difference") {
    if (ratApproxsOut[0]) {
      moreText = "no " + (ratApproxs.length > 0 ? "more " : "") + "results ";
    }
    else {
      moreText = "search for more";
    }
  }
  $('#ratTableMore').html(moreText);

  if (toUpdate) {
    updateURLWithParams({[toUpdate]: $('#' + toUpdate).val()});
  }
}

// Update the best EDO approximations dropdowns and table based on the
// current value of the dropdowns, and call `updateURLWithParams` on the
// given argument, if an argument is given
function updateEDOApproxs(toUpdate) {

  const loEDO   = parseInt($('#loEDO').val());
  const hiEDO   = parseInt($('#hiEDO').val());
  const sortEDO = $('#sortEDO').val();
  updateDropdown($('#loEDO')  , loEDOOpts(hiEDO), loEDO);
  updateDropdown($('#hiEDO')  , hiEDOOpts(loEDO), hiEDO);
  updateDropdown($('#sortEDO'), sortEDOOpts(), sortEDO);

  const params = { startEDO: loEDO, endEDO: hiEDO };
  const fn = sortEDO === "difference" ? microtonal_utils.bestEDOApproxsByDiff
                                      : microtonal_utils.bestEDOApproxsByEDO;
  const edoApproxs = fn(res.intv, params);

  $('#edoTable').empty();
  for (let {steps, diff} of edoApproxs.slice(0,10)) {
    let row = $('<tr>');
    let firstNonZero = steps.findIndex(step => step[0] != 0);
    if (firstNonZero == -1) { firstNonZero = steps.length; }
    let stepStrs = steps.map(fmtEDOStep);
    if (firstNonZero >= 4) {
      stepStrs = stepStrs.slice(0,2).concat(["..."]).concat(stepStrs.slice(firstNonZero-1));
    }
    const lhs = fmtExtExprLink(stepStrs.join(", "));
    row.append($('<td>').addClass("approxsLeftColumn").html(lhs));
    let diffStr = diff == 0 ? "exact" : (diff < 0 ? "+" : "-") +
                                        fmtCents(Math.abs(diff), 3, true);
    row.append($('<td>').addClass("approxsRightColumn").html(diffStr));
    $("#edoTable").append(row);
  }

  let moreText = "";
  if (edoApproxs.length > 10) {
    moreText = "show more";
  }
  $('#edoTableMore').html(moreText);

  if (toUpdate) {
    updateURLWithParams({[toUpdate]: $('#' + toUpdate).val()});
  }
}

// ================================================================
// Handling the URL and browser state
// ================================================================

function updateURLWithParams(toUpdate) {
  const url = new URL(window.location);
  for (const [param, val] of Object.entries(toUpdate)) {
    if (val != undefined && (!val.trim || val.trim() !== "")) {
      url.searchParams.set(param, val);
    }
    else {
      url.searchParams.delete(param);
    }
  }
  console.log(Date.now() + " [pushed] " + url.searchParams);
  console.log(res);
  const st = { html: $("#results").prop("outerHTML"), res: res };
  history.pushState(st, $("#expr").val(), url);
}

function initState() {
  const url = new URL(window.location);
  console.log(Date.now() + " [ready] " + url.searchParams);
  console.log(res);
  const st = { html: $("#results").prop("outerHTML"), res: res };
  // On my machine firefox has weird behavior on refresh, so I always pushState
  // (which still gives weird behavior, but at least it's better)
  if (navigator.userAgent.toLowerCase().includes("firefox")) {
    history.pushState(st, $("#expr").val(), url);
  }
  else {
    history.replaceState(st, $("#expr").val(), url);
  }
}

window.onpopstate = function(e) {
  const url = new URL(window.location);
  console.log(Date.now() + " [popped] " + url.searchParams);
  if (e && e.state && e.state.res) { console.log(e.state.res); }
  else if (e) { console.log("bad state!!"); console.log(e); }
  setStateFromURL(e);
};

function setStateFromURL(e) {
  function getWithDefault(urlParams, param, deflt) {
    return urlParams.has(param) ? urlParams.get(param) : deflt;
  }
  const urlParams = new URLSearchParams(window.location.search);
  const expr       = getWithDefault(urlParams, 'expr'      , "");
  const primeLimit = getWithDefault(urlParams, 'primeLimit', defaultPrimeLimit);
  const oddLimit   = getWithDefault(urlParams, 'oddLimit'  , defaultOddLimit);
  const sortRat    = getWithDefault(urlParams, 'sortRat'   , defaultSortRat);
  const loEDO      = getWithDefault(urlParams, 'loEDO'     , defaultLoEDO);
  const hiEDO      = getWithDefault(urlParams, 'hiEDO'     , defaultHiEDO);
  const sortEDO    = getWithDefault(urlParams, 'sortEDO'   , defaultSortEDO);
  moreRat          = getWithDefault(urlParams, 'moreRat'   , defaultMoreRat);
  moreEDO          = getWithDefault(urlParams, 'moreEDO'   , defaultMoreEDO);
  $('#expr').val(urlParams.has('expr') ? urlParams.get('expr') : "");
  updateDropdown($('#primeLimit'), primeLimitOpts(), primeLimit);
  updateDropdown($('#oddLimit')  , oddLimitOpts(sortRat), oddLimit);
  updateDropdown($('#sortRat')   , sortRatOpts(oddLimit), sortRat);
  updateDropdown($('#loEDO')     , loEDOOpts(hiEDO), loEDO);
  updateDropdown($('#hiEDO')     , hiEDOOpts(loEDO), hiEDO);
  updateDropdown($('#sortEDO')   , sortEDOOpts(), sortEDO);
  if (e && e.state && e.state.html && e.state.html.trim() !== "") {
    $('#results').replaceWith(e.state.html);
    $('#primeLimit').change(() => updateRatApproxs('primeLimit'));
    $('#oddLimit')  .change(() => updateRatApproxs('oddLimit'));
    $('#sortRat')   .change(() => updateRatApproxs('sortRat'));
    $('#loEDO')     .change(() => updateEDOApproxs('loEDO'));
    $('#hiEDO')     .change(() => updateEDOApproxs('hiEDO'));
    $('#sortEDO')   .change(() => updateEDOApproxs('sortEDO'));
    res = e.state.res;
    addXenWikiLink(microtonal_utils.Fraction(res.ratio).toFraction());
  }
  else {
    updateResults();
  }
}

// ================================================================
// Initalizing
// ================================================================

$(document).ready(function() {
  setStateFromURL();
  initState();

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
    updateResults();
    let toUpdate = {"expr": $('#expr').val()};
    toUpdate["moreRat"] = ""; toUpdate["moreEDO"] = "";
    updateURLWithParams(toUpdate);
  });

  // results dropdowns (must be re-set on state change)
  $('#primeLimit').change(() => updateRatApproxs('primeLimit'));
  $('#oddLimit')  .change(() => updateRatApproxs('oddLimit'));
  $('#sortRat')   .change(() => updateRatApproxs('sortRat'));
  $('#loEDO')     .change(() => updateEDOApproxs('loEDO'));
  $('#hiEDO')     .change(() => updateEDOApproxs('hiEDO'));
  $('#sortEDO')   .change(() => updateEDOApproxs('sortEDO'));
});
