
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
const primeLimitOpts =
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, "–"];

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
    res.hertz = res.intv.mul(res.ref.hertz).valueOf();
    typeStr = "Interval";
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
    typeStr = "Note";
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
      ret.push(["Interval from reference note:",
                fmtExtExprLink(fmtEDOStep(res.edoStepsToRef))]);
    }
    else {
      ret.push(["Interval from reference note:",
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
    $('#resHeader').html(typeStr + " results");
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
    $('#resAudioHeader').html(typeStr + " audio");
    if (res.type === "interval") {
      $('#intervalAudioButtons').removeClass("hidden");
      $('#noteAudioButtons').addClass("hidden");
      $('#resApproxs').removeClass("hidden");
      updateRatApproxs();
      updateEDOApproxs();
    }
    else {
      $('#intervalAudioButtons').addClass("hidden");
      $('#noteAudioButtons').removeClass("hidden");
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
  if (moreRat < 1 || (toUpdate && toUpdate !== "moreRat")) {
    moreRat = defaultMoreRat;
  }

  const primeLimit = tryParseInt($('#primeLimit').val());
  const oddLimit   = tryParseInt($('#oddLimit')  .val());
  const sortRat    = $('#sortRat').val();
  updateDropdown($('#primeLimit'), primeLimitOpts, primeLimit);
  updateDropdown($('#oddLimit')  , oddLimitOpts(sortRat), oddLimit);
  updateDropdown($('#sortRat')   , sortRatOpts(oddLimit), sortRat);

  const cutoff = res.edoSteps ? 600/res.edoSteps[1] : 50;
  if (sortRat === "difference") {
    $('#cutoffRatSpan').addClass("hidden");
  }
  else {
    $('#cutoffRatSpan').removeClass("hidden");
    $('#cutoffRat').html("±" + fmtCents(cutoff, 1));
  }

  const params = { cutoff: microtonal_utils.Interval(2).pow(cutoff, 1200)
                 , primeLimit: isNaN(primeLimit) ? undefined : primeLimit
                 , oddLimit  : isNaN(oddLimit)   ? undefined : oddLimit
                 , numIterations: moreRat };
  const fn = sortRat === "difference" ? microtonal_utils.bestRationalApproxsByDiff
                                      : microtonal_utils.bestRationalApproxsByHeight;
  const ratApproxsOut = fn(res.intv, params);
  const ratApproxs = sortRat === "difference" ? ratApproxsOut.slice(0,10*moreRat)
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

  if (sortRat === "difference" && ratApproxsOut.length > 10*moreRat) {
    let link = $('<a>').attr("href", "javascript:void(0)")
                       .attr("id", "ratTableMoreLink")
                       .html("show more");
    link.click(function() { moreRat++; updateRatApproxs("moreRat"); });
    $('#ratTableMore').html(link);
  }
  else if (sortRat !== "difference" && !ratApproxsOut[0]) {
    let link = $('<a>').attr("href", "javascript:void(0)")
                       .attr("id", "ratTableMoreLink")
                       .html("search for more"
                             + (moreRat > 1 ? " (x" + moreRat + ")" : ""));
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

// The function to be called if the "Play/pause note" button is clicked
function toggleNote() {
  if ($('#playNoteToggle').html()[0] == "▶") {
    synth.playFreq(1, res.hertz, organ);
    $('#playNoteToggle').html("■ Stop note");
  }
  else {
    stopNoteIfActive();
  }
}
function stopNoteIfActive() {
  if ($('#playNoteToggle').html()[0] != "▶") {
    synth.stopFreqAfter(1, 0);
    $('#playNoteToggle').html("▶ Play note");
  }
}

// Play the melodic interval between res.ref.hertz and res.hertz
function playMelodic() {
  stopNoteIfActive();
  synth.playFreq(0, res.ref.hertz, percussive(1.75));
  synth.stopFreqAfter(0, 2);
  setTimeout(function() {
    synth.playFreq(1, res.hertz, percussive(1.75));
    synth.stopFreqAfter(1, 2);
  }, 700);
}

// Play the harmonic interval between res.ref.hertz and res.hertz
function playHarmonic() {
  stopNoteIfActive();
  synth.playFreq(0, res.ref.hertz, percussive(1.75));
  synth.playFreq(1, res.hertz    , percussive(1.75));
  synth.stopFreqAfter(0, 2);
  synth.stopFreqAfter(1, 2);
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
  const st = { html: $("#results").prop("outerHTML"), res: res };
  if (doReplace) {
    console.log(Date.now() + " [replaced] " + newURL.searchParams);
    console.log(res);
    history.replaceState(st, $("#expr").val(), newURL);
  }
  else {
    console.log(Date.now() + " [pushed] " + newURL.searchParams);
    console.log(res);
    history.pushState(st, $("#expr").val(), newURL);
  }
}

function initState() {
  const url = new URL(window.location);
  // On my machine firefox has weird behavior on refresh, so I always pushState
  // (which still gives weird behavior, but at least it's better)
  updateURLTo(url, !navigator.userAgent.toLowerCase().includes("firefox"));
}

window.onpopstate = function(e) {
  const url = new URL(window.location);
  console.log(Date.now() + " [popped] " + url.searchParams);
  if (e && e.state && e.state.res) { console.log(e.state.res); }
  else if (e) { console.log("bad state!!"); console.log(e); }
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
  const expr       = getWithDefault(urlParams, 'expr'      , "");
  const primeLimit = getWithDefault(urlParams, 'primeLimit', defaultPrimeLimit);
  const oddLimit   = getWithDefault(urlParams, 'oddLimit'  , defaultOddLimit);
  const sortRat    = getWithDefault(urlParams, 'sortRat'   , defaultSortRat);
  const loEDO      = getWithDefault(urlParams, 'loEDO'     , defaultLoEDO);
  const hiEDO      = getWithDefault(urlParams, 'hiEDO'     , defaultHiEDO);
  const sortEDO    = getWithDefault(urlParams, 'sortEDO'   , defaultSortEDO);
  moreRat          = getWithDefault(urlParams, 'moreRat'   , defaultMoreRat);
  moreEDO          = getWithDefault(urlParams, 'moreEDO'   , defaultMoreEDO);
  // update the expr fields and all the dropdowns based on the above
  $('#expr').val(urlParams.has('expr') ? urlParams.get('expr') : "");
  updateDropdown($('#primeLimit'), primeLimitOpts, primeLimit);
  updateDropdown($('#oddLimit')  , oddLimitOpts(sortRat), oddLimit);
  updateDropdown($('#sortRat')   , sortRatOpts(oddLimit), sortRat);
  updateDropdown($('#loEDO')     , loEDOOpts(hiEDO), loEDO);
  updateDropdown($('#hiEDO')     , hiEDOOpts(loEDO), hiEDO);
  updateDropdown($('#sortEDO')   , sortEDOOpts(), sortEDO);
  // either directly set the results section html if we have a valid state, or
  // call updateResults to generate it
  if (e && e.state && e.state.html && e.state.html.trim() !== "") {
    $('#results').replaceWith(e.state.html);
    res = e.state.res;
    addXenWikiLink(microtonal_utils.Fraction(res.ratio).toFraction());
  }
  else {
    updateResults();
  }
  // set (or refresh) the click/change events for all the interactables in the
  // results section
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
}

// ================================================================
// Initalizing
// ================================================================

$(document).ready(function() {
  setStateFromURL();
  initState();

  // reset button
  $('#reset').click(function () {
    setStateFromParams(new URLSearchParams());
    const url = new URL(window.location);
    for (const [param,_] of [...url.searchParams.entries()]) {
      url.searchParams.delete(param);
    }
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
    updateResults();
    let params = {"expr": $('#expr').val()};
    params["moreRat"] = ""; params["moreEDO"] = "";
    updateURLWithParams(params);
  });
});
