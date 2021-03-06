function tryParseInt(x) {
  return isNaN(x) ? x : parseInt(x);
}

function xenWikiPageExists(title) {
  const xenAPI = "https://en.xen.wiki/api.php?origin=*";
  const params = "&action=query&format=json&prop=&list=search&srsearch=";
  const url = xenAPI + params + title;
  try {
    return fetch(url).then(function(res) { return res.json(); })
                     .then(function(res) { return !!res.query.searchinfo.totalhits; })
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

// Makes a nicely-formatted dropdown menu
function dropdown(opts, selected, id, title, cls) {
  let sel = $('<select>').attr("id", id).attr("title", title);
  for (const str of opts) {
    let opt = $('<option>').attr('value', str).text(str);
    if (str == selected) { opt.attr("selected", true); }
    sel.append(opt);
  }
  const icon = $('<div>').addClass("selectIcon").text("▽");
  return $('<div>').attr("id", id + "Container")
                   .addClass(["selectContainer", cls])
                   .append(sel).append(icon);
}

var primeLimit;
var oddLimit  ;
var loEDO     ;
var hiEDO     ;
var sortRat   ;
var sortEDO   ;

function primeLimitDropdown() {
  const opts = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, "–"];
  return dropdown(opts, primeLimit, "primeLimit", "Prime limit", "twoDigitSelect");
}
function oddLimitDropdown() {
  let opts = [];
  for (let o = 3; o <= 99; o += 2) { opts.push(o); }
  opts.push("–");
  return dropdown(opts, oddLimit, "oddLimit", "Odd limit", "twoDigitSelect");
}
function loEDODropdown() {
  let opts = [];
  for (let e = 1; e < hiEDO; e++) { opts.push(e); }
  return dropdown(opts, loEDO, "loEDO", "Lowest EDO", "threeDigitSelect");
}
function hiEDODropdown() {
  let opts = [];
  for (let e = loEDO+1; e <= 120; e++) { opts.push(e); }
  return dropdown(opts, hiEDO, "hiEDO", "Highest EDO", "threeDigitSelect");
}
function sortRatDropdown() {
  return dropdown( ["height", "denominator", "difference"], sortRat, "sortRat"
                 , "Sort best rational approximations", "sortRatSelect");
}
function sortEDODropdown() {
  return dropdown( ["EDO", "difference"], sortEDO, "sortEDO"
                 , "Sort best EDO approximations", "sortEDOSelect");
}

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

var res = {};

function getResults() {
  res = microtonal_utils.parseCvt($('#expr').val());
  let [typeStr, ret] = ["", []];
  // Add interval-specific rows
  if (res.type == "interval") {
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
    if (res.edoSteps) {
      ret.push(["EDO steps:", fmtExtExprLink(fmtEDOStep(res.edoSteps))]);
    }
  }
  // Add note-specific rows
  if (res.type == "note") {
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
  if (res.type == "note" && !res.intvToRef.equals(1)) {
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

function updateURLWithParam(param, val) {
  const url = new URL(window.location);
  if (val != undefined && (!val.trim || val.trim() !== "")) {
    url.searchParams.set(param, val);
  }
  else {
    url.searchParams.delete(param);
  }
  history.pushState($("#results").html(), $("#expr").val(), url);
}

function updateResults() {
  $("#results").empty();
  if ($('#expr').val().trim() == "") { return; }
  try {
    const [typeStr, rows] = getResults();
    let resTable = $('<table id="resTable">').addClass("resTable");
    for (const [n,v] of rows) {
      let row = $('<tr>');
      row.append($('<td>').addClass("resLeftColumn").html(n));
      row.append($('<td>').addClass("resRightColumn").html(v));
      resTable.append(row);
    }
    $("#results").append($('<h4>').html(typeStr));
    $('#results').append(resTable);
    // add xen wiki link
    if (res.ratio) {
      const xenPageName = res.ratio.toFraction();
      const xenURL = "https://en.xen.wiki/w/" + xenPageName;
      const pageExists = xenWikiPageExists(xenPageName);
      if (pageExists) {
        pageExists.then(function(exists) {
          if (exists) {
            let link = $('<a>').attr("href", xenURL)
                               .append(xenURL);
            // $('#resRatio').html(link);
            let row = $('<tr>');
            row.append($('<td>').addClass("resLeftColumn").html("Xenharmonic wiki page:"));
            row.append($('<td>').addClass("resRightColumn").html(link));
            $('#resTable').append(row);
          }
        });
      }
    }
    if (res.type == "interval") {
      // add best rational approximations
      $('#results').append($('<h4>').html('Best rational approximations</b>'));
      let ratApproxsDesc = $('<div>').addClass("approxsDesc");
      ratApproxsDesc.append(primeLimitDropdown());
      ratApproxsDesc.append("-limit, ");
      ratApproxsDesc.append(oddLimitDropdown());
      ratApproxsDesc.append("-odd-limit, ");
      const cutoff = res.edoSteps ? 600/res.edoSteps[1] : 50;
      ratApproxsDesc.append("cutoff at ±" + fmtCents(cutoff,1) + ", sorted by ");
      ratApproxsDesc.append(sortRatDropdown());
      $('#results').append(ratApproxsDesc);
      $('#results').append($('<div id="ratTableDiv">'));
      $('#primeLimit').on("change", updateRatApproxs);
      $('#oddLimit')  .on("change", updateRatApproxs);
      $('#sortRat')   .on("change", updateRatApproxs);
      updateRatApproxs();
      // add best EDO approximations
      $('#results').append($('<h4>').html('Best EDO approximations'));
      let edoApproxsDesc = $('<div>').addClass("approxsDesc");
      edoApproxsDesc.append(loEDODropdown());
      edoApproxsDesc.append("-EDO to ");
      edoApproxsDesc.append(hiEDODropdown());
      edoApproxsDesc.append("-EDO, cutoff at ±50c, sorted by ");
      edoApproxsDesc.append(sortEDODropdown());
      $('#results').append(edoApproxsDesc);
      $('#results').append($('<div id="edoTableDiv">'));
      $('#loEDO')  .on("change", updateEDOApproxs);
      $('#hiEDO')  .on("change", updateEDOApproxs);
      $('#sortEDO').on("change", updateEDOApproxs);
      updateEDOApproxs();
    }
  }
  catch (err) {
    $("#results").append($('<pre>').addClass("parseError")
                                   .html(err.toString().replace("\n","<br>")));
  }
}

function updateRatApproxs() {
  const [oldPrimeLimit, oldOddLimit, oldSortRat] = [primeLimit, oddLimit, sortRat];
  primeLimit = tryParseInt($('#primeLimit').val());
  oddLimit   = tryParseInt($('#oddLimit')  .val());
  sortRat = $('#sortRat').val();
  $('#ratTableDiv').empty();
  const cutoff = res.edoSteps ? microtonal_utils.Interval(2).pow(1,2*res.edoSteps[1])
                              : undefined;
  const params = { cutoff: cutoff
                 , primeLimit: isNaN(primeLimit) ? undefined : primeLimit
                 , oddLimit  : isNaN(oddLimit)   ? undefined : oddLimit };
  const ratApproxs = microtonal_utils.bestRationalApproxs(res.intv, params);
  let ratTable = $('<table id="ratTable">').addClass("approxsTable");
  for (const {ratio, diff} of ratApproxs[1]) {
    let row = $('<tr>');
    const lhs = fmtExtExprLink(ratio.toFraction(), true);
    row.append($('<td>').addClass("approxsLeftColumn").html(lhs));
    let diffStr = "exact";
    if (diff != 0) {
      diffStr = (diff > 0 ? "+" : "-") + fmtCents(Math.abs(diff), 3, true);
    }
    row.append($('<td>').addClass("approxsRightColumn").html(diffStr));
    ratTable.append(row);
  }
  $('#ratTableDiv').append(ratTable);
  if (!ratApproxs[0]) {
    $('#ratTableDiv').append("<i>search for more</i>");
  }
  else if (ratApproxs[1].length == 0) {
    $('#ratTableDiv').append("<i>no results</i>");
  }
  if (primeLimit != oldPrimeLimit) { updateURLWithParam("primeLimit", primeLimit || "–"); }
  if (oddLimit   != oldOddLimit  ) { updateURLWithParam("oddLimit"  , oddLimit   || "–"); }
  if (sortRat    != oldSortRat   ) { updateURLWithParam("sortRat"   , sortRat   ); }
}

function updateEDOApproxs() {
  const [oldLoEDO, oldHiEDO, oldSortEDO] = [loEDO, hiEDO, sortEDO];
  loEDO   = parseInt($('#loEDO').val());
  hiEDO   = parseInt($('#hiEDO').val());
  sortEDO = $('#sortEDO').val();
  $('#edoTableDiv').empty();
  const params = { startEDO: loEDO, endEDO: hiEDO };
  const fn = sortEDO == "difference" ? microtonal_utils.bestEDOApproxsByDiff
                                     : microtonal_utils.bestEDOApproxsByEDO;
  const edoApproxs = fn(res.intv, params);
  let edoTable = $('<table id="edoTable">').addClass("approxsTable");
  for (let {steps, diff} of edoApproxs.slice(0,10)) {
    let row = $('<tr>');
    let firstNonZero = steps.findIndex(step => step[0] != 0);
    if (firstNonZero == -1) { firstNonZero = steps.length; }
    let stepStrs = steps.map(fmtEDOStep);
    if (firstNonZero >= 4) {
      stepStrs = stepStrs.slice(0,2).concat(["..."]).concat(stepStrs.slice(firstNonZero-1));
    }
    const lhs = fmtExtExprLink(stepStrs.join(", "), true);
    row.append($('<td>').addClass("approxsLeftColumn").html(lhs));
    let diffStr = diff == 0 ? "exact" : (diff < 0 ? "+" : "-") +
                                        fmtCents(Math.abs(diff), 3, true);
    row.append($('<td>').addClass("approxsRightColumn").html(diffStr));
    edoTable.append(row);
  }
  $('#edoTableDiv').append(edoTable);
  if (edoApproxs.length > 10) {
    $('#edoTableDiv').append("<i>show more</i>");
  }
  if (loEDO != oldLoEDO) {
    updateURLWithParam("loEDO", loEDO);
    $('#hiEDO').empty();
    let opts = [];
    for (let e = loEDO+1; e <= 120; e++) { opts.push(e); }
    for (const str of opts) {
      let opt = $('<option>').attr('value', str).text(str);
      if (str == hiEDO) { opt.attr("selected", true); }
      $('#hiEDO').append(opt);
    }
  }
  if (hiEDO != oldHiEDO) {
    updateURLWithParam("hiEDO", hiEDO);
    $('#loEDO').empty();
    let opts = [];
    for (let e = 1; e < hiEDO; e++) { opts.push(e); }
    for (const str of opts) {
      let opt = $('<option>').attr('value', str).text(str);
      if (str == loEDO) { opt.attr("selected", true); }
      $('#loEDO').append(opt);
    }
  }
  if (sortEDO != oldSortEDO) { updateURLWithParam("sortEDO", sortEDO); }
}

function setStateFromURL(e) {
  const urlParams = new URLSearchParams(window.location.search);
  $('#expr').val(urlParams.has('expr') ? urlParams.get('expr') : "");
  primeLimit = urlParams.has('primeLimit') ? urlParams.get('primeLimit') : 13;
  oddLimit   = urlParams.has('oddLimit')   ? urlParams.get('oddLimit')   : 81;
  sortRat    = urlParams.has('sortRat')    ? urlParams.get('sortRat')    : "height";
  loEDO      = urlParams.has('loEDO')      ? urlParams.get('loEDO')      : 5;
  hiEDO      = urlParams.has('hiEDO')      ? urlParams.get('hiEDO')      : 60;
  sortEDO    = urlParams.has('sortEDO')    ? urlParams.get('sortEDO')    : "EDO";
  if (e && e.state) {
    $('#results').html(e.state);
    $('#primeLimit').on("change", updateRatApproxs);
    $('#oddLimit')  .on("change", updateRatApproxs);
    $('#sortRat')   .on("change", updateRatApproxs);
    $('#loEDO')     .on("change", updateEDOApproxs);
    $('#hiEDO')     .on("change", updateEDOApproxs);
    $('#sortEDO')   .on("change", updateEDOApproxs);
  }
  else {
    updateResults();
  }
}

$(document).ready(function() {
  history.replaceState($("#results").html(), "", new URL(window.location));
  setStateFromURL();
  window.onpopstate = setStateFromURL;

  // add accidental buttons
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
    updateURLWithParam("expr", $('#expr').val());
  });

});
