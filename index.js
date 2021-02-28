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
  return $('<div>').addClass(["selectContainer", cls]).append(sel).append(icon);
}
function primeLimitDropdown() {
  const opts = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, "--"];
  return dropdown(opts, 13, "primeLimit", "Prime limit", "twoDigitSelect");
}
function oddLimitDropdown() {
  let opts = [];
  for (let o = 3; o <= 99; o += 2) { opts.push(o); }
  opts.push("--");
  return dropdown(opts, 81, "oddLimit", "Odd limit", "twoDigitSelect");
}
function loEDODropdown() {
  let opts = [];
  for (let e = 1; e <= 120; e++) { opts.push(e); }
  return dropdown(opts, 5, "loEDO", "Low EDO", "threeDigitSelect");
}
function hiEDODropdown() {
  let opts = [];
  for (let e = 1; e <= 120; e++) { opts.push(e); }
  return dropdown(opts, 60, "hiEDO", "High EDO", "threeDigitSelect");
}
function sortEDODropdown() {
  return dropdown(["EDO", "cents"], "EDO", "sortEDO", "Sort by EDO or cents", "fiveDigitSelect");
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

function getResults() {
  const res = microtonal_utils.parseCvt($('#expr').val());
  let [typeStr, ret, ratApproxs, edoApproxs] = ["", [], undefined, undefined];
  // Add interval-specific rows
  if (res.type == "interval") {
    typeStr = "Interval results";
    ret.push(["Size in cents:", fmtCents(res.cents, 5)]);
    if (res.ratio) {
      ret.push(["Ratio:", res.ratio.toFraction()]);
    }
    else {
      try {
        if (res.intv.toNthRoot().n <= 6) {
          ret.push(["Expression:", res.intv.toNthRootString()]);
        }
      }
      catch (err) {}
    }
    let fact = [];
    for (const [p,e] of Object.entries(res.intv)) {
      fact.push(p + "^" + (e.d == 1 ? e.s*e.n : "(" + e.toFraction() + ")"));
    }
    if (fact.length > 0) {
      ret.push(["Factorization:", fact.join(" * ")]);
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
      ret.push(["EDO steps:", fmtEDOStep(res.edoSteps)]);
    }
  }
  // Add note-specific rows
  if (res.type == "note") {
    typeStr = "Note results";
    ret.push(["Frequency in hertz:", fmtHertz(res.hertz, 5)]);
    ret.push(["Tuning meter read-out:", res.tuningMeter]);
    const refSymb = microtonal_utils.pyNote(res.ref.intvToA4);
    if (!res.intvToRef.equals(1)) {
      if (res.edoStepsToRef) {
        ret.push(["Interval to reference:",
                  fmtEDOStep(res.edoStepsToRef[0]) + " + " + refSymb]);
      }
      else {
        ret.push(["Interval to reference:",
                  res.intvToRef.toNthRootString() + " * " + refSymb]);
      }
    }
  }
  // Add any symbols
  if (res.symb) {
    if (res.symb["FJS"] &&
        // for now we only have integer accidentals, since I'm not sure how
        //  useful showing non-integer accidentals actually is
        !(res.symb["FJS"].includes("root") || res.symb["FJS"].includes("sqrt"))) {
      ret.push(["FJS name:", res.symb["FJS"]]);
    }
    if (res.symb["NFJS"] &&
        // for now we only have integer accidentals, since I'm not sure how
        //  useful showing non-integer accidentals actually is
        !(res.symb["NFJS"].includes("root") || res.symb["NFJS"].includes("sqrt"))) {
      ret.push(["Neutral FJS name:", res.symb["NFJS"]]);
    }
    if (res.symb["ups-and-downs"]) {
      ret.push(["Ups-and-downs notation:", res.symb["ups-and-downs"].join(", ")]);
    }
  }
  const addS = res.english && res.english.length > 1 ? "(s):" : ":";
  if (res.english && res.english.length > 0){
    const end = res.english.length > 1 ? "(s):" : ":";
    ret.push(["(Possible) English name" + end, res.english.join("<br>")]);
  }
  // Add best rational and EDO approximations
  if (res.type == "interval") {
    const cutoff = res.edoSteps ? microtonal_utils.Interval(2).pow(1,2*res.edoSteps[1])
                                : undefined;
    ratApproxs = microtonal_utils.bestRationalApproxs(res.intv,
                            {cutoff: cutoff, primeLimit: 13, oddLimit: 81});
    ratApproxs.push(res.edoSteps ? 600/res.edoSteps[1] : 50);
    edoApproxs = microtonal_utils.bestEDOApproxsByEDO(res.intv).slice(0,10);
  }
  return [typeStr, ret, ratApproxs, edoApproxs];
}

function updateURL() {
  const url = new URL(window.location);
  url.searchParams.set("expr", $("#expr").val());
  history.pushState($("#results").html(), $("#expr").val(), url);
}

function updateResults() {
  $("#results").empty();
  if ($('#expr').val().trim() == "") { return; }
  try {
    const [typeStr, rows, ratApproxs, edoApproxs] = getResults();
    let resTable = $('<table id="resTable">').addClass("resTable");
    for (const [n,v] of rows) {
      let row = $('<tr>');
      row.append($('<td>').addClass("resLeftColumn").html(n));
      row.append($('<td>').addClass("resRightColumn").html(v));
      resTable.append(row);
    }
    $("#results").append($('<h4>').html(typeStr));
    $('#results').append(resTable);
    if (ratApproxs) {
      $('#results').append($('<h4>').html('Best rational approximations</b>'));
      let approxsDesc = $('<div>').addClass("approxsDesc");
      approxsDesc.append(primeLimitDropdown());
      approxsDesc.append("-limit, ");
      approxsDesc.append(oddLimitDropdown());
      approxsDesc.append("-odd-limit, ");
      approxsDesc.append("cutoff at ±" + fmtCents(ratApproxs[2],1) + ", ")
      approxsDesc.append("sorted by height");
      $('#results').append(approxsDesc);
      let ratTable = $('<table id="ratTable">').addClass("approxsTable");
      for (const {ratio, diff} of ratApproxs[1]) {
        let row = $('<tr>');
        row.append($('<td>').addClass("approxsLeftColumn").html(ratio.toFraction()));
        let diffStr = "exact";
        if (diff != 0) {
          diffStr = (diff > 0 ? "+" : "-") + fmtCents(Math.abs(diff), 3, true);
        }
        row.append($('<td>').addClass("approxsRightColumn").html(diffStr));
        ratTable.append(row);
      }
      $('#results').append(ratTable);
      if (!ratApproxs[0]) { $('#results').append("<i>show more</i>"); }
    }
    if (edoApproxs) {
      $('#results').append($('<h4>').html('Best EDO approximations'));
      let approxsDesc = $('<div>').addClass("approxsDesc");
      approxsDesc.append(loEDODropdown());
      approxsDesc.append("-EDO to ");
      approxsDesc.append(hiEDODropdown());
      approxsDesc.append("-EDO, sorted by ");
      approxsDesc.append(sortEDODropdown());
      $('#results').append(approxsDesc);
      let edoTable = $('<table id="edoTable">').addClass("approxsTable");
      for (let {steps, diff} of edoApproxs) {
        let row = $('<tr>');
        let firstNonZero = steps.findIndex(step => step[0] != 0);
        if (firstNonZero == -1) { firstNonZero = steps.length; }
        let stepStrs = steps.map(fmtEDOStep);
        if (firstNonZero >= 4) {
          stepStrs = stepStrs.slice(0,2).concat(["..."]).concat(stepStrs.slice(firstNonZero-1));
        }
        row.append($('<td>').addClass("approxsLeftColumn").html(stepStrs.join(", ")));
        let diffStr = diff == 0 ? "exact" : (diff < 0 ? "+" : "-") +
                                            fmtCents(Math.abs(diff), 3, true);
        row.append($('<td>').addClass("approxsRightColumn").html(diffStr));
        edoTable.append(row);
      }
      $('#results').append(edoTable);
      $('#results').append("<i>show more</i>")
    }
  }
  catch (err) {
    $("#results").append($('<pre>').addClass("parseError")
                                   .html(err.toString().replace("\n","<br>")));
  }
}

function setStateFromURL(e) {
  const urlParams = new URLSearchParams(window.location.search);
  if (urlParams.has('expr')) { $('#expr').val(urlParams.get('expr')); }
  if (e && e.state) {
    $('#results').html(e.state);
  }
  else {
    updateResults();
  }
}

$(document).ready(function() {
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
    updateURL();
  });

});
