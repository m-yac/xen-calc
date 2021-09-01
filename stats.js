
var sessionCounters = {};

// Increment the count for each of the given strings
function logStrs(ids) {
  // always log things locally
  ids.forEach(s => sessionCounters[s] = 1 + (sessionCounters[s] || 0));
  // don't log anything remotely if we're not connected via yacavone.net
  if (window.location.href.indexOf("https://www.yacavone.net") != 0) {
    console.log("[Offline] Incremented counters: \"" + ids.join("\", \"") + "\"");
    return;
  }
  setTimeout(function () {
    try {
      const xhr = new XMLHttpRequest();
      xhr.open("POST", "https://hc7onb7dbi.execute-api.us-east-2.amazonaws.com/logPageUse_yacavone_dot_net", true);
      xhr.setRequestHeader('Content-Type', 'text/plain');
      xhr.send(JSON.stringify({ page: "xen-calc", ids: ids }));
      console.log("[AWS] Incremented counters: \"" + ids.join("\", \"") + "\"");
    } catch (err) {
      console.error(err);
    }
  });
}

const logQueryStrMap = [
  ["color", "clr"],
  ["color (verbose)", "clr vb"],
  ["Pythagorean", "py"],
  ["neutral Pythagorean", "neut py"],
  ["semi-neutral Pythagorean", "semi-neut py"],
  ["multiplicative", "mult"],
  ["additive", "addv"],
  ["symbol", "symb"],
];

const queryTypeUnambigType = [
  "ratio", "monzo", "cents", "EDO step", "EDO TT", "hertz", "TT", "phi"
]

const logResStrMap = [
  ["square root", "sqrt"],
  ["isoharmonic interval", "iso"]
];

// Increment the count for strings related to the current result
function logResultTypes(res, xs) {
  if (res.type == undefined) { return; }
  const typec = res.type == "interval" ? "i" : "n";
  let toLog = xs ? xs : [];
  // log the query type
  if (res.symbolType != undefined && res.symbolType !== "") {
    let abbr_symbolType = res.symbolType;
    for (const [s1,s2] of logQueryStrMap) {
      if (res.symbolType == s1) { abbr_symbolType = s2; break; }
    }
    toLog.push("q " + typec + " " + abbr_symbolType);
  }
  else {
    let abbr_queryType = res.queryType;
    for (const [s1,s2] of logQueryStrMap) {
      if (res.queryType == s1) { abbr_queryType = s2; break; }
    }
    toLog.push("q " + typec + " " + abbr_queryType);
  }
  // log the result type
  if (res.type == "note") {
    toLog.push("r note");
  }
  else if (res.ratio) {
    toLog.push("r ratio");
  }
  else if (res.edoSteps) {
    toLog.push("r EDO step");
  }
  else if (res.intv && res.intv.pow(2).isFrac()) {
    toLog.push("r sqrt");
  }
  else if (res.iso) {
    toLog.push("r iso");
  }
  // log the overall type (interval or note)
  toLog.push("t " + res.type);
  // log to the overall total
  toLog.push("total");
  logStrs(toLog);
}

// Query the count of different strings
function logQuery(date, ids, callback) {
  setTimeout(function () {
    try {
      const xhr = new XMLHttpRequest();
      xhr.addEventListener('load', function () {
        const res = xhr.responseText;
        console.log("[AWS] For " + date + ", queried counters: " + res);
        if (callback != undefined) { callback(JSON.parse(res)); }
      });
      xhr.open("POST", "https://hc7onb7dbi.execute-api.us-east-2.amazonaws.com/queryPageUse_yacavone_dot_net", true);
      xhr.setRequestHeader('Content-Type', 'text/plain');
      let params = { page: "xen-calc" };
      if (date != undefined) { params.date = date };
      if (ids != undefined) { params.ids = ids; }
      xhr.send(JSON.stringify(params));
    }
    catch (err) {
      console.error(err);
    }
  });
}
