class Standings {
  // detPoints : game -> (abbrev: points, abbrev: points)
  constructor(detPoints, tableID) {
      this.detPoints = detPoints;
      this.standings = {};
      this.tableID = tableID;

      for (let i = 0; i < data.length; i++) {
          var game = detPoints(data[i]);
          if (game[0][0] in this.standings) {
              this.standings[game[0][0]] = this.standings[game[0][0]] + game[0][1];
          } else {
              this.standings[game[0][0]] = game[0][1];
          }

          if (game[1][0] in this.standings) {
              this.standings[game[1][0]] = this.standings[game[1][0]] + game[1][1];
          } else {
              this.standings[game[1][0]] = game[1][1];
          }
      }
  }

  showStandings() {
    // sort standings
    const sortedDict = Object.fromEntries(Object.entries(this.standings).sort(([,a],[,b]) => b - a));

    var table = document.getElementById(this.tableID);

    for (var key in sortedDict) {
        var row = table.insertRow(-1);

        var cell1 = row.insertCell(0);
        var cell2 = row.insertCell(1);

        cell1.innerHTML = key;
        cell2.innerHTML = this.standings[key];
    }
  }

  updateStandings() {
    // sort standings
    const sortedDict = Object.fromEntries(Object.entries(this.standings).sort(([,a],[,b]) => b - a));

    var table = document.getElementById(this.tableID);

    let i = 0;
    for (var key in sortedDict) {
        var row = table.rows[i];

        var cell1 = row.cells[0];
        var cell2 = row.cells[1];

        cell1.innerHTML = key;
        cell2.innerHTML = this.standings[key];
        i++;
    }
  }
}

import data from "./nhldata.json" with {type: "json"};

function detGame(x) {
    const RW = 2;
    const OTW = 2;
    const OTL = 1;
    const L = 0;

    var away = x.awayTeam;
    var home = x.homeTeam;

    var away_abbrev = away.abbrev;
    var home_abbrev = home.abbrev;

    var away_score = away.score;
    var home_score = home.score;

    var wintype = x.gameOutcome.lastPeriodType;

    if (wintype == "REG") {
        if (away_score > home_score) {
            return [[away_abbrev, RW], [home_abbrev, L]];
        } else {
            return [[home_abbrev, RW], [away_abbrev, L]];
        }
    } else {
        if (away_score > home_score) {
            return [[away_abbrev, OTW], [home_abbrev, OTL]];
        } else {
            return [[home_abbrev, OTW], [away_abbrev, OTL]];
        }
    }
}

function detOtherGame(x, rw, otw, otl, l) {
    const RW = rw;
    const OTW = otw;
    const OTL = otl;
    const L = l;

    var away = x.awayTeam;
    var home = x.homeTeam;

    var away_abbrev = away.abbrev;
    var home_abbrev = home.abbrev;

    var away_score = away.score;
    var home_score = home.score;

    var wintype = x.gameOutcome.lastPeriodType;

    if (wintype == "REG") {
        if (away_score > home_score) {
            return [[away_abbrev, RW], [home_abbrev, L]];
        } else {
            return [[home_abbrev, RW], [away_abbrev, L]];
        }
    } else {
        if (away_score > home_score) {
            return [[away_abbrev, OTW], [home_abbrev, OTL]];
        } else {
            return [[home_abbrev, OTW], [away_abbrev, OTL]];
        }
    }
}

const lbd = new Standings(detGame, "ranking");
var lbdTwo = new Standings(a => detOtherGame(a, 3, 2, 1, 0), "otherranking");

lbd.showStandings();
lbdTwo.showStandings();

export function runStandings() {
    var w = parseInt(document.getElementById("RW").value);
    var otw = parseInt(document.getElementById("OTW").value);
    var otl = parseInt(document.getElementById("OTL").value);
    var l = parseInt(document.getElementById("L").value);

    var lbdTwo = new Standings(a => detOtherGame(a, w, otw, otl, l), "otherranking");
    lbdTwo.updateStandings();

    console.log(document.getElementById("RW").value);
}

var button = document.getElementById("runstandings");

button.addEventListener('click', function(){runStandings();});

button.onclick = runStandings();
