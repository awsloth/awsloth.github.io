function sortFunc(a, b) {

    return b[1][0] - a[1][0] || (a[1][1] + a[1][2] + a[1][3] + a[1][4]) - (b[1][1] + b[1][2] + b[1][3] + b[1][4]) || b[1][1] - a[1][1];
}

function addGames(a, b) {
    return [a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3], a[4] + b[4]];
}

class Standings {
  // detPoints : game -> (abbrev: points, abbrev: points)
  constructor(detPoints, tableID) {
      this.detPoints = detPoints;
      this.standings = {};
      this.tableID = tableID;

      for (let i = 0; i < data.length; i++) {
          var game = detPoints(data[i]);
          if (game[0][0] in this.standings) {
              this.standings[game[0][0]] = addGames(this.standings[game[0][0]], game[0][1]);
          } else {
              this.standings[game[0][0]] = game[0][1];
          }

          if (game[1][0] in this.standings) {
              this.standings[game[1][0]] = addGames(this.standings[game[1][0]], game[1][1]);
          } else {
              this.standings[game[1][0]] = game[1][1];
          }
      }
  }

  showStandings() {
    // sort standings
    const sortedDict = Object.fromEntries(Object.entries(this.standings).sort(sortFunc));

    var table = document.getElementById(this.tableID);

    var row = table.insertRow(0);
    var cell1 = row.insertCell(0);
    var cell2 = row.insertCell(1);

    cell1.innerHTML = "Team"
    cell2.innerHTML = "Points"

    for (var key in sortedDict) {
        var row = table.insertRow(-1);

        var cell1 = row.insertCell(0);
        var cell2 = row.insertCell(1);

        cell1.innerHTML = key;
        cell2.innerHTML = this.standings[key][0];
    }
  }

  updateStandings() {
    // sort standings
    const sortedDict = Object.fromEntries(Object.entries(this.standings).sort(sortFunc));

    var table = document.getElementById(this.tableID);

    let i = 1;
    for (var key in sortedDict) {
        var row = table.rows[i];

        var cell1 = row.cells[0];
        var cell2 = row.cells[1];

        cell1.innerHTML = key;
        cell2.innerHTML = this.standings[key][0];
        i++;
    }
  }
}

import data from "./nhldata.json" with {type: "json"};

function detGame(x, rw, otw, otl, l) {
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
            return [[away_abbrev, [RW, 1, 0, 0, 0]], [home_abbrev, [L, 0, 0, 0, 1]]];
        } else {
            return [[home_abbrev, [RW, 1, 0, 0, 0]], [away_abbrev, [L, 0, 0, 0, 1]]];
        }
    } else {
        if (away_score > home_score) {
            return [[away_abbrev, [OTW, 0, 1, 0, 0]], [home_abbrev, [OTL, 0, 0, 1, 0]]];
        } else {
            return [[home_abbrev, [OTW, 0, 1, 0, 0]], [away_abbrev, [OTL, 0, 0, 1, 0]]];
        }
    }
}

const lbd = new Standings(a => detGame(a, 2, 2, 1, 0), "ranking");
var lbdTwo = new Standings(a => detGame(a, 3, 2, 1, 0), "otherranking");

lbd.showStandings();
lbdTwo.showStandings();

export function runStandings() {
    var w = parseInt(document.getElementById("RW").value);
    var otw = parseInt(document.getElementById("OTW").value);
    var otl = parseInt(document.getElementById("OTL").value);
    var l = parseInt(document.getElementById("L").value);

    var lbdTwo = new Standings(a => detGame(a, w, otw, otl, l), "otherranking");
    lbdTwo.updateStandings();
}

var button = document.getElementById("runstandings");

button.addEventListener('click', function(){runStandings();});

button.onclick = runStandings();
