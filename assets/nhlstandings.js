import data from "./nhldata.json" with {type: "json"};
import teamdata from "./nhlteams.json" with {type: "json"};

class Game {
    constructor(team, homeOrAway, homeScore, awayScore, gameType) {
        this.team = team;
        this.homeOrAway = homeOrAway;
        this.homeScore = homeScore;
        this.awayScore = awayScore;
        this.gameType = gameType;

        if (this.homeOrAway == "H") {
            this.goals = homeScore;
            this.goalDiff = homeScore - awayScore;
        } else {
            this.goals = awayScore;
            this.goalDiff = awayScore - homeScore;
        }

        if (this.goalDiff > 0) {
            if (gameType == "REG") {
                this.outcome = "RW";
            } else {
                this.outcome = "OTW";
            }
        } else {
            if (gameType == "REG") {
                this.outcome = "RL";
            } else {
                this.outcome = "OTL";
            }
        }
    }
}

class Team {
    constructor(name, abbrev, image) {
        this.name = name;
        this.abbrev = abbrev;
        this.image = image;

        for (let i = 0; i < teamdata.length; i++) {
            var team = teamdata[i];
            if (team.abbr == abbrev) {
                this.div = team.division.name;
                this.conference = team.conference.name;
                break;
            }
        }

        this.games = [];
    }

    addGame(game) {
        this.games.push(game);
    }

    evalPoints(gameEval) {
        return this.games.reduce((x, a) => x + gameEval(a), 0);
    }

    gamesPlayed() {
        return this.games.length;
    }

    regulationWins() {
        function isRW(a) {
            if (a.outcome == "RW") {
                return 1;
            } else {
                return 0;
            }
        }
        return this.games.map(isRW).reduce((x, a) => x + a, 0);
    }
}

// Given two teams (and function to evaluate games)
// an integer to choose which goes first
function sortFunc(a, b, gameEval) {
    // Sort on points, then games, then regulation wins
    return b.evalPoints(gameEval) - a.evalPoints(gameEval)
        || a.gamesPlayed()        - b.gamesPlayed()
        || b.regulationWins()     - a.regulationWins();
}

class Standings {
    constructor(gameEval, tableID) {

        this.gameEval = gameEval;
        this.table = document.getElementById(tableID);
        this.standings = {}

        for (let i=0; i < data.length; i++) {
            var game = data[i];
            var home_team  = game.homeTeam;
            var away_team  = game.awayTeam;
            var home_score = home_team.score;
            var away_score = away_team.score;
            var game_type  = game.gameOutcome.lastPeriodType;

            var home_team_name = home_team.abbrev;
            var away_team_name = away_team.abbrev;

            var home_game = new Game(home_team_name, "H", home_score, away_score, game_type);
            var away_game = new Game(away_team_name, "A", home_score, away_score, game_type);

            if (!(home_team_name in this.standings)) {
                this.standings[home_team_name] = new Team(home_team.placeName.default + "  " + home_team.commonName.default, home_team_name, home_team.logo);
            }

            this.standings[home_team_name].addGame(home_game);

            if (!(away_team_name in this.standings)) {
                this.standings[away_team_name] =
                    new Team(away_team.placeName.default + "  " + away_team.commonName.default, away_team_name, away_team.logo);
            }

            this.standings[away_team_name].addGame(away_game);
        }
    }

    showRankings(rankings) {
        this.table.innerHTML = "";
        var row = this.table.insertRow(0);
        var cell1 = row.insertCell(0);
        var cell2 = row.insertCell(1);
        var cell3 = row.insertCell(2);

        cell1.innerHTML = "Team";
        cell2.innerHTML = "Points";
        cell3.innerHTML = "RWs";



        for (var key in rankings) {
            var row = this.table.insertRow(-1);


            var cell1 = row.insertCell(0);
            var cell2 = row.insertCell(1);
            var cell3 = row.insertCell(2);

            var team = rankings[key];
            cell1.innerHTML = "<img style='height:30px;' src=" + team.image + "> " + team.name;
            cell2.innerHTML = team.evalPoints(this.gameEval);
            cell3.innerHTML = team.regulationWins();
        }
    }

    showStandings() {
        const sortedDict = Object.fromEntries(Object.entries(this.standings)
                                 .sort(([,a],[,b]) => sortFunc(a, b, this.gameEval)));

        this.showRankings(sortedDict);
    }

    showConferences() {
        var east = Object.fromEntries(Object.entries(this.standings).filter((([,a]) => a.conference == "Eastern")));

        const sortedDict = Object.fromEntries(Object.entries(east)
                                 .sort(([,a],[,b]) => sortFunc(a, b, this.gameEval)));

        this.showRankings(sortedDict);
    }

    showDivisions() {
        var metro = Object.fromEntries(Object.entries(this.standings).filter((([,a]) => a.div == "Metropolitan")));

        const sortedDict = Object.fromEntries(Object.entries(metro)
                                 .sort(([,a],[,b]) => sortFunc(a, b, this.gameEval)));

        this.showRankings(sortedDict);

    }

    showWildCard() {
        var east = Object.fromEntries(Object.entries(this.standings).filter((([,a]) => a.conference == "Eastern")));

        const sortedDict = Object.fromEntries(Object.entries(east)
                                 .sort(([,a],[,b]) => sortFunc(a, b, this.gameEval)));

        this.showRankings(sortedDict);
    }
}

/*

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
    var cell3 = row.insertCell(2);

    cell1.innerHTML = "POS"
    cell3.innerHTML = "PTS"

    let i = 0;
    for (var key in sortedDict) {
        var row = table.insertRow(-1);

        var cell1 = row.insertCell(0);
        var cell2 = row.insertCell(1);
        var cell3 = row.insertCell(2);

        var diff = findDiff(key, i);

        if (diff < 0) {
            cell1.innerHTML = -diff;
            cell1.style.color = "red";
        } else if (diff > 0) {
            cell1.innerHTML = diff;
            cell1.style.color = "green";
        } else {
            cell1.innerHTML = "-";
        }

        cell2.innerHTML = key;
        cell3.innerHTML = this.standings[key][0];
        i ++;
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
        var cell3 = row.cells[2];
        
        cell2.innerHTML = key;
        cell3.innerHTML = this.standings[key][0];
        i++;
    }
  }
}
*/

// Gives a function that determines
// the points for a game
function detGame(rw, otw, otl, rl, top_goals, goal_diff) {
    function gameCheck(game) {
        let points = 0;
        if (top_goals <= game.goals) {
            points++;
        }
        if (goal_diff <= game.goal_diff) {
            points ++;
        }
        switch (game.outcome) {
            case "RW":
                return rw + points;
            case "OTW":
                return otw + points;
            case "OTL":
                return otl + points;
            case "RL":
                return rl + points;
            default:
                return 0;
        }
    }
    return gameCheck
}

var state = "S";

const lbd = new Standings(detGame(2, 2, 1, 0, 100, 100), "ranking");
var lbdTwo = new Standings(detGame(3, 2, 1, 0, 100, 100), "otherranking");

lbd.showStandings();
lbdTwo.showStandings();
addDiff(state);

function addDiff(state) {
    if (state == "W") {
        return 1;
    }

    var tableL = document.getElementById("ranking");
    var tableR = document.getElementById("otherranking");

    for (let i = 0; i < tableR.rows.length; i++) {
        var cell1 = tableR.rows[i].insertCell(0);

        if (i > 0) {
        for (let j = 0; j < tableL.rows.length; j++) {
            if (tableL.rows[j].cells[0].innerHTML == tableR.rows[i].cells[1].innerHTML) {
                var diff = j - i;

                if (diff < 0) {
                    cell1.innerHTML = "↓" + (-diff).toString();
                    cell1.style.color = "red";
                } else if (diff > 0) {
                    cell1.innerHTML = "↑" + diff.toString();
                    cell1.style.color = "green";
                } else {
                    cell1.innerHTML = "-";
                }
                break;
            }
        }
        }
    }
}

function runFrame(ftype) {
    var w = parseInt(document.getElementById("RW").value);
    var otw = parseInt(document.getElementById("OTW").value);
    var otl = parseInt(document.getElementById("OTL").value);
    var l = parseInt(document.getElementById("L").value);

    var lbdTwo = new Standings(detGame(w, otw, otl, l, 100, 100), "otherranking");

    state = ftype;

    switch (ftype) {
        case "S":
            lbd.showStandings();
            lbdTwo.showStandings();
            break;
        case "C":
            lbd.showConferences();
            lbdTwo.showConferences();
            break;
        case "D":
            lbd.showDivisions();
            lbdTwo.showDivisions();
            break;
        case "W":
            lbd.showWildCard();
            lbdTwo.showWildCard();
            break;
    }

    addDiff(state);
}



// Button mappings
var run_button = document.getElementById("runstandings");
run_button.addEventListener('click', function(){runFrame(state);});

var stand_button = document.getElementById("standings");
var conf_button = document.getElementById("conference");
var div_button = document.getElementById("division");
var wild_button = document.getElementById("wildcard");

stand_button.addEventListener('click', function(){runFrame("S");});
conf_button.addEventListener('click', function(){runFrame("C");});
div_button.addEventListener('click', function(){runFrame("D");});
wild_button.addEventListener('click', function(){runFrame("W");});
