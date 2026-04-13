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

function addDiff(tableId) {
    var tableL = document.getElementById(tableId.slice(5));
    var tableR = document.getElementById(tableId);

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

    showMultRankings(ranklist) {
        this.table.innerHTML = "";

        for (let i=0; i < ranklist.length; i++) {
            var rankings = ranklist[i];

            var row = this.table.insertRow(-1);
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

    }

    showStandings() {
        const sortedDict = Object.fromEntries(Object.entries(this.standings)
                                 .sort(([,a],[,b]) => sortFunc(a, b, this.gameEval)));

        this.showRankings(sortedDict);

        if (this.table.id[0] == 'o') {
            addDiff(this.table.id);
        }
    }

    showConference(chosenConf) {
        var conf = Object.fromEntries(Object.entries(this.standings).filter((([,a]) => a.conference == chosenConf)));

        const sortedDict = Object.fromEntries(Object.entries(conf)
                                 .sort(([,a],[,b]) => sortFunc(a, b, this.gameEval)));

        this.showRankings(sortedDict);

        if (this.table.id[0] == 'o') {
            addDiff(this.table.id);
        }
    }

    showDivision(chosenDiv) {
        var division = Object.fromEntries(Object.entries(this.standings).filter((([,a]) => a.div == chosenDiv)));

        const sortedDict = Object.fromEntries(Object.entries(division)
                                 .sort(([,a],[,b]) => sortFunc(a, b, this.gameEval)));

        this.showRankings(sortedDict);

        if (this.table.id[0] == 'o') {
            addDiff(this.table.id);
        }
    }

    showWildCard(chosenDivL, chosenDivR) {
        var leftDiv = Object.fromEntries(Object.entries(this.standings).filter((([,a]) => a.div == chosenDivL)));
        var rightDiv = Object.fromEntries(Object.entries(this.standings).filter((([,a]) => a.div == chosenDivR)));

        const sortedLDict = Object.entries(leftDiv)
                                 .sort(([,a],[,b]) => sortFunc(a, b, this.gameEval));

        const sortedRDict = Object.entries(rightDiv)
                                 .sort(([,a],[,b]) => sortFunc(a, b, this.gameEval));

        // top 3 leftdiv
        var top3l = Object.fromEntries(sortedLDict.slice(0, 3));

        // top 3 rightdiv
        var top3r = Object.fromEntries(sortedRDict.slice(0, 3));

        // rest
        var rest = Object.fromEntries(sortedLDict.slice(3).concat(sortedRDict.slice(3)).sort(([,a],[,b]) => sortFunc(a, b, this.gameEval)));

        this.showMultRankings([top3l, top3r, rest]); 

        if (this.table.id[0] == 'o') {
            // Need to work this out
        }
    }

    clear() {
        this.table.innerHTML = "";
    }
}

// Gives a function that determines
// the points for a game
function detGame(rw, otw, otl, rl, top_goals, goal_diff) {
    function gameCheck(game) {
        let points = 0;
        if (top_goals <= game.goals) {
            points++;
        }
        switch (game.outcome) {
            case "RW":
                return rw + points;
            case "OTW":
                return otw + points;
            case "OTL":
                return otl + points;
            case "RL":
                if (-game.goalDiff <= goal_diff) {
                    return rl + points + 1;
                } else {
                    return rl + points;
                }
            default:
                return 0;
        }
    }
    return gameCheck
}

var state = "S";

const lbd = new Standings(detGame(2, 2, 1, 0, 100, -100), "ranking");
const lbd1 = new Standings(detGame(2, 2, 1, 0, 100, -100), "ranking1");
const lbd2 = new Standings(detGame(2, 2, 1, 0, 100, -100), "ranking2");
const lbd3 = new Standings(detGame(2, 2, 1, 0, 100, -100), "ranking3");

var lbdTwo = new Standings(detGame(3, 2, 1, 0, 100, -100), "otherranking");
var lbdTwo1 = new Standings(detGame(3, 2, 1, 0, 100, -100), "otherranking1");
var lbdTwo2 = new Standings(detGame(3, 2, 1, 0, 100, -100), "otherranking2");
var lbdTwo3 = new Standings(detGame(3, 2, 1, 0, 100, -100), "otherranking3");

lbd.showStandings();
lbdTwo.showStandings();
addDiff("otherranking");

var table1Title = document.getElementById("table1");
var table2Title = document.getElementById("table2");
var table3Title = document.getElementById("table3");
var table4Title = document.getElementById("table4");

table1Title.innerHTML = "National Hockey League";

function runFrame(ftype) {
    var w = parseInt(document.getElementById("RW").value);
    var otw = parseInt(document.getElementById("OTW").value);
    var otl = parseInt(document.getElementById("OTL").value);
    var l = parseInt(document.getElementById("L").value);

    var bpc = document.getElementById("BPC").checked;

    if (bpc) {
        var bp = parseInt(document.getElementById("BP").value);
    } else {
        var bp = 100;
    }

    var bptc = document.getElementById("BPTC").checked;

    if (bptc) {
        var bpt = parseInt(document.getElementById("BPT").value);
    } else {
        var bpt = -100;
    }

    var lbdTwo = new Standings(detGame(w, otw, otl, l, bp, bpt), "otherranking");
    var lbdTwo1 = new Standings(detGame(w, otw, otl, l, bp, bpt), "otherranking1");
    var lbdTwo2 = new Standings(detGame(w, otw, otl, l, bp, bpt), "otherranking2");
    var lbdTwo3 = new Standings(detGame(w, otw, otl, l, bp, bpt), "otherranking3");

    state = ftype;

    switch (ftype) {
        case "S":
            table1.innerHTML = "National Hockey League";
            table2.innerHTML = "";
            table3.innerHTML = "";
            table4.innerHTML = "";

            lbd.showStandings();
            lbdTwo.showStandings();

            lbd1.clear();
            lbdTwo1.clear();

            lbd2.clear();
            lbdTwo2.clear();

            lbd3.clear();
            lbdTwo3.clear();
            break;
        case "C":
            table1.innerHTML = "Eastern";

            lbd.showConference("Eastern");
            lbdTwo.showConference("Eastern");

            table2.innerHTML = "Western";

            lbd1.showConference("Western");
            lbdTwo1.showConference("Western");

            table3.innerHTML = "";
            table4.innerHTML = "";

            lbd2.clear();
            lbdTwo2.clear();

            lbd3.clear();
            lbdTwo3.clear();
            break;
        case "D":
            table1.innerHTML = "Atlantic";

            lbd.showDivision("Atlantic");
            lbdTwo.showDivision("Atlantic");

            table2.innerHTML = "Metropolitan";
            
            lbd1.showDivision("Metropolitan");
            lbdTwo1.showDivision("Metropolitan");

            table3.innerHTML = "Central";

            lbd2.showDivision("Central");
            lbdTwo2.showDivision("Central");

            table4.innerHTML = "Pacific";

            lbd3.showDivision("Pacific");
            lbdTwo3.showDivision("Pacific");
            break;
        case "W":
            table1.innerHTML = "Eastern";
            lbd.showWildCard("Metropolitan", "Atlantic");
            lbdTwo.showWildCard("Metropolitan", "Atlantic");

            table2.innerHTML = "Western";
            lbd1.showWildCard("Pacific", "Central");
            lbdTwo1.showWildCard("Pacific", "Central");

            table3.innerHTML = "";
            table4.innerHTML = "";

            lbd2.clear();
            lbdTwo2.clear();

            lbd3.clear();
            lbdTwo3.clear();
            break;
    }
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
