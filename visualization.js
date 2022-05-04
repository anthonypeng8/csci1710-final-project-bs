// BS model visualization
const d3 = require('d3')
d3.selectAll("svg > *").remove();

function printCard(xoffset, yoffset, rank, suit) {
    d3.select(svg)
    .append('rect')
    .attr('x', xoffset)
    .attr('y', yoffset)
    .attr('width', 25)
    .attr('height', 50)
    .attr('stroke-width', 2)
    .attr('stroke', 'black')
    .attr('fill', 'transparent')
    .text(rank);

    // Print rectangle
    // Number
    // Suit (either simply add text of suit, or more complicated add an image for suit)
        // h: heart
        // s: spades
        // c: club
        // d: diamond
}

function printPile(x_loc, y_loc) {
    // printcard() based on how many n cards in deck
    for (n = 0; n <= 5; n++) {
        printCard(n, yoffset, )
    }
}

function printPlayer(row, col, yoffset, value) {
    // hand of cards
    printPile()

    // set of cards said played
    printPile()    

    // bs/fold indicator?
}

function printState(stateAtom, yoffset) {
    // Print out the 2 players
        // hand of cards
        // set of cards said played
        // bs/fold indicator?
    for (n = 0; n <= 2; n++) {
        printPlayer()
    }

    // Current pile
    printPile(x_loc, y_loc)
    // Current pile value
    d3.select(svg)
        .append("text")
        .attr("x", x_loc)
        .attr("y", y_loc + 50)
        .text(value);
}

// This is for the states, in this case b = 10 or 11 states
var offset = 0
for(b = 0; b <= 10; b++) {  
    if(State.atom("State"+b) != null)
        printState(State.atom("State"+b), offset)  
    offset = offset + 55
}


// TicTacToe
const d3 = require('d3')
d3.selectAll("svg > *").remove();

function printValue(row, col, yoffset, value) {
  d3.select(svg)
    .append("text")
    .style("fill", "black")
    .attr("x", (row+1)*10)
    .attr("y", (col+1)*14 + yoffset)
    .text(value);
}

function printState(stateAtom, yoffset) {
  for (r = 0; r <= 2; r++) {
    for (c = 0; c <= 2; c++) {
      printValue(r, c, yoffset,
                 stateAtom.board[r][c]
                 .toString().substring(0,1))  
    }
  }
  
  d3.select(svg)
    .append('rect')
    .attr('x', 5)
    .attr('y', yoffset+1)
    .attr('width', 40)
    .attr('height', 50)
    .attr('stroke-width', 2)
    .attr('stroke', 'black')
    .attr('fill', 'transparent');
}


var offset = 0
for(b = 0; b <= 10; b++) {  
  if(State.atom("State"+b) != null)
    printState(State.atom("State"+b), offset)  
  offset = offset + 55
}


// Connect4
const d3 = require('d3')
d3.selectAll("svg > *").remove();

function printValue(row, col, xoffset, yoffset, value) {
  
  var color = "red"
  if (value == "B")
    color = "blue"
  d3.select(svg)
    .append("text")
    .style("fill", color)
    .attr("x", (col+1)*10 + xoffset)
    .attr("y", (row+1.2)*14 + yoffset)
    .text(value);
}

function printState(stateAtom, xoffset, yoffset) {
  for (r = 0; r <= 5; r++) {
    for (c = 0; c <= 6; c++) {
      printValue(r, c, xoffset, yoffset,
                 stateAtom.board[r][c]
                 .toString().substring(0,1))  
    }
  }
  
  d3.select(svg)
    .append('rect')
    .attr('x', xoffset+5)
    .attr('y', yoffset+1)
    .attr('width', 80)
    .attr('height', 90)
    .attr('stroke-width', 2)
    .attr('stroke', 'black')
    .attr('fill', 'transparent');
}

var col = 0
var offset = 0
for(b = 0; b <= 42; b++) {
  if(State.atom("State"+b) != null)
    printState(State.atom("State"+b), col*85 ,offset)
  if (col == 4) {
    col = 0
    offset = offset + 95
  } else {col = col + 1}  
}



