const d3 = require('d3')
d3.selectAll("svg > *").remove();

function printCard(card, xoffset, yoffset) {    
    d3.select(svg)
    .append('rect')
    .attr('x', xoffset)
    .attr('y', yoffset + 5)
    .attr('width', 25)
    .attr('height', 50)
    .attr('stroke-width', 2)
    .attr('stroke', 'black')
    .attr('fill', 'transparent')
    .text(card.value);

    var c = Card.atom(card._atoms[0]._id)
    d3.select(svg)
        .append("text")
        .attr("x", xoffset + 10)
        .attr("y", yoffset + 25)
        .text(c.value.toString());

    d3.select(svg)
        .append("text")
        .style("font", "14px times")
        .attr("x", xoffset + 10)
        .attr("y", yoffset + 45)
        .text(c.suit.toString()[0]);

    // Print rectangle
    // Number
    // Suit (either simply add text of suit, or more complicated add an image for suit)
        // h: heart
        // s: spades
        // c: club
        // d: diamond
}

function printPile(stateAtom, player, xoffset, yoffset) {
    // printcard() based on how many n cards in deck
    
    // for (n = 0; n <= 5; n++) {
    //     // printCard(n, yoffset, )
    //     if(State.atom("State"+b) != null)
    //       printState(State.atom("State"+b), offset)  
    // }


    // for (const card of player.hand[stateAtom]) {
    //   printCard(card, curr_xoffset, yoffset);
    //   curr_xoffset = curr_xoffset + 5
    // }

    //console.log(player.hand[stateAtom]._tuples)

    var curr_xoffset = xoffset
    player.hand[stateAtom]._tuples.forEach(card => {
      printCard(card, curr_xoffset, yoffset);
      curr_xoffset = curr_xoffset + 30
    });
}

function printPlayer(stateAtom, player, yoffset) {
    // hand of cards
    d3.select(svg)
      .append("text")
      .attr("x", 10)
      .attr("y", yoffset + 25)
      .text("Player " + player.toString()[1]);
    printPile(stateAtom, player, 10, yoffset + 25)

    // set of cards said played
    // printPile()    

    // bs/fold indicator?
}

function printState(stateAtom, yoffset) {
    // Print out the 2 players
        // hand of cards
        // set of cards said played
        // bs/fold indicator?
    printPlayer(stateAtom, P1.atom("P10"), yoffset + 15)
    printPlayer(stateAtom, P2.atom("P20"), yoffset + 90)

    // Current pile
    d3.select(svg)
      .append("text")
      .attr("x", 10)
      .attr("y", yoffset + 190)
      .text("Pile");
    var curr_xoffset = 10
    Pile.atom("Pile0").hand[stateAtom]._tuples.forEach(card => {
      printCard(card, curr_xoffset, yoffset + 190);
      curr_xoffset = curr_xoffset + 30
    });
    // printPile(20, yoffset)

    // Current pile value
    d3.select(svg)
        .append("text")
        .attr("x", 10)
        .attr("y", yoffset + 20)
        .text("Current Rank: " + stateAtom.currValue.toString());
}

// This is for the states, in this case b = 10 or 11 states
var offset = 0
for(b = 0; b <= 10; b++) {  
    if(State.atom("State"+b) != null)
        printState(State.atom("State"+b), offset)  
    offset = offset + 250
}


// // TicTacToe
// const d3 = require('d3')
// d3.selectAll("svg > *").remove();

// function printValue(row, col, yoffset, value) {
//   d3.select(svg)
//     .append("text")
//     .style("fill", "black")
//     .attr("x", (row+1)*10)
//     .attr("y", (col+1)*14 + yoffset)
//     .text(value);
// }

// function printState(stateAtom, yoffset) {
//   for (r = 0; r <= 2; r++) {
//     for (c = 0; c <= 2; c++) {
//       printValue(r, c, yoffset,
//                  stateAtom.board[r][c]
//                  .toString().substring(0,1))  
//     }
//   }
  
//   d3.select(svg)
//     .append('rect')
//     .attr('x', 5)
//     .attr('y', yoffset+1)
//     .attr('width', 40)
//     .attr('height', 50)
//     .attr('stroke-width', 2)
//     .attr('stroke', 'black')
//     .attr('fill', 'transparent');
// }


// var offset = 0
// for(b = 0; b <= 10; b++) {  
//   if(State.atom("State"+b) != null)
//     printState(State.atom("State"+b), offset)  
//   offset = offset + 55
// }


// // Connect4
// const d3 = require('d3')
// d3.selectAll("svg > *").remove();

// function printValue(row, col, xoffset, yoffset, value) {
  
//   var color = "red"
//   if (value == "B")
//     color = "blue"
//   d3.select(svg)
//     .append("text")
//     .style("fill", color)
//     .attr("x", (col+1)*10 + xoffset)
//     .attr("y", (row+1.2)*14 + yoffset)
//     .text(value);
// }

// function printState(stateAtom, xoffset, yoffset) {
//   for (r = 0; r <= 5; r++) {
//     for (c = 0; c <= 6; c++) {
//       printValue(r, c, xoffset, yoffset,
//                  stateAtom.board[r][c]
//                  .toString().substring(0,1))  
//     }
//   }
  
//   d3.select(svg)
//     .append('rect')
//     .attr('x', xoffset+5)
//     .attr('y', yoffset+1)
//     .attr('width', 80)
//     .attr('height', 90)
//     .attr('stroke-width', 2)
//     .attr('stroke', 'black')
//     .attr('fill', 'transparent');
// }

// var col = 0
// var offset = 0
// for(b = 0; b <= 42; b++) {
//   if(State.atom("State"+b) != null)
//     printState(State.atom("State"+b), col*85 ,offset)
//   if (col == 4) {
//     col = 0
//     offset = offset + 95
//   } else {col = col + 1}  
// }