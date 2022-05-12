const d3 = require("d3");
d3.selectAll("svg > *").remove();


div.innerHTML = '';
const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
svg.style.height = `${(Math.ceil(State.atoms().length + 1)) * 280}px`;
div.style.maxHeight = '100vh';
div.style.overflow = 'auto';
div.appendChild(svg);


function printCard(stateAtom, card, xOffset, yOffset) {
  const cMoved = stateAtom.cardsMoved.toString().split('\n');
  const cardName = card._atoms[0]._id;

  d3.select(svg)
    .append("rect")
    .attr("x", xOffset)
    .attr("y", yOffset + 5)
    .attr("width", 25)
    .attr("height", 50)
    .attr("stroke-width", 1)
    .attr("stroke", "black")
    .attr("fill", cMoved.includes(cardName) ? 'gray' : "white")
    .text(card.value);
  // Number
  var c = Card.atom(cardName);
  d3.select(svg)
    .append("text")
    .attr("x", xOffset + 8)
    .attr("y", yOffset + 25)
    .text(c.value.toString());
  // Suit (either simply add text of suit, or more complicated add an image for suit)
  // h: heart
  // s: spades
  // c: club
  // d: diamond
  d3.select(svg)
    .append("text")
    .style("font", "14px times")
    .attr("x", xOffset + 8.5)
    .attr("y", yOffset + 45)
    .text(c.suit.toString()[0]);

}
const cToVal = (c) => parseInt(c._atoms[0].value._id);
const cToSuit = (c) => c._atoms[0].suit._id;

const sortHand = (h) =>
  h.sort((a, b) => {
    var n = cToVal(a) - cToVal(b);
    if (n !== 0) {
      return n;
    }
    console.log(cToSuit(a));
    console.log(cToSuit(b));
    return cToSuit(a).localeCompare(cToSuit(b));
  });

function printPile(stateAtom, player, xOffset, yOffset) {
  var curr_xOffset = xOffset + 10;
  sortHand(player.hand[stateAtom]._tuples).forEach((card) => {
    printCard(stateAtom, card, curr_xOffset, yOffset);
    curr_xOffset = curr_xOffset + 30;
  });
}

function printPlayer(stateAtom, player, xOffset, yOffset, bsCalled) {
  const playerTurn = stateAtom.whoseTurn.equals(player);

  // hand of cards
  if (playerTurn) {
    d3.select(svg)
      .append("text")
      .attr("x", xOffset + 10)
      .attr("y", yOffset + 25)
      .attr("font-weight", "bolder")
      .attr("fill", "red")
      .text("Player " + player.toString()[1] + "\u2190");

    if (bsCalled) {
      d3.select(svg)
        .append("text")
        .attr("x", xOffset + 90)
        .attr("y", yOffset + 25)
        .attr("fill", "orange")
        .text("Called BS");
    }
  } else {
    d3.select(svg)
      .append("text")
      .attr("x", xOffset + 10)
      .attr("y", yOffset + 25)
      .attr("font-weight", "bolder")
      .text("Player " + player.toString()[1]);
  }

  printPile(stateAtom, player, xOffset, yOffset + 25);
}

function printState(stateAtom, xOffset, yOffset) {
  // Print out the 2 players
  const minWidth = 400;

  d3.select(svg)
    .append("rect")
    .attr("x", xOffset)
    .attr("y", yOffset)
    .attr("width", 600)
    .attr("height", 260)
    .attr("fill", tableColor)
    .attr("stroke-width", 2)
    .attr("stroke", "black");

  const firstState = stateAtom.equals(State.atom("State0"));
  const emptyPile = Pile.atom("Pile0").hand[stateAtom].empty();

  const bsCalled = emptyPile && !firstState;

  printPlayer(stateAtom, P1.atom("P10"), xOffset, yOffset + 15, bsCalled);
  printPlayer(stateAtom, P2.atom("P20"), xOffset, yOffset + 90, bsCalled);

  // Current pile
  if (emptyPile) {
    d3.select(svg)
      .append("text")
      .attr("x", xOffset + 10)
      .attr("y", yOffset + 190)
      .attr("font-weight", "bolder")
      .text("Empty Pile");
  } else {
    d3.select(svg)
      .append("text")
      .attr("x", xOffset + 10)
      .attr("y", yOffset + 190)
      .attr("font-weight", "bolder")
      .text("Pile");
  }

  var curr_xOffset = xOffset + 10;

  if (!emptyPile) {
    sortHand(Pile.atom("Pile0").hand[stateAtom]._tuples).forEach((card) => {
      printCard(stateAtom, card, curr_xOffset, yOffset + 190);
      curr_xOffset = curr_xOffset + 30;
    });
  }

  // Current Value
  d3.select(svg)
    .append("text")
    .attr("x", xOffset + 10)
    .attr("y", yOffset + 20)
    .attr("font-weight", "bold")
    .text("Current Value: " + stateAtom.currValue.toString());

  // Cards Moved
  // d3.select(svg)
  //   .append("text")
  //   .attr("x", xOffset + 280)
  //   .attr("y", yOffset + 190)
  //   .attr("font-weight", "bolder")
  //   .text("Cards Moved");

  // Print cards moved
  // Is this necessary? Adds clutter + can be confusing since cards moved also includes bs calls (i.e cards moved != cards played)
  // var curr_xoffset = xOffset + 280;
  // stateAtom.cardsMoved._tuples.forEach((card) => {
  //   printCard(stateAtom, card, curr_xoffset, yOffset + 190);
  //   curr_xoffset = curr_xoffset + 30;
  // });
}

const tableColor = "#458554";

// var responsiveDivHeight = 30 * 30;
var legendSVG = d3
  .select(svg)
//   .attr("height", "100%")
  .attr("width", "100%")
//   .attr("viewBox", "0 0 850 " + responsiveDivHeight + "")
//   .attr("preserveAspectRatio", "xMinYMin");

// This is for the states, in this case b = 10 or 11 states
var yOffset = 0;
var xOffset = 0;
for (let stateNum = 0; stateNum < State.atoms().length; stateNum++) {
  const stateName = "State" + stateNum;

  var stateAtom = State.atom(stateName);

  printState(stateAtom, xOffset, yOffset);

  yOffset = yOffset + 280;
}
