
# Modeling BS

## Background

Our project aimed to model the card game BS (typically a drinking card game). In this game, players take turns placing down cards of increasing rank, with the objective of getting rid of all of their cards. Players may choose to lie by placing down cards of a different rank, although if another player calls “BS”, the liar will pick up all played cards. If a player calls “BS” when the last played hand did not contain false cards, the player who called “BS” picks up the cards instead.

## Model

Our project achieved two main modeling goals: model the mechanics of the game, and test the viability of a certain strategy.

As modeled, the game is complete, with players able to play cards, lie, and call BS.

For strategy testing, we tested a basic strategy where a player avoids placing false cards and calls BS if and only if the player is certain that the last player played false cards.
Our first tests showed that, in two player-games, players will be able to detect a lie if the number of cards placed that turn exceeds a certain number. The reasoning is that, if players can remember how many cards of each rank they held at the start of a round, they can deduce how many cards the other player holds of each rank.
We then tested that, in two-player games, if each player starts off with similar decks, the first player will always win by playing with this strategy, for games up to 20 states. However, testing also showed that, if games did not start in ideal arrangements, it was possible for the second player to win.

## Assumptions

We assume that Players will only lie about the ranks of the cards played and not the quantity. This lets us assume what the player claims they have played by counting the number of cards they put down and the rank they were supposed to play.

### Tradeoffs/Limits

We limited the size of the deck to 20 cards, with five ranks and four suits. Modeling a full deck with 13 ranks would have increased the search space and extended the lengths of games in a way we felt was unnecessary to our model’s needs.

We also limited games to two players because testing player behavior across more than two players involves a level of risk and probability that Forge has difficulty modeling. Testing with more than two players was also much slower due to longer games and an increase in possible actions.

## Instance/Visualization

To use the visualizer, copy the contents of visualization.js into Forge’s visualizer and select the “div” option.

An instance of the model will have either 10 or 20 states, where as shown in the custom visualization, each state of the game displays the hands of the 2 players, whose turn, the resulting pile, the current rank, whether BS was called, and the cards that were moved.
