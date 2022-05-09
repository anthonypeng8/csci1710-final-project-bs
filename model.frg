#lang forge

abstract sig Suit {}

one sig Hearts, Diamonds, Clubs, Spades extends Suit {}

sig Card {
    suit: one Suit,
    value: one Int
}

abstract sig CardHolder {
    hand: set State -> Card
}

sig Player extends CardHolder {
    nextPlayer: one Player
}

one sig P1, P2 extends Player {}

one sig Pile extends CardHolder {}

sig State {
    currValue: one Int,
    nextState: lone State,
    whoseTurn: one Player,
    cardsMoved: set Card
    -- Optional fields:
    -- handPlayed: set Card,
    -- hasBS
}

-- If we want to run multiple games per trace
-- Currently unused
// sig Game {
//     gNextState: pfunc State -> State
// }

inst FiveRanksFourSuitsTwoPlayers {
    Card = `c0 + `c1 + `c2 + `c3 + `c4 + `c5 + `c6 + `c7 + `c8 + `c9 + `c10
        + `c11 + `c12 + `c13 + `c13 + `c14 + `c15 + `c16 + `c17 + `c18 + `c19
    Hearts = `Hearts0
    Diamonds = `Diamonds0
    Clubs = `Clubs0
    Spades = `Spades0
    Suit = Hearts + Diamonds + Clubs + Spades

    suit = (`c0 + `c1 + `c2 + `c3 + `c4) -> Hearts
        + (`c5 + `c6 + `c7 + `c8 + `c9) -> Diamonds
        + (`c10 + `c11 + `c12 + `c13 + `c14) -> Clubs
        + (`c15 + `c16 + `c17 + `c18 + `c19) -> Spades

    value = (`c0 + `c5 + `c10 + `c15) -> 1
        + (`c1 + `c6 + `c11 + `c16) -> 2
        + (`c2 + `c7 + `c12 + `c17) -> 3
        + (`c3 + `c8 + `c13 + `c18) -> 4
        + (`c4 + `c9 + `c14 + `c19) -> 5

    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    Pile = `Pile0
    CardHolder = Player + Pile

    nextState is linear
}


// Predicates:
pred wellFormed {
    -- Constrain values of cards -- should be contiguous
    Card.value in (1 + 2 + 3 + 4 + 5)
    #Card = multiply[#Suit, 5]
    all s: Suit, val: Int | {
        val in (1 + 2 + 3 + 4 + 5) => (one c: Card | c.suit = s and c.value = val)
    }
    -- every card is either in pile or in a player's hand
    all s: State | {
      no c: Card | {
        not (c in P1.hand[s]) and not (c in P2.hand[s]) and not (c in Pile.hand[s]) 
        -- Cards must be in exactly one hand
        or (some disj ch1, ch2: CardHolder | c in ch1.hand[s] and c in ch2.hand[s])
      }
    }
    -- TODO: nextPlayer is cyclic
    (^nextPlayer) = (Player -> Player)
}

pred initState[s: State] {
    no s.~nextState
    -- Deal Cards Evenly to Players
    #{c: Card | c in P1.hand[s]} = #{c: Card | c in P2.hand[s]}
    no Pile.hand[s]
    s.currValue = 1
}


pred IncrementStateValue[s: State] {
    s.nextState.currValue = add[s.currValue, 1]
}

pred ResetStateValue[s: State] {
    s.currValue = 1
}

pred advanceTurn[s: State] {
    -- Player count advances
    s.nextState.whoseTurn = s.whoseTurn.nextPlayer
    -- Value count advances
    (s.currValue < 5) => IncrementStateValue[s]
    else ResetStateValue[s.nextState]
}

pred dontAdvanceTurn[s: State] {
    -- Player count advances
    s.nextState.whoseTurn = s.whoseTurn
    -- Value count advances
    s.nextState.currValue = s.currValue
}

pred moveCard[s: one State, c: one Card] {
    some disj ch1, ch2: CardHolder | c in ch1.hand[s] and c in ch2.hand[s.nextState]
}

pred dontMoveCards[s: State, c: set Card] {
    -- keep these cards in the same hand
    one ch: CardHolder | c in ch.hand[s] and c in ch.hand[s.nextState]
}

-- The current player gives a few cards to the pile and the turn advances.
pred playCards[s: State] {
    some s.nextState
    -- Play a reasonable number of cards
    0 < #{s.cardsMoved} and #{s.cardsMoved} <= #{Suit}
    all c: Card | {
        moveCard[s, c] => {
            c in s.whoseTurn.hand[s]
            c in Pile.hand[s.nextState]
        }
    }

    advanceTurn[s]
}

pred pickUp[s: State, p: Player] {
    some Pile.hand[s]
	-- give Pile.hand to Player p
    all c: Card | {
        c in Pile.hand[s] => c in p.hand[s.nextState]
        else not moveCard[s, c]
    }
}

pred prevStatePlayedBS[s: State] {
    one prev_s: State | {
        prev_s.nextState = s
        prev_s.cardsMoved.value != prev_s.currValue
    }
}


pred callBS[s: State, caller: Player] {
    some s.nextState
    -- Pile must have cards (aka someone went last turn)
    some Pile.hand[s]
    -- Caller shouldn't call BS on themselves?
    caller != s.(~nextState).whoseTurn
    -- Give Pile to either previous player or caller
	prevStatePlayedBS[s] => pickUp[s, s.(~nextState).whoseTurn]
	else pickUp[s, caller]

    dontAdvanceTurn[s]
}

pred Transition[s: State] {
    some s.nextState
    -- One of three players who didn’t move last calls BS OR
    -- Current player playsCards
    s.cardsMoved = {c: Card | moveCard[s, c]}
    playCards[s] or (some caller: Player | callBS[s, caller])
}

pred Fold[s: State, p: Player] {
    p.hand[s.nextState] = p.hand[s]
    Pile.hand[s.nextState] = Pile.hand[s]
}

-- Player p wins exactly this turn
-- This happens only after the next player plays and isn't forced to pick up
-- their cards next turn. That is, they keep an empty hand for two turns
pred winningTurn[s: State, p: Player] {
    no p.hand[s.(~nextState)]
    no p.hand[s]
}

pred traces {
    some iState: State | initState[iState]
    all s1: State | (some s1.nextState) => Transition[s1]
}

test expect {
    vacuity: {
        wellFormed
        traces
    } for 5 Int for FiveRanksFourSuitsTwoPlayers is sat

    cardsHaveOneOwner: {
        (wellFormed and traces) => (all s: State | {
            all c: Card | one ch: CardHolder | c in ch.hand[s]
        })
    } for 5 Int for FiveRanksFourSuitsTwoPlayers is theorem

    cardsMustMove: {
        (wellFormed and traces) => {
            all s: State | (some s.nextState) => (some s.cardsMoved)
        }
    } for 5 Int for FiveRanksFourSuitsTwoPlayers is theorem

    manyCardsCanMove: {
        wellFormed
        traces
        some s: State | {
            (some s.nextState)
            #{s.cardsMoved} > 1
        }
    } for 5 Int for FiveRanksFourSuitsTwoPlayers is sat

    cardMovesToOrFromPile: {
        (wellFormed and traces) => (all s: State | {
            (some s.nextState) => (
                (s.cardsMoved in Pile.hand[s]) iff not (s.cardsMoved in Pile.hand[s.nextState])
            )
        })
    } for 5 Int for FiveRanksFourSuitsTwoPlayers is theorem

    -- Can't play cards and call BS in the same turn
    playAndBSAreExclusive: {
        (wellFormed and traces) => {
            all s: State | (some s.nextState) => {
                playCards[s] iff not (some p: Player | callBS[s, p])
            }
        }
    } for 5 Int for FiveRanksFourSuitsTwoPlayers is theorem

    -- Calling BS after another player called should be impossible
    cantCallBSTwice: {
        wellFormed
        traces
        some s: State | {
            (some s.nextState)
            some p1: Player | callBS[s, p1]
            some p2: Player | callBS[s.nextState, p2]
        }
    } for 5 Int for FiveRanksFourSuitsTwoPlayers is unsat

    -- With many players, multiple players could call BS in one turn because,
    -- if the last player BS'd, it doesn't matter who calls it.
    -- In our 2-player model, the current player's turn has to be the one to
    -- call bs
    // canCallBSTwiceInOneTurn: {
    //     wellFormed
    //     traces
    //     some s: State | {
    //         (some s.nextState)
    //         some disj p1, p2: Player | callBS[s, p1] and callBS[s, p2]
    //     }
    // } for 5 Int for FiveRanksFourSuitsTwoPlayers is sat
    cantCallBSTwiceInOneTurn: {
        wellFormed
        traces
        some s: State | {
            (some s.nextState)
            some disj p1, p2: Player | callBS[s, p1] and callBS[s, p2]
        }
    } for 5 Int for FiveRanksFourSuitsTwoPlayers is unsat


}

// run {
//     wellFormed
//     traces
// } for 10 State, 5 Int for FiveRanksFourSuitsTwoPlayers


// Strategies


// Some strategies we might want to test

// All players try to play truthfully
// Call BS whenever someone is on their last card
// Maybe develop some heuristics
    // # of total BS's needed
    // # of BS'd turns

// :Between two players, it's always possible to determine if someone is BS'ing.


// bla bla bla ignore what's below here

// Some strategies -- we set an initial state and test certain strategies

// True if the player has cards that matches this turn's values
pred canPlayTruthfully[s: State, p: Player] {
    s.currValue in (Player.hand[s]).value
}

pred canCallBS[s: State, p: Player] {
    some Pile.hand[s]
    s.~nextState.whoseTurn != p
}

pred playRightCards[s: State, p: Player] {
    // All cards in the player's hand that match the current value are played.
    {c: Player.hand[s] | c.value = s.currValue} in s.cardsMoved
}

pred canPlayBS[s: State] {
    some s.nextState
    -- Need cards to BS with
    (s.whoseTurn.hand[s]).value not in s.currValue
}

pred playBS[s: State] {
    playCards[s]
    s.cardsMoved.value not in s.currValue
}

// No BS is played this turn
pred dontPlayBS[s: State] {
    playCards[s]
    s.cardsMoved.value = s.currValue
}

-- Players always play a card if it is the correct value
pred fastShedding {
    all s: State | {
        playCards[s] => {
            -- Get rid of all cards of the right value
            -- aka, next turn, there shouldn't be any cards of that value in the
            -- current player's hand
            -- Example: if the current player has to play 3's, next state, they
            -- shouldn't be holding any 3's.
            s.currValue not in (s.whoseTurn.hand[s.nextState]).value
        }
    }
}

// A game consists of runs. At the start of each run, the pile is empty.
// A new run is started when a player calls BS.
// equivalent to init[] without the constraint that all players have the same
// number of cards
pred runInit[s: State] {
    no Pile.hand[s]
    s.currValue = 1
}
pred runEnd[s: State] {
    -- Either the pile is empty or a player's hand is empty
    no Pile.hand[s] or (some p: Player | winningTurn[s, p])
}

// True if the trace contains only one run
pred oneRunTrace {
    -- Enforce one run
    some s: State | (no s.~nextState) and runInit[s]
    some s: State | (no s.nextState) and runEnd[s]
    -- No states in between can have an empty pile
    no s: State | (some s.nextState and some s.~nextState and runEnd[s])

    all s: State | (some s.nextState) => Transition[s]
}

// ORT = one-run trace, only use this pred with oneRunTrace
-- The number of cards that the player knows about this run
-- If the player started with 2 Aces, then the numOfCardsOfValueKnownORT[p, 1]
-- would be 2.
fun numCardsOfValueKnownORT[p: Player, v: Int]: one Int {
    let runInitState = {s: State | runInit[s]} |
        #{c: p.hand[runInitState] | c.value = v}
}

// s refers to the state in which the other player plays their cards
pred playerKnowsOtherIsLyingORT[s: State, p: player] {
    playCards[s]
    p != s.whoseTurn
    add[#(s.cardsMoved), numCardsOfValueKnownORT[p, s.currValue]] > #Suit
    -- Extra case due to bitwidth problems
    or add[#(s.cardsMoved), numCardsOfValueKnownORT[p, s.currValue]] < 1
}

-- Call BS when certain that a player has lied
pred callEasyBS {
    all s: State | {
        (some p: Player | playerKnowsOtherIsLyingORT[s, p]) => 
        (some p: Player | playerKnowsOtherIsLyingORT[s, p] and callBS[s, p])
    }
}


test expect {
    // Between two players, the optimal strategy is to not lie.

    ortVacuity: {
        wellFormed
        oneRunTrace
        callEasyBS
        fastShedding
    } for exactly 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is sat

    // Test for playerKnowsOtherIsLyingORT
    // If some player detects a BS, then it has to be certain.
    testLieDetection: {
        (wellFormed and oneRunTrace) => {
            all s: State | {
                (some p: Player | playerKnowsOtherIsLyingORT[s, p]) => playBS[s]
            }
        }
    } for 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem

    -- It is possible to play false cards and not be called on it, even with two
    -- players. (You just don't get any advantage from it.)
    twoPlayersCanPlayBS: {
        (wellFormed and oneRunTrace and callEasyBS)
        some s: State | {
            playBS[s]
            no p: Player | playerKnowsOtherIsLyingORT[s, p]
        }
    } for exactly 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is sat

    -- If you play all true cards held and some extras, the other player will
    -- detect the lie.
    twoPlayersUnoptimalBS: {
        (wellFormed and oneRunTrace and callEasyBS and fastShedding) =>
        (all s: State | {
            playBS[s] => {
                some p: Player | playerKnowsOtherIsLyingORT[s, p]
            }
        })
    } for 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem
    
    -- Stronger version of the statement above
    -- At each turn, there's a limit to how many cards can be played.
    -- If you're supposed to play 3's and you held 2 at the start of the run,
    -- you can only play 2 cards at most when asked to play 3's.
    twoPlayersCantShedQuicker: {
        (wellFormed and oneRunTrace and callEasyBS) =>
        (all s: State | {
            playCards[s] and #(s.cardsMoved) > numCardsOfValueKnownORT[s.whoseTurn, s.currValue] => {
                some p: Player | playerKnowsOtherIsLyingORT[s, p]
            }
        })
    } for 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem

    -- TODO: Determine exactly who wins for 2 players
}


// Junk section

// Try not to BS
pred tryToPlayTruthfully[p: Player] {
    all s: State | {
        (some s.nextState and canPlayTruthfully[s, p]) => playRightCards[s, p]
    }
}

pred alwaysBS[p: Player] {
    all s: State | canCallBS[s, p] => callBS[s, p]
}

pred neverBS[p: Player] {
    no s: State | callBS[s, p]
}
