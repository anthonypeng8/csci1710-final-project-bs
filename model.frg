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

-- Returns the set of cards played in that state (if they took a turn that state)
// fun cardsPlayed[s: one State]: set Card {
//     {c: Card | some disj p1, p2: Player | }
// }

pred dontMoveCards[s: State, c: set Card] {
    -- keep these cards in the same hand
    one ch: CardHolder | c in ch.hand[s] and c in ch.hand[s.nextState]
}

-- The current player gives a few cards to the pile and the turn advances.
pred playCards[s: State] {
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
    } for FiveRanksFourSuitsTwoPlayers is sat

    cardsHaveOneOwner: {
        (wellFormed and traces) => (all s: State | {
            all c: Card | one ch: CardHolder | c in ch.hand[s]
        })
    } for FiveRanksFourSuitsTwoPlayers is theorem

    cardsMustMove: {
        (wellFormed and traces) => {
            all s: State | (some s.nextState) => (some s.cardsMoved)
        }
    } for FiveRanksFourSuitsTwoPlayers is theorem

    manyCardsCanMove: {
        wellFormed
        traces
        some s: State | {
            (some s.nextState)
            #{s.cardsMoved} > 1
        }
    } for FiveRanksFourSuitsTwoPlayers is sat

    cardMovesToOrFromPile: {
        (wellFormed and traces) => (all s: State | {
            (some s.nextState) => (
                (s.cardsMoved in Pile.hand[s]) iff not (s.cardsMoved in Pile.hand[s.nextState])
            )
        })
    } for FiveRanksFourSuitsTwoPlayers is theorem

    -- Can't play cards and call BS in the same turn
    playAndBSAreExclusive: {
        (wellFormed and traces) => {
            all s: State | (some s.nextState) => {
                playCards[s] iff not (some p: Player | callBS[s, p])
            }
        }
    } for FiveRanksFourSuitsTwoPlayers is theorem

    -- Calling BS after another player called should be impossible
    cantCallBSTwice: {
        wellFormed
        traces
        some s: State | {
            (some s.nextState)
            some p1: Player | callBS[s, p1]
            some p2: Player | callBS[s.nextState, p2]
        }
    } for FiveRanksFourSuitsTwoPlayers is unsat

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
    // } for FiveRanksFourSuitsTwoPlayers is sat
    cantCallBSTwiceInOneTurn: {
        wellFormed
        traces
        some s: State | {
            (some s.nextState)
            some disj p1, p2: Player | callBS[s, p1] and callBS[s, p2]
        }
    } for FiveRanksFourSuitsTwoPlayers is unsat

}

run {
    wellFormed
    traces
} for 10 State for FiveRanksFourSuitsTwoPlayers
