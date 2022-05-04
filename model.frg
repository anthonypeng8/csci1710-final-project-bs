#lang forge

abstract sig Suit {}

one sig Hearts, Diamonds, Clubs, Spades extends Suit {}

sig Card {
    suit: one Suit,
    value: one Int
}

abstract sig CardHolder {
    hand: State -> set Card
}

sig Player extends CardHolder {
    nextPlayer: one Player
}

one sig P1, P2 extends Player {}

sig Pile extends CardHolder {}

sig State {
    currValue: one Int,
    nextState: lone State,
    whoseTurn: one Player,
    -- Optional fields:
    -- handPlayed: set Card,
    -- hasBS
}

-- If we want to run multiple games per trace
-- Currently unused
// sig Game {
//     gNextState: pfunc State -> State
// }

inst FiveRanksFourSuits {
    Card = `c0 + `c1 + `c2 + `c3 + `c4 + `c5 + `c6 + `c7 + `c8 + `c9 + `c10
        + `c11 + `c12 + `c13 + `c13 + `c14 + `c15 + `c16 + `c17 + `c18 + `c19
    
    suit = (`c0 + `c1 + `c2 + `c3 + `c4) -> Hearts
        + (`c5 + `c6 + `c7 + `c8 + `c9) -> Diamonds
        + (`c10 + `c11 + `c12 + `c13 + `c14) -> Clubs
        + (`c15 + `c16 + `c17 + `c18 + `c19) -> Spades

    nextState is linear
}


// Predicates:
pred wellFormed {
    -- Constrain values of cards -- should be contiguous
    Card.value in (1 + 2 + 3 + 4 + 5)
    #Card = mult[#Suit, 5]
    all s: Suit, val: Int | {
        val in (1 + 2 + 3 + 4 + 5) => (one c: Card | c.suit = s and c.value = val)
    }
    -- every card is either in pile or in a player's hand
    all s: State | {
      no c: Card | {
        not (c in P1.hand[s]) and not (c in P2.hand[s]) and not (c in Pile.hand[s]) 
        -- Cards must be in exactly one hand
        no disj ch1, ch2: CardHolder | c in ch1.hand[s] and ch2.hand[s]
      }
    }
}

pred initState[s: State] {
    -- Deal Cards Evenly to Players
    #{c: Card | c in P1.hand[s]} = #{c: Card | c in P2.hand[s]}
}


pred IncrementStateValue[s: State] {
    s.next.currValue == add[s.currValue, 1]
}

pred ResetStateValue[s: State] {
    s.currValue == 1
}

pred advanceTurn[s: State] {
    -- Player count advances
    s.next.whoseTurn = s.whoseTurn.nextPlayer
    -- Value count advances
    (s.currValue < 5) => IncrementStateValue[s]
    else ResetStateValue[s.next]
}

fun moveCard[s: one State, c: one Card] {
    some disj ch1, ch2: CardHolder | c in ch1.hand[s] and c in ch2.hand[s.next]
}

-- Returns the set of cards moved in that state
fun cardsMoved[s: one State]: set Card {
    {c: Card | moveCard[s, c]}
}

-- Returns the set of cards played in that state (if they took a turn that state)
// fun cardsPlayed[s: one State]: set Card {
//     {c: Card | some disj p1, p2: Player | }
// }

pred dontMoveCards[s: State, c: set Card] {
    -- keep these cards in the same hand
    one ch: CardHolder | c in ch.hand[s] and c in ch.hand[s.next]
}

-- The current player gives a few cards to the pile and the turn advances.
pred playCards[s: State] {
    -- Play a reasonable number of cards
    0 < #{cardsMoved[s]} and #{cardsMoved[s]} <= #{Suit}
    all c: Card | {
        moveCard[s, c] => {
            c in s.whoseTurn.hand[s]
            c in Pile.hand[s.next]
        }
    }

    advanceTurn[s]
}

pred pickUp[s: State, p: Player] {
	-- give Pile.hand to Player p
    all c: Card | {
        c in Pile.hand[s] => c in p.hand[s.next]
        else dontMoveCards[s, c]
    }
}

pred prevStatePlayedBS[s: State] {
    one prev_s: State | {
        prev_s.nextState == s
        cardsMoved[prev_s].value != prev_s.currValue
    }
}


pred callBS[s: State, caller: Player] {
    -- Pile must have cards (aka someone went last turn)
    some Pile.hand[s]
    -- Caller shouldn't call BS on themselves?
    caller != s.(~next).whoseTurn
    -- Give Pile to either previous player or caller
	prevStatePlayedBS[s] => pickUp[s, s.(~next).whoseTurn]
	else => pickUp[s, caller]
}

pred Transition[s: State] {
    -- One of three players who didn’t move last calls BS OR
    -- Current player playsCards
    
}

pred Fold[s: State, p: Player] {
    p.hand[s.next] == p.hand[s]
    Pile.hand[s.next] == Pile.hand[s]
}

pred traces {
    all s1: State | (some s1.next) => Transition[s1]
}

test expect {

}

run {
    wellFormed
    traces
} for exactly 20 Card for {nextState is linear}
