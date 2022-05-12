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
    s.whoseTurn = P1
}
pred endState[s: State] {
    no s.cardsMoved
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

pred traces {
    some iState: State | initState[iState]
    all s1: State | (some s1.nextState) => Transition[s1] else endState[s1]
}

-- We modify traces to support "doing nothing" after a win. This doesn't change
-- the proofs, but it looks nicer when visualized, and it is important for
-- strategies.

pred doNothing[s: State] {
    no s.cardsMoved
    s.nextState.currValue = s.currValue
    s.nextState.whoseTurn = s.whoseTurn
}

pred Fold[s: State, p: Player] {
    p.hand[s.nextState] = p.hand[s]
    Pile.hand[s.nextState] = Pile.hand[s]
}

-- Player p wins exactly this turn
-- This happens only after the next player plays and isn't forced to pick up
-- their cards next turn. That is, they keep an empty hand for two turns
pred winningTurn[s: State, p: Player] {
    some s.~nextState
    no p.hand[s.(~nextState)]
    no p.hand[s]
}

pred completeTransition[s: State] {
    some s.nextState
    s.cardsMoved = {c: Card | moveCard[s, c]}
    (some p: Player | winningTurn[s, p]) => doNothing[s]
    -- One of three players who didn’t move last calls BS OR
    -- Current player playsCards
    else playCards[s] or (some caller: Player | callBS[s, caller])
}

pred completeTraces {
    some iState: State | initState[iState]
    all s1: State | (some s1.nextState) => completeTransition[s1] else endState[s1]
    some s: State | some p: Player | winningTurn[s, p]
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

    completeTraceHasVictor: {
        (wellFormed and completeTraces) => {
            all s: State | (no s.nextState) => (some p: Player | no p.hand[s])
        }
    } for 5 Int for FiveRanksFourSuitsTwoPlayers is theorem
}


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


pred canCallBS[s: State, p: Player] {
    some Pile.hand[s]
    s.~nextState.whoseTurn != p
}

pred playAllTrueCards[s: State] {
    // All cards in the player's hand that match the current value are played.
    all c: s.whoseTurn.hand[s] | (c.value = s.currValue) => c in s.cardsMoved
}
pred playsAllTrueCards[p: Player] {
    all s: State | ((s.whoseTurn = p) and playCards[s]) => playAllTrueCards[s]
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
    all s: State | playCards[s] => playAllTrueCards[s]
}


// A game consists of runs. At the start of each run, the pile is empty.
// A new run is started when a player calls BS.
// equivalent to init[] without the constraint that all players have the same
// number of cards
pred runInit[s: State] {
    no Pile.hand[s]
    s.currValue = 1
    s.whoseTurn = P1
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

    all s: State | (some s.nextState) => Transition[s] else endState[s]
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

-- Call BS when certain that a player has lied (unless another player does it)
pred callsEasyBSORT[p: Player] {
    all s: State | {
        playerKnowsOtherIsLyingORT[s, p] => {
            some p: Player | callBS[s.nextState, p]
        }
    }
}
pred onlyCallsEasyBSORT[p: Player] {
    all s: State | {
        callBS[s.nextState, p] => playerKnowsOtherIsLyingORT[s.nextState, p]
    }
}

pred allCallEasyBSORT {
    all s: State | {
        (some p: Player | playerKnowsOtherIsLyingORT[s, p]) => 
        (some p: Player | playerKnowsOtherIsLyingORT[s, p] and callBS[s.nextState, p])
    }
}

test expect {
    // Between two players, the optimal strategy is to not lie.

    ortVacuity: {
        wellFormed
        oneRunTrace
        allCallEasyBSORT
        fastShedding
    } for exactly 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is sat

    fastSheddingEquivalence: {
        fastShedding iff (all p: Player | playsAllTrueCards[p])
    } for exactly 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem


    pickupCausesSetback: {
        (wellFormed and oneRunTrace) => {
            all s: State, p: Player | pickUp[s, p] => {
                some iState, eState: State | {
                    runInit[iState]
                    runEnd[eState]
                    p.hand[iState] in p.hand[eState]
                }
            }
        }
    } for 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem

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
        (wellFormed and oneRunTrace and allCallEasyBSORT)
        some s: State | {
            playBS[s]
            no p: Player | playerKnowsOtherIsLyingORT[s, p]
        }
    } for exactly 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is sat

    -- If you play all true cards held and some extras, the other player will
    -- detect the lie.
    twoPlayersUnoptimalBS: {
        (wellFormed and oneRunTrace and allCallEasyBSORT and fastShedding) =>
        (all s: State | {
            playBS[s] iff {
                some p: Player | playerKnowsOtherIsLyingORT[s, p]
            }
        })
    } for 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem
    
    -- Stronger-ish version of the statement above
    -- At each turn, there's a limit to how many cards can be played.
    -- If you're supposed to play 3's and you held 2 at the start of the run,
    -- you can only play 2 cards at most when asked to play 3's.
    twoPlayersCantShedQuicker: {
        (wellFormed and oneRunTrace and allCallEasyBSORT) =>
        (all s: State | {
            playCards[s] and #(s.cardsMoved) > numCardsOfValueKnownORT[s.whoseTurn, s.currValue] => {
                some p: Player | playerKnowsOtherIsLyingORT[s, p]
            }
        })
    } for 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem

    oneBSPerRun: {
        (wellFormed and oneRunTrace and allCallEasyBSORT and fastShedding) => {
            lone s: State | playBS[s]
        }
    } for 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem
}



-- Now we prove a certain strategy for entire games.


-- All players start with one of each value
pred fairStart {
    some s: State | {
        no s.~nextState
        all p: Player | (p.hand[s]).value = Card.value
    }
}

// True if the player has cards that matches this turn's values
pred canPlayTruthfully[s: State, p: Player] {
    s.whoseTurn = p
    s.currValue in (Player.hand[s]).value
}

// Try not to BS
pred tryToPlayTruthfully[p: Player] {
    all s: State | {
        canPlayTruthfully[s, p] => dontPlayBS[s]
    }
}

pred alwaysCallBS[p: Player] {
    all s: State | canCallBS[s, p] => callBS[s, p]
}

pred neverCallBS[p: Player] {
    no s: State | callBS[s, p]
}


pred startsRun[s: State] {
    no Pile.hand[s]
}
pred occursBefore[s1: State, s2: State] {
    s1->s2 in ^nextState
}
pred startsMostRecentRun[s: State, curState: State] {
    (s = curState) or occursBefore[s, curState]
    startsRun[s]
    // There's no state between s and curState that also starts a run
    no s2: State | startsRun[s2] and occursBefore[s, s2] and
        (s2 = curState or occursBefore[s2, curState])
}

test expect {
    startsMostRecentRunORTCounting: {
        (wellFormed and oneRunTrace) => (
            (some s: State, p: Player | winningTurn[s, p]) => (
                #{runStart: State | some s: State | startsMostRecentRun[runStart, s]} <= 2
            ) else (
                -- Only the first and last states of a one-run trace start a run
                #{runStart: State | some s: State | startsMostRecentRun[runStart, s]}
                    = min[#State + 2]
            )
        )
    } for 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem

    startsMostRecentRunORT: {
        (wellFormed and oneRunTrace) => {
            all runStart: State | (some s: State | startsMostRecentRun[runStart, s])
                => (runInit[runStart] or runEnd[runStart])
        }
    } for 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem

    allStatesInOneRun: {
        (wellFormed and traces) => {
            all s: State | one runStart: State | startsMostRecentRun[runStart, s]
        }
    } for 5 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem
    
    multiRunVacuity: {
        wellFormed
        traces
        #{runStart: State | some s: State | startsMostRecentRun[runStart, s]} > 2
    } for 6 State, 5 Int for FiveRanksFourSuitsTwoPlayers is sat
}

fun cardsKnown[curState: State, p: Player]: set Card {
    p.hand[{s: State | startsMostRecentRun[s, curState]}]
}

-- The number of cards that the player knows about this run
-- If the player started with 2 Aces, then the numCardsOfValueKnown[p, 1]
-- would be 2.
fun numCardsOfValueKnown[curState: State, p: Player, v: Int]: one Int {
    #{c: cardsKnown[curState, p] | c.value = v}
}

// s refers to the state in which the other player plays their cards
pred playerKnowsOtherIsLying[s: State, p: player] {
    playCards[s]
    p != s.whoseTurn
    add[#(s.cardsMoved), numCardsOfValueKnown[s, p, s.currValue]] > #Suit
    -- Extra case due to bitwidth problems
    or add[#(s.cardsMoved), numCardsOfValueKnown[s, p, s.currValue]] < 1
}

-- Player strategies

-- Call BS when certain that a player has lied (unless another player does it)
pred callsEasyBS[p: Player] {
    all s: State | {
        playerKnowsOtherIsLying[s, p] => {
            some p: Player | callBS[s.nextState, p]
        }
    }
}
pred onlyCallsEasyBS[p: Player] {
    all s: State | {
        callBS[s.nextState, p] => {
            playerKnowsOtherIsLying[s, p]
            -- If the last play was a lie, we can't tell who calls BS here
            or (some otherPlayer: Player | callBS[s.nextState, otherPlayer])
        }
    }
}

pred playsOptimally[p: Player] {
    tryToPlayTruthfully[p] and playsAllTrueCards[p]
    callsEasyBS[p] and onlyCallsEasyBS[p]
}


test expect {
    gameVacuity: {
        wellFormed
        traces
        fairStart
    } for 20 State, 5 Int for FiveRanksFourSuitsTwoPlayers is sat
    gameStrategyVacuity: {
        wellFormed
        traces
        fairStart
        playsOptimally[P1]
    } for 20 State, 5 Int for FiveRanksFourSuitsTwoPlayers is sat
    completeGameVacuity: {
        wellFormed
        completeTraces
        fairStart
    } for 20 State, 5 Int for FiveRanksFourSuitsTwoPlayers is sat
    completeGameStrategyVacuity: {
        wellFormed
        completeTraces
        fairStart
        playsOptimally[P1]
    } for 20 State, 5 Int for FiveRanksFourSuitsTwoPlayers is sat

    canBSOptimal: {
        wellFormed
        completeTraces
        fairStart
        playsOptimally[P1]
        some s: State | (not winningTurn[s, P1]) and callBS[s, P1] 
    } for 20 State, 5 Int for FiveRanksFourSuitsTwoPlayers is sat

    p1WinsWhenP1Optimal: {
        (wellFormed and traces and fairStart and playsOptimally[P1]) => {
            some s: State, p: Player | winningTurn[s, p] =>
            (some s: State | winningTurn[s, P1])
        }
    } for 20 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem
    p1WinsWhenP1OptimalComplete: {
        (wellFormed and completeTraces and fairStart and playsOptimally[P1]) => {
            some s: State | winningTurn[s, P1]
        }
    } for 20 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem

    p1WinsWhenP1P2Optimal: {
        (wellFormed and completeTraces and fairStart and playsOptimally[P1] and playsOptimally[P2]) => {
            some s: State | winningTurn[s, P1]
        }
    } for 20 State, 5 Int for FiveRanksFourSuitsTwoPlayers is theorem

    p2LosesWhenStartIsUnfair: {
        (wellFormed and completeTraces and playsOptimally[P1]) => {
            some s: State | winningTurn[s, P2]
        }
    } for 20 State, 5 Int for FiveRanksFourSuitsTwoPlayers is sat

}

-- Run a standard trace of the game for 10 states.
// run {
//     wellFormed
//     traces
// } for 10 State, 5 Int for FiveRanksFourSuitsTwoPlayers

-- Run a trace of the game with a winner
// run {
//     wellFormed
//     completeTraces
// } for 20 State, 5 Int for FiveRanksFourSuitsTwoPlayers

-- Run a game where player 1 plays optimally.
run {
    wellFormed
    completeTraces
    fairStart
    playsOptimally[P1]
} for 20 State, 5 Int for FiveRanksFourSuitsTwoPlayers
