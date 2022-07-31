'reach 0.1';

//define enumerations for the hands that may be played, as well as the outcomes of the game.
const [ isHand, ROCK, PAPER, SCISSORS ] = makeEnum(3);
const [ isOutcome, B_WINS, DRAW, A_WINS ] = makeEnum(3);

// define the function that computes the winner of the game.
const winner = (handAlice, handBob) =>
    ((handAlice + (4 - handBob)) % 3);

//on first line, makes an assertion that when Alice plays Rock and Bob plays Paper, then Bob wins as expected
assert(winner(ROCK, PAPER) == B_WINS);
assert(winner(PAPER, ROCK) == A_WINS);
assert(winner(ROCK, ROCK) == DRAW);

//no matter what values are provided for handAlice and handBob, winner will always provide a valid outcome
forall(UInt, handAlice =>
    forall(UInt, handBob =>
        assert(isOutcome(winner(handAlice, handBob)))));

// whenever the same value is provided for both hands, no matter what it is, winner always returns DRAW.
forall(UInt, (hand) =>
    assert(winner(hand, hand) == DRAW));

const Player = {
    ...hasRandom, // <--- new!
    getHand: Fun([], UInt),
    seeOutcome: Fun([UInt], Null),
    informTimeout: Fun([], Null),
};

export const main = Reach.App(() => {
    const Alice = Participant('Alice', {
        ...Player,
        wager: UInt, // atomic units of currency
        deadline: UInt, // time delta (blocks/rounds)
    });
    const Bob = Participant('Bob', {
        ...Player,
        acceptWager: Fun([UInt], Null),
    });
    init();

    const informTimeout = () => { //defines the function as an arrow expression.
        each([Alice, Bob], () => {//each of the participants perform a local step.
            interact.informTimeout();//has them call the new informTimeout method.
        });
    };
    
    Alice.only(() => {
        const wager = declassify(interact.wager);
        const deadline = declassify(interact.deadline);
    });
    Alice.publish(wager, deadline)
        .pay(wager);
    commit();

    Bob.only(() => {
        interact.acceptWager(wager);
    });
    Bob.pay(wager)
        .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout));

    var outcome = DRAW;//defines the loop variable, outcome.
    // states the invariant that the body of the loop does not change the balance in the contract account and that outcome is a valid outcome.
    invariant( balance() == 2 * wager && isOutcome(outcome) );
    // begins the loop with the condition that it continues as long as the outcome is a draw.
    while (outcome == DRAW ) {
        commit ();

        Alice.only(() => {
            const _handAlice = interact.getHand();
            const [_commitAlice, _saltAlice] = makeCommitment(interact, _handAlice);
            const commitAlice = declassify(_commitAlice);
        });
        Alice.publish(commitAlice)
            .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));
        commit();

        unknowable(Bob, Alice(_handAlice, _saltAlice));
        Bob.only(() => {
            const handBob = declassify(interact.getHand());
        });
        Bob.publish(handBob)
            .timeout(relativeTime(deadline), () => closeTo(Alice, informTimeout));
        commit();

        Alice.only(() => {
            const saltAlice = declassify(_saltAlice);
            const handAlice = declassify(_handAlice);
        });
        Alice.publish(saltAlice, handAlice)
            .timeout(relativeTime(deadline), () => closeTo(Bob, informTimeout));
        checkCommitment(commitAlice, saltAlice, handAlice);

        outcome = winner(handAlice, handBob);
        continue;
    }

    assert(outcome == A_WINS || outcome == B_WINS);
    transfer(2 * wager).to(outcome == A_WINS ? Alice : Bob);
    commit();

    each([Alice, Bob], () => {
        interact.seeOutcome(outcome);
    });
});