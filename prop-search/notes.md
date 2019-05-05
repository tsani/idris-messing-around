If the state succeeds, then what happens next depends on the presence of
subgoals. If there are subgoals, then we need to choose:
* do we try to solve them now?
* or do we return the term with holes in it to the caller and make that their
  problem?

Option 1 is simpler, I think.
The upshot is that we always return closed terms.

But it doesn't fucking work.

The type I settled on for the continuation is
Maybe (Tm Z) -> Either (State a) (Tm Z)

The Maybe indicates whether a solution was found, and the either is used to
indicate whether we need to keep going.

The issue is when in the D phase, when we're analyzing an implication.

If the term `t` we're analyzing has type `A ~> B`, with goal `C`, then the idea
is this: Form the term `App t _` and introduce a subgoal of type A. Continue
trying to deduce `C` from `App t _ : B`.

So we return a new State:
  - term: `App t _`.
  - type: `B`.
  - goal: `C`.
  - continuation:
    - on success: try to prove `A` from scratch.

Well now we have a problem with the CPS! The term `App t _` has one subgoal in
it, so it isn't a `Tm Z` anymore!

I think that the continuation should *preserve* the number of subgoals, but then
even this isn't right because sometimes we introduce subgoals!
