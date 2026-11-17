import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Discrete-time transitions and finite-step distributions

`Step x` is the conditional distribution of the next state given the current state
`x`. `Evolve` composes these kernels at each step; it does not reuse a single sampled
coordinate throughout a run. `StopAt` freezes the state after the goal is reached.
Time zero is initialization. These definitions do not themselves assert runtime
bounds or termination.
-/

namespace ECTheoryLib.Probability

/-- Assign a next-state probability distribution to each current state. -/
abbrev Transition (State : Type*) := State → PMF State

noncomputable section

/-- The initial law at time zero, followed by repeated composition with `Step`. -/
def Evolve {State : Type*} (Step : Transition State) (Initial : PMF State) :
    Nat → PMF State
  | 0 => Initial
  | t + 1 =>
      -- Mix the successor distributions using the current state's probability law.
      (Evolve Step Initial t).bind Step

/-- Inspect the current state and freeze it if the goal holds; otherwise take one step. -/
def StopAt {State : Type*} (Step : Transition State)
    (Goal : State → Prop) [DecidablePred Goal] (x : State) : PMF State :=
  if Goal x then
    
    PMF.pure x
  else
    Step x

/-- Goal states are absorbing under the stopped transition. -/
theorem StopAtOfGoal {State : Type*} (Step : Transition State)
    (Goal : State → Prop) [DecidablePred Goal] (x : State) (Reached : Goal x) :
    StopAt Step Goal x = PMF.pure x := by
  unfold StopAt
  rw [if_pos Reached]

/-- Before reaching the goal, the stopped and original transition kernels coincide. -/
theorem StopAtOfNotGoal {State : Type*} (Step : Transition State)
    (Goal : State → Prop) [DecidablePred Goal] (x : State) (NotReached : ¬ Goal x) :
    StopAt Step Goal x = Step x := by
  unfold StopAt
  rw [if_neg NotReached]

/-- Starting at a goal state, every finite-step stopped law remains concentrated there. -/
theorem EvolveStoppedOfGoal {State : Type*} (Step : Transition State)
    (Goal : State → Prop) [DecidablePred Goal] (x : State) (Reached : Goal x)
    (t : Nat) : Evolve (StopAt Step Goal) (PMF.pure x) t = PMF.pure x := by
  induction t with
  | zero =>
      
      rfl
  | succ t Previous =>
      
      rw [Evolve]
      rw [Previous]
      
      rw [PMF.pure_bind]
      exact StopAtOfGoal Step Goal x Reached

end
end ECTheoryLib.Probability
