axiom P : Prop
axiom Q : Prop
axiom R : Prop
axiom p : P
axiom q : q
#print And
#print Or
example : P ∨ Q := Or.inl p
def porq : P ∨ Q := Or.inl p
--return one more than the argument
def inc : Nat → Nat
| Nat.zero => Nat.zero
| Nat.succ n => Nat.succ (Nat.succ n)
-- Implication but in computing terms but type of function
axiom pimpr : P → R
axiom qimpr : Q → R
def porq_imp_r : (P ∨ Q) → R
| Or.inl p => pimpr p
| Or.inr q => qimpr q

/-
Prove: Assume we have proof of P ∨ Q and that it's called porq. The proof is by case analysis on porq. In the first case, the proof is constructed from a proof of P, but we can also have a proof of P → R. In the other case, porq must have been constructed from a proof of Q, but we also have a proof of Q → R. In either case, R must be true.
We've thus shown if P or Q is true, then R is true, and that proves P or Q → R.
-/
def foo : P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R
| And.intro p (Or.inl q) => Or.inl (And.intro p q)
| And.intro p (Or.inr r) => Or.inr (And.intro p r)

theorem no_contradiction : ¬ (P ∧ ¬ P)
