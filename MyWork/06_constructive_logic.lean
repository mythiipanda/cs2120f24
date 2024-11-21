namespace cs2120f24.constructiveLogic

/-! HOMEWORK #5. COUNTS FOR TWO ASSIGNMENTS.

This is an important homework. It gives you an
opportunity to work out many of the kinks in your
understanding of predicate logic and deductive
proofs in type theory. With P, Q, and R accepted
as propositions, you are to give proofs of all of
the identities from Library/propLogic/identities,
which I've rewritten in Lean for you. There's one
of these axioms that has no constructive proof (in
just one direction). You can just identify it.
-/


-- Suppse P, Q, and R are arbitrary propositions
axiom P : Prop
axiom Q : Prop
axiom R : Prop

/-!
Give proofs in Lean that each of the following identities
is valid. We already know they're classically valid as we
validated their propositional logic analogics semantically
using our model / validity checker. To get you started with
a concrete example, we prove the first one for you and give
a little English explanation after. You should od the same
for each proposition you prove.
-/


def andIdempotent   : P ↔ (P ∧ P) :=
Iff.intro
  -- forward direction: P → P ∧ P
  -- assume p : P, show P ∧ P
  (fun (p : P) => And.intro p p)
  -- backwards direction: P ∧ P → P
  (fun (pimpp : P ∧ P) => pimpp.left)

/-!
In English. We are to show that any proposition
P is equivalent to P ∧ P. By the Iff.intro axiom,
it will suffice to first prove P → P ∧ P and then
to prove P ∧ P → P. With that we'll be done.

Proof of forward direction: P → P ∧ P. Assume we
have a proof (p : P). Then applying the axiom
of And introduction to p and p, we can derive the
proof of P ∧ P that will show that if P is true,
then P ∧ P is true. So P → P ∧ P.

Proof of backward direction. P ∧ P → P. Assume
we have a proof, pandp : P ∧ P. By either one of
the two elimination axioms we can derive a proof
of p: as either pandp.left or pandp.right.
-/

def orIdempotent    : P ↔ (P ∨ P) :=
Iff.intro
  (fun (p : P) => Or.inl p)
  (fun (porp : P ∨ P) => porp.elim (fun (p : P) => p) (fun (p : P) => p))

def andCommutative  : (P ∧ Q) ↔ (Q ∧ P) :=
Iff.intro
  (fun (pandq : P ∧ Q) => And.intro pandq.right pandq.left)
  (fun (qandp : Q ∧ P) => And.intro qandp.right qandp.left)

def orCommutative   : (P ∨ Q) ↔ (Q ∨ P) :=
Iff.intro
  (fun (porq : P ∨ Q) => porq.elim (fun (p : P) => Or.inr p) (fun (q : Q) => Or.inl q))
  (fun (qorp : Q ∨ P) => qorp.elim (fun (q : Q) => Or.inr q) (fun (p : P) => Or.inl p))

def identityAnd     : (P ∧ True) ↔ P :=
Iff.intro
  (fun (pandt : P ∧ True) => pandt.left)
  (fun (p : P) => And.intro p True.intro)

def identityOr      : (P ∨ False) ↔ P :=
Iff.intro
  (fun (porf : P ∨ False) => porf.elim (fun (p : P) => p) (fun (f : False) => False.elim f))
  (fun (p : P) => Or.inl p)

def annhilateAnd    : (P ∧ False) ↔ False  :=
Iff.intro
  (fun (pandf : P ∧ False) => pandf.right)
  (fun (f : False) => False.elim f)

def annhilateOr     : (P ∨ True) ↔ True :=
Iff.intro
  (fun (port : P ∨ True) => True.intro)
  (fun (t : True) => Or.inr t)

def orAssociative   : ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R)) :=
Iff.intro
  -- forward direction: ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R))
  (fun (pq_r : (P ∨ Q) ∨ R) =>
    Or.elim pq_r
      (fun (pq : P ∨ Q) =>
        Or.elim pq
          (fun (p : P) => Or.inl p)
          (fun (q : Q) => Or.inr (Or.inl q)))
      (fun (r : R) => Or.inr (Or.inr r)))
  -- backward direction: (P ∨ (Q ∨ R)) → ((P ∨ Q) ∨ R)
  (fun (p_qr : P ∨ (Q ∨ R)) =>
    Or.elim p_qr
      (fun (p : P) => Or.inl (Or.inl p))
      (fun (qr : Q ∨ R) =>
        Or.elim qr
          (fun (q : Q) => Or.inl (Or.inr q))
          (fun (r : R) => Or.inr r)))

def andAssociative  : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
Iff.intro
  -- forward direction: ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
  (fun (pqr : (P ∧ Q) ∧ R) =>
    And.intro
      (pqr.left.left)
      (And.intro pqr.left.right pqr.right))
  -- backward direction: (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
  (fun (pqr : P ∧ (Q ∧ R)) =>
    And.intro
      (And.intro pqr.left pqr.right.left)
      pqr.right.right)

def distribAndOr    : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) :=
Iff.intro
  -- forward direction: (P ∧ (Q ∨ R)) → ((P ∧ Q) ∨ (P ∧ R))
  (fun (p_qr : P ∧ (Q ∨ R)) =>
    Or.elim p_qr.right
      (fun (q : Q) => Or.inl (And.intro p_qr.left q))
      (fun (r : R) => Or.inr (And.intro p_qr.left r)))
  -- backward direction: ((P ∧ Q) ∨ (P ∧ R)) → (P ∧ (Q ∨ R))
  (fun (pq_pr : (P ∧ Q) ∨ (P ∧ R)) =>
    pq_pr.elim
      (fun (pq : P ∧ Q) => And.intro pq.left (Or.inl pq.right))
      (fun (pr : P ∧ R) => And.intro pr.left (Or.inr pr.right)))

def distribOrAnd    : (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R)) :=
Iff.intro
  -- forward direction: (P ∨ (Q ∧ R)) → ((P ∨ Q) ∧ (P ∨ R))
  (fun (p_qr : P ∨ (Q ∧ R)) =>
    p_qr.elim
      (fun (p : P) => And.intro (Or.inl p) (Or.inl p))
      (fun (qr : Q ∧ R) => And.intro (Or.inr qr.left) (Or.inr qr.right)))
  -- backward direction: ((P ∨ Q) ∧ (P ∨ R)) → (P ∨ (Q ∧ R))
  (fun (pq_pr : (P ∨ Q) ∧ (P ∨ R)) =>
    Or.elim pq_pr.left
      (fun (p : P) => Or.inl p)
      (fun (q : Q) =>
      Or.elim pq_pr.right
          (fun (p : P) => Or.inl p)
          (fun (r : R) => Or.inr (And.intro q r))))

def equivalence     : (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) :=
Iff.intro
  -- forward direction: (P ↔ Q) → ((P → Q) ∧ (Q → P))
  (fun (piffq : P ↔ Q) => And.intro piffq.mp piffq.mpr)
  -- backward direction: ((P → Q) ∧ (Q → P)) → (P ↔ Q)
  (fun (pq_qp : (P → Q) ∧ (Q → P)) => Iff.intro pq_qp.left pq_qp.right)

def implication     : (P → Q) ↔ (¬P ∨ Q) :=
Iff.intro
  (fun (h : P → Q) =>
    (Or.inr P))
  (fun (h : (¬P ∨ Q)) =>
    (fun (p : P) =>
      Or.elim
      h
      (fun (k : ¬P) => False.elim (k p))
      (fun q => q)
    )
  )

def exportation     : ((P ∧ Q) → R) ↔ (P → Q → R) :=
Iff.intro
  -- forward direction: ((P ∧ Q) → R) → (P → Q → R)
  (fun (pqr : (P ∧ Q) → R) =>
    fun (p : P) =>
      fun (q : Q) =>
        pqr (And.intro p q))
  -- backward direction: (P → Q → R) → ((P ∧ Q) → R)
  (fun (pqr : P → Q → R) =>
    fun (pq : P ∧ Q) =>
      pqr pq.left pq.right)

def absurdity       : (P → Q) ∧ (P → ¬Q) → ¬P :=
fun (pq_pnq : (P → Q) ∧ (P → ¬Q)) =>
  fun (p : P) =>
    (pq_pnq.right p) (pq_pnq.left p)

-- def distribNotAnd   : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) :=
-- no constructive proof

def distribNotOr    : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) :=
Iff.intro
  -- forward direction: ¬(P ∨ Q) → (¬P ∧ ¬Q)
  (fun (nporq : ¬(P ∨ Q)) =>
    And.intro
      (fun (p : P) => nporq (Or.inl p))
      (fun (q : Q) => nporq (Or.inr q)))
  -- backward direction: (¬P ∧ ¬Q) → ¬(P ∨ Q)
  (fun (npandnq : ¬P ∧ ¬Q) =>
    fun (porq : P ∨ Q) =>
      porq.elim
        (fun (p : P) => npandnq.left p)
        (fun (q : Q) => npandnq.right q))


/-!
EXTRA CREDIT: apply the axiom of the excluded middle
to give a classical proof of the one proposition that
you identified as having no constructive proof. The
axiom is available as Classical.em (p : Prop) : p ∨ ¬p.
-/
def absurdity1 : (P → Q) ∧ (P → ¬Q) → ¬P :=
  fun (pq_and_pnq : (P → Q) ∧ (P → ¬Q)) =>
    Or.elim (Classical.em P)
      -- Case 1: Assume P is true
      (fun (p : P) =>
        let pq := pq_and_pnq.left    -- We have P → Q
        let pnq := pq_and_pnq.right  -- We have P → ¬Q
        let q := pq p                -- From P, we conclude Q
        let nq := pnq p              -- From P, we conclude ¬Q
        False.elim (nq q))           -- Contradiction: Q and ¬Q are both true
      -- Case 2: Assume ¬P is true
      (fun (np : ¬P) => np)          -- Directly conclude ¬P
#check Classical.em
-- Classical.em (p : Prop) : p ∨ ¬p
-- Given any proposition p, you can have a proof of p ∨ ¬p
-- You then have two cases: one with a proof of p, one with ¬p
example (A : Prop) : A ∨ ¬A := Classical.em A
