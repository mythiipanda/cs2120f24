import «Cs2120f24».Library.propLogic.syntax
import «Cs2120f24».Library.propLogic.model_theory.counterexamples

namespace cs2120f24.propLogic

/-!
# Exam 1: MidTerm

This is an individual exam. You must complete it entirely on your own,
with no outside inputs of any kind other than in response to questions
posed directly to the instructor. You must take the exam while in class
in the classroom. When you come in to the classroom, spread yourselves
out, mix up, and don't sit where you or someone you know of might hope to
catch a glance.

TO TAKE THIS EXAM: First copy it into your MyWork directory. Then complete
it. THEN SAVE IT. Then upload it. THEN CHECK YOUR UPLOAD, correcting it if
necessary.
-/



/-!
PART #1: Reading, writing, and expressing ideas in PL.
-/

/-
To begin with we give you declarations of three propositional logic
variables from which we'll construct variable *expressions* to use in
constructing larger propositions (expressions) in propositional logic.
The questions that then follow refer back to these propositions.
-/

-- First define a disting variable for each variable expression
def v₀ : BoolVar := BoolVar.mk 0    -- abstract syntax for a variable
def v₁ : BoolVar := ⟨1⟩             -- Lean gives this notation for mk
def v₂ : BoolVar := ⟨2⟩

-- With these variables, we can now constuct three variable expressions.
def P := PLExpr.var_expr v₀         -- abstract syntax for variable expression
def Q := { v₁ }                     -- we defined correspond concrete syntax
def R := { v₂ }

-- And now here are the expressions we car about
def e1 : PLExpr := (R ⇒ ⊥) ⇒ ¬R
def e2 : PLExpr :=
  (P ⇒ Q ⇒ P ∧ Q) ⇒
  (P ∧ Q ⇒ P) ⇒
  (P ∧ Q ⇒ Q) ⇒
  ((P ∧ Q) ⇒ (Q ∧ P))
def e3 := (P ↔ Q) ∧ (Q ↔ R) ⇒ (P ↔ R)
def e4 := ¬(P ∨ Q) ↔ (¬P ∧ ¬ Q)
def e5 := (P ⇒ Q) ⇒ P ⇒ R


/- Part #1, A
For each proposition, e1 - e5, (1) give a precise English language rendering
of the proposition from left to right, (2) then give an English rendering from
right to left.
_
Give you answers here:

e1:
Whenever R is true, then it is impossible, then not R is true.
If you want to know that not R is true, then it suffices to say that whenever R is true, then it is impossible.

e2:
If (whenever P is true, and in addition Q is true, then P and Q is true) and whenever that is true, (if P or Q is true, then P is also true), and in addition (if P or Q is true, then Q is true), and in addition to that whenever (P and Q)  is true, then (Q and P) is also true.
If you want to know that (whenever (P and Q) is true, then (Q and P) is also true), then it suffices to say that when (P or Q is true, then Q is true) and in addition to that when (P or Q is true, then P is also true), and in addition to that when (whenever P is true, and in addition Q is true, then P and Q is true).
e3:
Whenever P is true if and only if Q is true and Q is true if and only R is true, then P is true if and only if R is true.
If you want to know that P is true if and only if R is true, then it suffices to say that P is true if and only if Q is true and Q is true if and only if R is true.
e4:
Not (P or Q) is true if and only if (not P and not Q) is true.
Not P and not Q is true if and only if not (P or Q) is true.
e5:
Whenever P is true, Q is true, and in addition to that P is true, then R is true.
If you want to know that R is true, then it suffices to say that P is true, and in addition whenever P is true, Q is true.

-/

/- Part #1, B
Give formal versions of the following propositions expressed in English.
You may use the variable expressions, P, Q, and R in writing your answers.

A. "Going to school makes you smart."

(Use "P" for the proposition, "GoesToSchool" and "Q" for "IsSmart".
-/
def f1 : PLExpr := P ⇒ Q

/-
B. If you learn at home (P) or you learn at school (Q) then you'll be smart (R)
-/
def f2 : PLExpr := (P ∨ Q) ⇒ R

/-
C. It's not true that truth is (equivalent to) not truth.
-/
def f3 : PLExpr := ¬(⊤ ↔ ¬ ⊤)

-- #eval! is_valid f3
/-
Part $2: Semantic Validity

#A. Write a truth table for the proposition (P ⇒ Q) ⇒ (Q ⇒ P)

| P | Q | (P ⇒ Q) | (Q ⇒ P) | (P ⇒ Q) ⇒ (Q ⇒ P) |
| F   F      T          T         T
| F   T      T          F         F
| T   F      F          T         T
| T   T      T          T         T

Part #2, B: The proposition is not valid. Give an interpretation
that serves as a counter-example and a corresponding real world example
where some condition P implies some condition Q, but where Q being the
case does not necessarily mean that P is, too.
If it is not raining but the streets are wet, where P is whether or not its raining and Q is whether or not the streets are wet.
This is a counterexample because if it is not raining, and the streets are still wet, the streets can be wet due to some other factor (like sprinkling) and not be raining.


Part #2, D. Suppose you have a function that, when given any proposition in
PL, returns a list of its models, but that you need a function that returns
a list of its counterexamples. Describe very briefly how you'd implement a
new counterexamples-finding function, given a models finder. What type of
argument(s) would your new function take, and what would it do with it/them
to compute the desired answer.

Answer here: Given that we have a a function (find models e) that returns the list of models, e is some proposition, we can do find models ¬ e to find a list of counterexamples.
This is because there is a model to a proposition, then a counterexample would be a model to the negation of the proposition.

MODEST EXTRA CREDIT: Suppose you have a models-finding function. We use
"sorry" in the first definition below to tell Lean just to assume we've
provided a definition of a modelsFinding function. Just pretend that it
is fully defined and that it works. Complete the implementation of the
counterexamples-finder.
-/

def modelsFinder : PLExpr → List BoolInterp := sorry

-- complete this definition
def counterexamplesFinder : PLExpr → List BoolInterp
| e => modelsFinder (¬ e)



/-
PART #3: Counting Things
-/

/-
A. Suppose you have a PL expression that uses N distinct PL variables. Give a
formula that tells you how many interpretations there are for that expression.
number of intrepretations = 2^N

B. Give an algebraic formula for the number of distinct functions there are
from N Boolean input values to a Boolean output. Two functions are equal in
our formulation if they produce the same outputs on *all* inputs, otherwise
they are unequal/distinct.
number of distinct functions = 2^(2^N)

C. Consider a language of arithmetic expressions, where variables now have
natural number values, rather than Boolean values like PL variables. How
many interpretations are there for this expression: (X + 2) * (Y - 5) = 0?

Answer: infinite since X and Y can be any natural number

Tiny extra credit: give both a model and a counterexample for this formula.

Answer:
Model: X = -2, Y = 5
Counterexample: X = 2, Y = 3

-/


/- Part #4: Inductive thinking

Inductive data type definitions and recursive functions are vital
to how we've defined both the syntax and semantics of PL and other
expression languages. This question is meant to test your ability
to read and complete such definitions.

Here's a definition of a "NatTree" data type that we just made
up. A NatTree is either empty, or it's a node holding a Nat value
and two smaller trees.

Complete the definition of the function, given here, that takes a
NatTree and returns the number of nodes it contains.
-/

inductive NatTree : Type where
| empty
| node (n : Nat) (left : NatTree) (right : NatTree)

open NatTree

-- Complete this definition by replacing the line with the sorry

def numNatTreeNodes : NatTree → Nat
| empty => 0
| node n left right => 1 + numNatTreeNodes left + numNatTreeNodes right
-- def node0: NatTree := empty
-- def node1: NatTree := node 1 node0 node0
-- def node2: NatTree := node 2 node1 node1
-- def tree1: NatTree := node 2 node1 node1
-- def tree2: NatTree := node 3 node2 node1
-- #eval! numNatTreeNodes tree2
end cs2120f24.propLogic
