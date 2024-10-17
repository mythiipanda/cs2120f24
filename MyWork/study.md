# Discrete Math and Theory 1 Study Guide: Detailed Solutions

## 1. Languages and Paradigms

### Key Concepts:

1. Natural vs. formal languages:
   - Natural languages (e.g., English) are used for human communication and evolved naturally over time.
   - Formal languages (e.g., programming languages, mathematical notation) are designed for specific purposes and have precise, unambiguous rules.

2. Procedural/imperative vs. declarative formal languages:
   - Procedural/imperative languages specify a sequence of steps to achieve a result (e.g., Python, C).
   - Declarative languages describe what should be accomplished without specifying how (e.g., SQL, Prolog, Lean).

### Practice Problems:

1.1 Compare and contrast procedural and declarative languages using the example of finding a square root.

Solution:
Procedural (Python) approach:
```python
def square_root(n, epsilon=1e-6):
    guess = n / 2
    while abs(guess * guess - n) > epsilon:
        guess = (guess + n / guess) / 2
    return guess
```
This approach specifies step-by-step how to calculate the square root using the Newton-Raphson method.

Declarative (Lean) approach:
```lean
def is_square_root (x y : ℝ) : Prop :=
  y ≥ 0 ∧ y * y = x

theorem square_root_exists (x : ℝ) (h : x ≥ 0) :
  ∃ y, is_square_root x y :=
  -- proof omitted
```
This approach defines what a square root is and asserts its existence for non-negative real numbers, without specifying how to compute it.

1.2 Identify whether the following are natural or formal languages, and if formal, whether they are procedural or declarative:

a) English: Natural language
b) Python: Formal language, primarily procedural/imperative
c) SQL: Formal language, declarative
d) Lean: Formal language, declarative (specifically, a proof assistant based on dependent type theory)

## 2. Propositional Logic Basics

### Key Concepts:

1. Propositions: Statements that are either true or false.
2. Logical connectives: NOT (¬), AND (∧), OR (∨), IMPLIES (→), IFF (↔)
3. Truth values: True (T) and False (F)
4. Boolean algebra: The algebraic structure dealing with the combination and manipulation of logical values.

### Practice Problems:

2.1 Define the following operations in Boolean algebra:

a) XOR (exclusive or):
   A XOR B = (A ∨ B) ∧ ¬(A ∧ B)
   Truth table:
   A | B | A XOR B
   ---------------
   F | F |    F
   F | T |    T
   T | F |    T
   T | T |    F

b) NAND (not and):
   A NAND B = ¬(A ∧ B)
   Truth table:
   A | B | A NAND B
   -----------------
   F | F |    T
   F | T |    T
   T | F |    T
   T | T |    F

2.2 Explain the concept of semantic validity in propositional logic.

Solution:
Semantic validity in propositional logic refers to a property of logical formulas that are true under all possible interpretations of their propositional variables. In other words, a semantically valid formula (also called a tautology) is true regardless of the truth values assigned to its variables.

For example, the formula P ∨ ¬P is semantically valid because it is true whether P is true or false. On the other hand, P ∨ Q is not semantically valid because it can be false when both P and Q are false.

Semantic validity is determined by evaluating the truth value of a formula for all possible combinations of truth values for its variables, often using truth tables or more advanced logical reasoning techniques.

## 3. Syntax and Semantics

### Key Concepts:

1. Abstract syntax: The structure of expressions in a language, often represented as trees.
2. Concrete syntax: The textual representation of expressions that adheres to specific formatting rules.
3. Operational semantics: Rules that define how expressions are evaluated or executed.

### Practice Problems:

3.1 Given the following abstract syntax tree, write the corresponding propositional logic expression:
```
     ⇒
   /   \
  ∧     ∨
 / \   / \
P   Q R   S
```

Solution:
The corresponding propositional logic expression is:
(P ∧ Q) → (R ∨ S)

Explanation:
- The root of the tree is an implication (→).
- The left child of the implication is a conjunction (∧) of P and Q.
- The right child of the implication is a disjunction (∨) of R and S.

3.2 Define the operational semantics for the XOR operation in propositional logic.

Solution:
The operational semantics for XOR can be defined as follows:

1. Evaluate the left operand to obtain its truth value.
2. Evaluate the right operand to obtain its truth value.
3. If the truth values are different, the result is True.
4. If the truth values are the same, the result is False.

In formal notation:
eval(A XOR B) = 
  let a = eval(A)
  let b = eval(B)
  if a ≠ b then True else False

This can also be expressed as a truth table:
A | B | A XOR B
---------------
F | F |    F
F | T |    T
T | F |    T
T | T |    F

## 4. Interpretations and Semantic Evaluation

### Key Concepts:

1. Interpretations: Functions that assign truth values to propositional variables.
2. Semantic evaluation: The process of determining the truth value of an expression given an interpretation.

### Practice Problems:

4.1 Given the interpretation I = {P: true, Q: false, R: true}, evaluate:
(P ∧ ¬Q) ∨ (Q → R)

Solution:
Let's evaluate this expression step by step:

1. Evaluate P ∧ ¬Q:
   P is true, ¬Q is true (since Q is false)
   true ∧ true = true

2. Evaluate Q → R:
   Q is false, R is true
   false → true = true (remember, false implies anything is true)

3. Now we have: true ∨ true
   The result is true

Therefore, given the interpretation I, the expression (P ∧ ¬Q) ∨ (Q → R) evaluates to true.

4.2 How many possible interpretations are there for an expression with 4 distinct variables?

Solution:
For each variable, there are 2 possible truth values (true or false).
With 4 distinct variables, we have 2 choices for each variable.
Therefore, the total number of possible interpretations is 2^4 = 16.

We can list them out:
1. {P:F, Q:F, R:F, S:F}
2. {P:F, Q:F, R:F, S:T}
3. {P:F, Q:F, R:T, S:F}
4. {P:F, Q:F, R:T, S:T}
5. {P:F, Q:T, R:F, S:F}
...
16. {P:T, Q:T, R:T, S:T}

This demonstrates why truth tables for expressions with 4 variables have 16 rows.

## 5. Truth Tables and Model Theory

### Key Concepts:

1. Truth tables: Systematic enumerations of all possible interpretations for a propositional logic expression.
2. Satisfiability: A property of expressions that are true for at least one interpretation.
3. Unsatisfiability: A property of expressions that are false for all interpretations.
4. Validity: A property of expressions that are true for all interpretations.
5. Models: Interpretations that make an expression true.
6. Counter-examples: Interpretations that make an expression false.

### Practice Problems:

5.1 Construct a truth table for: (P ∨ Q) → (¬P ∧ Q)

Solution:
P | Q | P ∨ Q | ¬P | ¬P ∧ Q | (P ∨ Q) → (¬P ∧ Q)
---------------------------------------------------
F | F |   F   |  T |    F   |          T
F | T |   T   |  T |    T   |          T
T | F |   T   |  F |    F   |          F
T | T |   T   |  F |    F   |          F

5.2 For the expression (P → Q) ∧ (Q → R) → (P → R):
a) Is it satisfiable?
b) Is it valid?
c) If it's not valid, provide a counter-example.

Solution:
Let's construct a truth table:

P | Q | R | P → Q | Q → R | (P → Q) ∧ (Q → R) | P → R | ((P → Q) ∧ (Q → R)) → (P → R)
----------------------------------------------------------------------------------
F | F | F |   T   |   T   |         T         |   T   |               T
F | F | T |   T   |   T   |         T         |   T   |               T
F | T | F |   T   |   F   |         F         |   T   |               T
F | T | T |   T   |   T   |         T         |   T   |               T
T | F | F |   F   |   T   |         F         |   F   |               T
T | F | T |   F   |   T   |         F         |   T   |               T
T | T | F |   T   |   F   |         F         |   F   |               T
T | T | T |   T   |   T   |         T         |   T   |               T

a) Is it satisfiable? Yes, it's true for all interpretations, so it's satisfiable.
b) Is it valid? Yes, it's true for all interpretations, so it's valid (a tautology).
c) Since it's valid, there are no counter-examples.

This expression is known as the "hypothetical syllogism" and is indeed a fundamental rule of inference in propositional logic.

5.3 How many distinct functions are there from 3 input Boolean values to a final output Boolean value?

Solution:
To determine this, let's think about how many possible input combinations we have and how many ways we can assign outputs to these combinations.

- With 3 input Boolean values, we have 2^3 = 8 possible input combinations.
- For each of these 8 combinations, we can assign either True or False as the output.

This means we're essentially creating a binary number with 8 digits, where each digit represents the output for one of the input combinations.

The number of such 8-digit binary numbers is 2^8 = 256.

Therefore, there are 256 distinct functions from 3 input Boolean values to a final output Boolean value.

To illustrate, here are two examples of such functions:
1. AND function: only true when all inputs are true (00000001 in binary)
2. OR function: true when at least one input is true (11111110 in binary)

## 6. Axioms and Equivalences in Propositional Logic

### Key Concepts:

1. Axioms: Basic principles accepted as true without proof, serving as a starting point for deduction.
2. Logical equivalences: Expressions that always have the same truth value regardless of the truth values of their variables.

### Practice Problems:

6.1 Translate the following axiom into precise English:
P → (Q → P)

Solution:
"If P is true, then P is true regardless of whether Q is true or false."

More verbosely:
"If P is true, then the statement 'if Q is true, then P is true' is always true."

This axiom is sometimes called the "principle of simplification" or "positive paradox." It states that a true statement P remains true even if we add an arbitrary condition Q to it.

6.2 Explain how to use the following equivalence both forwards and backwards:
P ∨ Q ⇔ ¬(¬P ∧ ¬Q)

Solution:
This equivalence is known as one of De Morgan's laws.

Using it forwards:
If we have an expression of the form P ∨ Q, we can replace it with ¬(¬P ∧ ¬Q).
This can be useful when we're trying to express everything in terms of AND and NOT operations, or when we're trying to push NOT operations inwards in an expression.

Example: (A ∨ B) ∧ C can be rewritten as ¬(¬A ∧ ¬B) ∧ C

Using it backwards:
If we have an expression of the form ¬(¬P ∧ ¬Q), we can replace it with P ∨ Q.
This can be useful when we're trying to simplify complex expressions involving multiple negations.

Example: ¬(¬(A ∨ B) ∧ ¬C) can be rewritten as (A ∨ B) ∨ C

In both directions, this equivalence allows us to switch between conjunctive (AND) and disjunctive (OR) forms of expressions, which can be helpful in various logical manipulations and proofs.

## 7. Formalization and Translation

### Key Concepts:

1. Translating between English and propositional logic involves identifying the logical structure of statements and representing them using appropriate logical connectives.
2. Complex implications often involve nested conditional statements and require careful analysis of the logical dependencies between propositions.

### Practice Problems:

7.1 Translate the following English statement into propositional logic:
"If it's not raining or I have an umbrella, then I won't get wet."

Solution:
Let's define our propositions:
R: It's raining
U: I have an umbrella
W: I will get wet

The logical structure of the statement is:
If (not raining OR have umbrella), then (not get wet)

Translated into propositional logic:
(¬R ∨ U) → ¬W

7.2 Translate and explain the meaning of:
X → (X → Z) → (Z → Y) → Y

Solution:
Let's break this down step by step:

1. X →               "If X is true, then..."
2.    (X → Z) →      "...if 'X implies Z' is true, then..."
3.             (Z → Y) → "...if 'Z implies Y' is true, then..."
4.                      Y "...Y is true."

Now, let's explain the meaning:

This proposition states that if X is true, and we know that X implies Z, and we also know that Z implies Y, then Y must be true.

It's a form of nested implication that demonstrates transitive reasoning. Here's how it works:

1. Assume X is true.
2. Given X → Z, we can conclude Z is true.
3. Given Z → Y, and knowing Z is true (from step 2), we can conclude Y is true.

This proposition is actually valid (a tautology) because it represents a valid chain of logical deductions. It's a more complex version of the simple transitive property (If A → B and B → C, then A → C).

## 8. Validity and Proofs (Continued)

8.1 Explain why X → false entails that (not X) is true.

Solution:
The statement X → false entails that (not X) is true because of the definition of implication and the principle of proof by contradiction. Here's a detailed explanation:

1. Recall the truth table for implication (→):
   X | false | X → false
   -------------------
   F |   F   |    T
   T |   F   |    F

2. For X → false to be true, X must be false. This is because:
   - If X were true, then X → false would be false (true implies false is false).
   - The only way for X → false to be true is if X is false.

3. If X is false, then by definition, (not X) is true.

4. This reasoning is closely related to proof by contradiction:
   - If we assume X is true, we derive a contradiction (false).
   - Therefore, X cannot be true, so it must be false.
   - Hence, (not X) must be true.

In logical notation, we can express this as:
(X → false) ⇔ ¬X

This equivalence is a fundamental principle in propositional logic and is often used in proofs and logical reasoning.

8.2 Describe in detail the precise meaning of the or_elim rule.

Solution:
The or_elim rule, also known as "proof by cases" or "disjunction elimination," is a fundamental rule of inference in propositional logic. Here's a detailed explanation of its meaning and usage:

Formal statement of the rule:
If we know:
1. P ∨ Q is true
2. P → R is true
3. Q → R is true

Then we can conclude:
R is true

Precise meaning:
The or_elim rule states that if we have a disjunction (P ∨ Q) and we can prove that a certain conclusion (R) follows from each disjunct separately (P → R and Q → R), then we can conclude that R is true, regardless of which disjunct (P or Q) is actually true.

Usage and reasoning:
1. We start with knowing that either P or Q is true (P ∨ Q).
2. We then show that if P is true, R would follow (P → R).
3. We also show that if Q is true, R would follow (Q → R).
4. Since we've covered all possible cases (P or Q), and R follows in both cases, we can conclude R without needing to know which of P or Q is actually true.

Example:
Suppose we know:
1. "It's raining or snowing" (P ∨ Q)
2. "If it's raining, the ground will be wet" (P → R)
3. "If it's snowing, the ground will be wet" (Q → R)

Using or_elim, we can conclude:
"The ground will be wet" (R)

This rule is powerful because it allows us to reason about situations where we have uncertainty (we don't know which of P or Q is true) but can still draw conclusions based on analyzing all possible cases.

8.3 Use the is_valid checker to determine if the following proposition is valid:
(P ∧ Q) → (P ∨ Q)

Solution:
To determine if this proposition is valid, we need to check if it's true for all possible interpretations of P and Q. Let's construct a truth table:

P | Q | P ∧ Q | P ∨ Q | (P ∧ Q) → (P ∨ Q)
-------------------------------------------
F | F |   F   |   F   |         T
F | T |   F   |   T   |         T
T | F |   F   |   T   |         T
T | T |   T   |   T   |         T

As we can see, the proposition (P ∧ Q) → (P ∨ Q) is true for all possible combinations of P and Q. Therefore, it is valid.

Explanation:
- When P ∧ Q is false (first three rows), the implication is trivially true because false implies anything.
- When P ∧ Q is true (last row), P ∨ Q must also be true, so the implication holds.

Using an is_valid checker in a programming language like Python with a logic library would confirm this result. The checker would essentially perform this truth table evaluation automatically.

## 9. Extended Domains: Arithmetic

### Key Concepts:

1. Syntax of arithmetic expressions: Rules for forming well-formed arithmetic expressions.
2. Semantics of arithmetic expressions: Rules for evaluating arithmetic expressions.
3. Extending propositional logic with arithmetic: Combining logical operators with arithmetic relations.

### Practice Problems:

9.1 Define the syntax for a simple arithmetic expression language that includes addition and multiplication.

Solution:
Here's a simple context-free grammar for arithmetic expressions with addition and multiplication:

```
<expr> ::= <term> | <expr> '+' <term>
<term> ::= <factor> | <term> '*' <factor>
<factor> ::= <number> | '(' <expr> ')'
<number> ::= <digit> | <number> <digit>
<digit> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
```

Explanation:
- An expression (<expr>) is either a term or an expression plus a term.
- A term (<term>) is either a factor or a term multiplied by a factor.
- A factor (<factor>) is either a number or an expression in parentheses.
- A number (<number>) is a sequence of one or more digits.
- A digit (<digit>) is any single digit from 0 to 9.

This grammar allows for expressions like:
- 5 + 3
- (2 + 3) * 4
- 1 + 2 * 3
- ((1 + 2) * 3) + (4 * 5)

The grammar enforces the standard precedence rules (multiplication before addition) through its structure.

9.2 Explain briefly why introducing a domain such as arithmetic requires a notion of validity other than semantic validity.

Solution:
Introducing a domain such as arithmetic to propositional logic requires a notion of validity beyond semantic validity for several important reasons:

1. Infinite domain: Arithmetic deals with an infinite set of numbers. Unlike propositional logic, where we can enumerate all possible truth value assignments, we cannot exhaustively check all possible numeric assignments in arithmetic.

2. Structure and relations: Arithmetic introduces structured objects (numbers) and relations between them (e.g., less than, greater than). These relations have properties that go beyond simple truth values.

3. Quantifiers: To express many arithmetic statements, we need quantifiers (∀ for all, ∃ for exists) which are not part of propositional logic. These quantifiers operate over the infinite domain of numbers.

4. Axiomatization: Arithmetic has its own set of axioms (e.g., Peano axioms) that define the properties of numbers and operations. Validity in arithmetic often involves proving statements from these axioms rather than just checking truth values.

5. Incompleteness: Gödel's Incompleteness Theorems show that for sufficiently powerful formal systems (including arithmetic), there are true statements that cannot be proved within the system. This means that semantic truth and provability (syntactic validity) can diverge.

6. Model theory: In arithmetic, we often care about specific models (e.g., the standard model of natural numbers) rather than all possible interpretations. A statement might be true in the standard model but not in all models of arithmetic.

Given these considerations, we need more sophisticated notions of validity when dealing with arithmetic:

- Proof-theoretic validity: A statement is valid if it can be derived from the axioms of arithmetic using accepted rules of inference.
- Model-theoretic validity: A statement is valid if it's true in all models of a specific theory of arithmetic.
- Arithmetic truth: A statement is true if it holds in the standard model of arithmetic, even if it might not be provable in a given formal system.

These notions allow us to reason about arithmetic statements more effectively, dealing with the complexities introduced by the rich structure and infinite nature of the domain of numbers.

## 10. Extra Credit Topics

### Key Concepts:

1. Deductive proofs: Formal arguments that derive conclusions from premises using rules of inference.
2. Z3: A powerful SMT (Satisfiability Modulo Theories) solver that can be used for model finding and theorem proving.

### Practice Problems:

10.1 Give a deductive proof of the proposition: X ∧ Y → Y ∧ X

Solution:
We'll provide a formal proof using natural deduction:

1. Assume X ∧ Y                    (Assumption)
2. X                               (∧-elimination left from 1)
3. Y                               (∧-elimination right from 1)
4. Y ∧ X                           (∧-introduction from 3 and 2)
5. (X ∧ Y) → (Y ∧ X)               (→-introduction, discharging assumption 1)

Explanation:
1. We start by assuming the antecedent of the implication.
2. From the conjunction X ∧ Y, we can derive X using the left conjunction elimination rule.
3. Similarly, we can derive Y using the right conjunction elimination rule.
4. Now that we have both Y and X separately, we can form the new conjunction Y ∧ X.
5. Finally, we can conclude that if X ∧ Y is true, then Y ∧ X is true, which is exactly what we wanted to prove.

This proof demonstrates the commutativity of conjunction, showing that the order of terms in a conjunction doesn't matter.

10.2 Write a Python program using Z3 to find a model or counterexample for:
(X + 3 < 6) ∧ (Y - 1 < 5)

Solution:
Here's a Python program using Z3 to find a model for the given expression:

```python
from z3 import *

# Create Z3 solver instance
solver = Solver()

# Define variables
X = Int('X')
Y = Int('Y')

# Add constraints
solver.add(X + 3 < 6)
solver.add(Y - 1 < 5)

# Check satisfiability
if solver.check() == sat:
    model = solver.model()
    print("Model found:")
    print(f"X = {model[X]}")
    print(f"Y = {model[Y]}")
else:
    print("No model exists (unsatisfiable)")
```

When you run this program, you should get output similar to:

```
Model found:
X = 2
Y = 3
```

Explanation:
1. We import Z3 and create a solver instance.
2. We define integer variables X and Y.
3. We add the constraints from our expression: (X + 3 < 6) and (Y - 1 < 5).
4. We use the solver to check if these constraints are satisfiable.
5. If a model is found (sat), we print the values of X and Y that satisfy the constraints.

This example demonstrates that the expression is satisfiable, and provides a model (X = 2, Y = 3) that makes both inequalities true:
- 2 + 3 < 6 is true (5 < 6)
- 3 - 1 < 5 is true (2 < 5)

Z3 is powerful because it can handle much more complex constraints, including combinations of arithmetic, boolean logic, and even quantifiers. It's widely used in formal verification, program analysis, and automated theorem proving.