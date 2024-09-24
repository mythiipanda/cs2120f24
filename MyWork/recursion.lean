def baseSum := 0
def stepSum : Nat → Nat → Nat
| n', sumn' => (n' + 1) + sumn'
def facBase := 1
def stepFac (n' facn' : Nat) := (n' + 1) * facn'
#eval stepFac 0 1
#eval stepFac 1 1
#eval stepFac 2 2
#eval stepFac 3 6
#eval stepFac 4 24
#eval stepFac 5 120
def fac : Nat → Nat := Nat.rec facBase stepFac
def sum : Nat → Nat := Nat.rec baseSum stepSum
#eval sum 0
#eval sum 1
#eval sum 5
#eval fac 10
-- Induction principles, only works for NATURAL numbers
def sum_up : Nat → Nat
| Nat.zero => 0
| (Nat.succ n') => Nat.succ n' + sum_up n'
def fac_up : Nat → Nat
| 0 => 1
| Nat.succ n' => Nat.succ n' * fac_up n'
#eval sum_up 100
