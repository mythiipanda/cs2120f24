from z3 import *

X = Int('X')
Y = Int('Y')
s = Solver()
s.add(X + 3 < 6, Y - 1 < 5)

if s.check() == sat:
    print(s.model())
else:
    print("No solution")
