structure ArithVar : Type :=
  mk :: (index: Nat)
deriving Repr

inductive ArithBinOp : Type
| add
| sub
| mul

inductive ArithUnOp : Type
| neg

inductive ArithExpr : Type
| lit_expr (from_ : Nat) : ArithExpr
| var_expr (from_var : ArithVar)
| un_op_expr (op : ArithUnOp) (e : ArithExpr)
| bin_op_expr (op : ArithBinOp) (e1 e2 : ArithExpr)

notation " { " v " } " => ArithExpr.var_expr v
notation " [ " n " ] " => ArithExpr.lit_expr n
notation:max "++" n => ArithExpr.UnOp ArithUnOp.inc n
notation:max "--" n => ArithExpr.UnOp ArithUnOp.dec n
notation e1 "+" e2 => ArithExpr.bin_op_expr ArithBinOp.add e1 e2
notation e1 "-" e2 => ArithExpr.bin_op_expr ArithBinOp.sub e1 e2
notation e1 "*" e2 => ArithExpr.bin_op_expr ArithBinOp.mul e1 e2

def arithEval: (ArithExpr → Nat) → Nat
| lit_expr (fromNat: Nat), i ⇒ fromNat
| var_expr (fromVar: ArithVar), i ⇒ i fromVar
| un_op_expr (op: ArithUnOp) (e: ArithExpr), i ⇒
  match op with
  | ArithUnOp.neg ⇒ - arithEval e i
| bin_op_expr (op: ArithBinOp) (e1 e2: ArithExpr), i ⇒
  match op with
  | ArithBinOp.add ⇒ arithEval e1 i + arithEval e2 i
  | ArithBinOp.sub ⇒ arithEval e1 i - arithEval e2 i
  | ArithBinOp.mul ⇒ arithEval e1 i * arithEval e2 i
def N:= { ⟨ 3 ⟩ }
def M:= { ⟨ 4 ⟩ }
def P:= { ⟨ 0 ⟩ }

#reduce N + M
#check (N + M) * P - (ArithExpr.lit_expr 1)

def v₀ := ArithVar.mk 0
def v₁ := ArithVar.mk 1
def v₂ := ArithVar.mk 2
def X := (ArithExpr.var_expr v₀)
def Y := (ArithExpr.var_expr v₁)
def Z := (ArithExpr.var_expr v₂)
#check ArithExpr.bin_op_expr ArithBinOp.add X Y
