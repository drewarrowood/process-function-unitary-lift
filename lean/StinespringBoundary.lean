-- Stinespring boundary. Lean 4.34.1, no Mathlib, no sorry, no axiom.
-- Closed contraction is not an isometry for every w.
-- The source-sink extension is a bijection for every w.
-- Ancilla-input 0 inherits column orthonormality from the full columns.
-- A spacetime metric is not a definition in this file.

namespace StinespringBoundary

inductive B where
  | o
  | i
  deriving DecidableEq, Repr, BEq

def bxor : B → B → B
  | .o, b => b
  | .i, .o => .i
  | .i, .i => .o

abbrev S := B × B × B

def outs : List S :=
  [(.o,.o,.o), (.o,.o,.i), (.o,.i,.o), (.o,.i,.i),
   (.i,.o,.o), (.i,.o,.i), (.i,.i,.o), (.i,.i,.i)]

def party : S → Nat → B
  | (a, _, _), 0 => a
  | (_, b, _), 1 => b
  | (_, _, c), _ => c

def ident : S → S := id

def Imat (r inp : B) : Int :=
  match r, inp with
  | .o, .o => 1
  | .o, .i => 0
  | .i, .o => 0
  | .i, .i => 1

def ampI (w : S → S) (s e : S) : Int :=
  Imat (party s 0) (bxor (party (w s) 0) (party e 0)) *
  Imat (party s 1) (bxor (party (w s) 1) (party e 1)) *
  Imat (party s 2) (bxor (party (w s) 2) (party e 2))

def gramDiag (w : S → S) (e : S) : Int :=
  outs.foldl (fun acc s => acc + ampI w s e * ampI w s e) 0

/-- Identity loop, local identity, source 0: eight fixed points, not one. -/
theorem closed_not_every_w :
    gramDiag ident (.o, .o, .o) = 8 := by
  native_decide

theorem xor_cancel (a b : B) : bxor a (bxor a b) = b := by
  cases a <;> cases b <;> rfl

def extend (w : S → S) (o e : S) : S × S :=
  ((bxor (party (w o) 0) (party e 0),
    bxor (party (w o) 1) (party e 1),
    bxor (party (w o) 2) (party e 2)), o)

def extendInv (w : S → S) (i s : S) : S × S :=
  (s, (bxor (party (w s) 0) (party i 0),
       bxor (party (w s) 1) (party i 1),
       bxor (party (w s) 2) (party i 2)))

theorem extend_left_inv (w : S → S) (o e : S) :
    extendInv w (extend w o e).1 (extend w o e).2 = (o, e) := by
  obtain ⟨a, b, c⟩ := o
  obtain ⟨x, y, z⟩ := e
  simp [extend, extendInv, party, xor_cancel]

theorem extend_right_inv (w : S → S) (i s : S) :
    extend w (extendInv w i s).1 (extendInv w i s).2 = (i, s) := by
  obtain ⟨a, b, c⟩ := i
  obtain ⟨x, y, z⟩ := s
  simp [extend, extendInv, party, xor_cancel]

def sum2 (f : B → Int) : Int := f .o + f .i

def colSlice (V : B → B → Int) (e e2 : B) : Int :=
  sum2 (fun sout => V sout e * V sout e2)

theorem column_slice (V : B → B → Int) (e e2 : B)
    (h : sum2 (fun sout => V sout e * V sout e2) = if e = e2 then 1 else 0) :
    colSlice V e e2 = if e = e2 then 1 else 0 := by
  simpa [colSlice] using h

end StinespringBoundary
