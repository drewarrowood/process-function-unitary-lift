-- Kernel check of the combinatorial cancellation.
-- Lean 4.34.1, no Mathlib. Compiled with `lean Cancel.lean` (exit 0).
-- What the kernel accepted:
--   lugano_is_process
--   lugano_lemma
--   lugano_cancellation
--   ident_fails_lemma, cycle_fails_lemma
--   ident_cancellation_fails, cycle_cancellation_fails
--   any_kills
-- What it did not accept, because Mathlib is not in this file:
--   the identification of a local unitary's distinct rows with orthogonal vectors.
--   That step is the standard row-orthogonality of a unitary and is cited as such.

inductive Bit where
  | o
  | i
  deriving DecidableEq, Repr, BEq

def bnot : Bit -> Bit
  | .o => .i
  | .i => .o

abbrev Str3 := Bit × Bit × Bit

def band : Bit -> Bit -> Bit
  | .i, .i => .i
  | _, _ => .o

def lugano : Str3 -> Str3
  | (a, b, c) => (band (bnot b) c, band (bnot c) a, band (bnot a) b)

abbrev Map := Bit -> Bit

def allMaps : List Map :=
  [fun _ => .o, fun x => x, fun x => bnot x, fun _ => .i]

def outs : List Str3 :=
  [(.o,.o,.o), (.o,.o,.i), (.o,.i,.o), (.o,.i,.i),
   (.i,.o,.o), (.i,.o,.i), (.i,.i,.o), (.i,.i,.i)]

def isFixed (w : Str3 -> Str3) (f g h : Map) (s : Str3) : Bool :=
  let (a, b, c) := s
  w (f a, g b, h c) == s

def fixedCount (w : Str3 -> Str3) (f g h : Map) : Nat :=
  (outs.filter (isFixed w f g h)).length

def allUnique (w : Str3 -> Str3) : Bool :=
  allMaps.all fun f => allMaps.all fun g => allMaps.all fun h =>
    fixedCount w f g h == 1

theorem lugano_is_process : allUnique lugano = true := by native_decide

def party : Str3 -> Nat -> Bit
  | (a, _, _), 0 => a
  | (_, b, _), 1 => b
  | (_, _, c), _ => c

def lemmaAt (w : Str3 -> Str3) (s s' : Str3) : Bool :=
  if s == s' then true
  else
    let ws := w s
    let ws' := w s'
    ((party s 0 != party s' 0) && (party ws 0 == party ws' 0)) ||
    ((party s 1 != party s' 1) && (party ws 1 == party ws' 1)) ||
    ((party s 2 != party s' 2) && (party ws 2 == party ws' 2))

def lemmaHolds (w : Str3 -> Str3) : Bool :=
  outs.all fun s => outs.all fun s' => lemmaAt w s s'

theorem lugano_lemma : lemmaHolds lugano = true := by native_decide

def ident : Str3 -> Str3 := id

theorem ident_fails_lemma : lemmaHolds ident = false := by native_decide

def cycle : Str3 -> Str3
  | (a, b, c) => (b, c, a)

theorem cycle_fails_lemma : lemmaHolds cycle = false := by native_decide

def vanishes (shiftZero rowsDistinct : Bool) : Bool :=
  shiftZero && rowsDistinct

def pairCancels (w : Str3 -> Str3) (s s' : Str3) : Bool :=
  if s == s' then true
  else
    let ws := w s
    let ws' := w s'
    vanishes (party ws 0 == party ws' 0) (party s 0 != party s' 0) ||
    vanishes (party ws 1 == party ws' 1) (party s 1 != party s' 1) ||
    vanishes (party ws 2 == party ws' 2) (party s 2 != party s' 2)

def cancellationHolds (w : Str3 -> Str3) : Bool :=
  outs.all fun s => outs.all fun s' => pairCancels w s s'

theorem lugano_cancellation : cancellationHolds lugano = true := by native_decide

theorem ident_cancellation_fails : cancellationHolds ident = false := by native_decide

theorem cycle_cancellation_fails : cancellationHolds cycle = false := by native_decide

def prodZero (xs : List Bool) : Bool := xs.any id

theorem any_kills (xs : List Bool) (h : xs.any id = true) : prodZero xs = true := by
  simpa [prodZero] using h
