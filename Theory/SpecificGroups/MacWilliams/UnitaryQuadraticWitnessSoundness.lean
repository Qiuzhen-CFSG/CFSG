module

public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticWitness

/-!
# Soundness of the finite unitary witness list

The 2,016 rows are checked through a kernel-reduced two-bit/two-bit XOR encoding.
The encoding is proved equivalent to the coordinate maps, words, square and polar
maps, and both generation products, after which the reduced finite certificate
transfers to `rowChecks`. This certifies the six-generator unitary table arising
from MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/
open scoped BigOperators
namespace MacWilliamsSylow.QuadraticCertificate
open MacWilliamsSylow

private def zxor (a b : Fin 4) : Fin 4 :=
  ⟨Nat.xor a.val b.val, by fin_cases a <;> fin_cases b <;> decide⟩
private def vxor (a b : Fin 16) : Fin 16 :=
  ⟨Nat.xor a.val b.val, by fin_cases a <;> fin_cases b <;> decide⟩
private def zcode (z : BinaryCoordinates 2) : Fin 4 :=
  ⟨(z.toAdd 0).val + 2 * (z.toAdd 1).val, by
    have h0 := ZMod.val_lt (z.toAdd 0); have h1 := ZMod.val_lt (z.toAdd 1); omega⟩
private def vcode (v : BinaryCoordinates 4) : Fin 16 :=
  ⟨(v.toAdd 0).val + 2 * (v.toAdd 1).val + 4 * (v.toAdd 2).val + 8 * (v.toAdd 3).val, by
    have h0 := ZMod.val_lt (v.toAdd 0); have h1 := ZMod.val_lt (v.toAdd 1)
    have h2 := ZMod.val_lt (v.toAdd 2); have h3 := ZMod.val_lt (v.toAdd 3); omega⟩

private theorem zcode_central (n : Fin 4) : zcode (central n) = n := by fin_cases n <;> decide +kernel
private theorem vcode_vector (n : Fin 16) : vcode (vector n) = n := by fin_cases n <;> decide +kernel
private theorem zcode_mul_central (a b : Fin 4) : zcode (central a * central b) = zxor a b := by
  fin_cases a <;> fin_cases b <;> decide +kernel
private theorem vcode_mul_vector (a b : Fin 16) : vcode (vector a * vector b) = vxor a b := by
  fin_cases a <;> fin_cases b <;> decide +kernel
private theorem zcode_one : zcode (1 : BinaryCoordinates 2) = 0 := by decide +kernel
private theorem vcode_one : vcode (1 : BinaryCoordinates 4) = 0 := by decide +kernel

private theorem central_mul_central (a b : Fin 4) : central a * central b = central (zxor a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel
private theorem vector_mul_vector (a b : Fin 16) : vector a * vector b = vector (vxor a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private theorem word_central_eq {n : Nat} (g : Fin n → Fin 4) (w : List (Fin n)) :
    word (fun i => central (g i)) w = central (w.foldr (fun i a => zxor (g i) a) 0) := by
  induction w with
  | nil => simp [word]
  | cons i w ih =>
    change central (g i) * word (fun i => central (g i)) w = _
    rw [ih, central_mul_central]
    simp only [List.foldr]

private theorem word_vector_eq {n : Nat} (g : Fin n → Fin 16) (w : List (Fin n)) :
    word (fun i => vector (g i)) w = vector (w.foldr (fun i a => vxor (g i) a) 0) := by
  induction w with
  | nil => simp [word]
  | cons i w ih =>
    change vector (g i) * word (fun i => vector (g i)) w = _
    rw [ih, vector_mul_vector]
    simp only [List.foldr]

private theorem zcode_prod_central {n : Nat} (g : Fin n → Fin 4) (w : List (Fin n)) :
    zcode (word (fun i => central (g i)) w) = w.foldr (fun i a => zxor (g i) a) 0 := by
  rw [word_central_eq (g := g) (w := w), zcode_central]

private theorem vcode_prod_vector {n : Nat} (g : Fin n → Fin 16) (w : List (Fin n)) :
    vcode (word (fun i => vector (g i)) w) = w.foldr (fun i a => vxor (g i) a) 0 := by
  rw [word_vector_eq (g := g) (w := w), vcode_vector]

private def b4 (x : Fin 16) (i : Fin 4) : Bool := (BitVec.ofFin x).getLsb i

private def squareIndices (x : Fin 16) : List (Fin 10) :=
  (if b4 x 0 then [0] else []) ++
  (if b4 x 1 then [1] else []) ++
  (if b4 x 2 then [2] else []) ++
  (if b4 x 3 then [3] else []) ++
  (if b4 x 1 && b4 x 0 then [4] else []) ++
  (if b4 x 2 && b4 x 0 then [5] else []) ++
  (if b4 x 2 && b4 x 1 then [6] else []) ++
  (if b4 x 3 && b4 x 0 then [7] else []) ++
  (if b4 x 3 && b4 x 1 then [8] else []) ++
  (if b4 x 3 && b4 x 2 then [9] else [])

private def qcode (c : Fin 1048576) (x : Fin 16) : Fin 4 :=
  (squareIndices x).foldr (fun i a => zxor (digit c i) a) 0

set_option maxHeartbeats 2000000000 in
private theorem square_word (c : Fin 1048576) (x : Fin 16) :
    coordinateSquare (coefficients c) (vector x) =
      word (fun i => central (digit c i)) (squareIndices x) := by
  fin_cases x <;> simp [coordinateSquare, coefficients, squareIndices, b4, word, vector, central] <;> ac_rfl

set_option maxHeartbeats 2000000000 in
private theorem zcode_square (c : Fin 1048576) (x : Fin 16) :
    zcode (coordinateSquare (coefficients c) (vector x)) = qcode c x := by
  rw [square_word]
  simpa [qcode] using (zcode_prod_central (fun i => digit c i) (squareIndices x))



private def gcode (r : UnitaryWitness) : Fin 6 → Fin 16 :=
  ![r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, 0, 0]
private def hcode (r : UnitaryWitness) : Fin 6 → Fin 4 :=
  ![0, 0, 0, 0, r.2.2.2.2.2.1, r.2.2.2.2.2.2]
private theorem quotient_code (r : UnitaryWitness) (i : Fin 6) :
    quotientGenerators r i = vector (gcode r i) := by
  fin_cases i <;> simp [quotientGenerators, gcode, vector_zero]
private theorem central_code (r : UnitaryWitness) (i : Fin 6) :
    centralGenerators r i = central (hcode r i) := by
  fin_cases i <;> simp [centralGenerators, hcode, central_zero]

private theorem square_eq_central (r : UnitaryWitness) (x : Fin 16) :
    coordinateSquare (coefficients r.1) (vector x) = central (qcode r.1 x) := by
  rw [square_word, word_central_eq]
  rfl

private def pcode (c : Fin 1048576) (x y : Fin 16) : Fin 4 :=
  zxor (zxor (qcode c (vxor x y)) (qcode c x)) (qcode c y)
private theorem polar_eq_central (r : UnitaryWitness) (x y : Fin 16) :
    coordinatePolar (coefficients r.1) (vector x) (vector y) = central (pcode r.1 x y) := by
  rw [coordinatePolar, vector_mul_vector, square_eq_central, square_eq_central,
    square_eq_central, central_mul_central, central_mul_central]
  rfl

private theorem square_check (r : UnitaryWitness)
    (h : ∀ i : Fin 6, qcode r.1 (gcode r i) =
      (unitaryTable.square i).foldr (fun j a => zxor (hcode r j) a) 0) :
    ∀ i, coordinateSquare (coefficients r.1) (quotientGenerators r i) =
      word (centralGenerators r) (unitaryTable.square i) := by
  intro i
  rw [quotient_code, square_eq_central]
  have hgen : centralGenerators r = (fun k => central (hcode r k)) := by
    funext k; exact central_code r k
  rw [hgen, word_central_eq]
  exact congrArg central (h i)

private theorem polar_check (r : UnitaryWitness)
    (h : ∀ i j : Fin 6, i < j → pcode r.1 (gcode r j) (gcode r i) =
      (unitaryTable.commutator j i).foldr (fun k a => zxor (hcode r k) a) 0) :
    ∀ i j, i < j →
      coordinatePolar (coefficients r.1) (quotientGenerators r j) (quotientGenerators r i) =
      word (centralGenerators r) (unitaryTable.commutator j i) := by
  intro i j hij
  rw [quotient_code, quotient_code, polar_eq_central]
  have hgen : centralGenerators r = (fun k => central (hcode r k)) := by
    funext k; exact central_code r k
  rw [hgen, word_central_eq]
  exact congrArg central (h i j hij)

private def gprod4 (r : UnitaryWitness) (t : Fin 16) : Fin 16 :=
  vxor (if b4 t 0 then gcode r 0 else 0)
    (vxor (if b4 t 1 then gcode r 1 else 0)
      (vxor (if b4 t 2 then gcode r 2 else 0)
        (if b4 t 3 then gcode r 3 else 0)))
private def b2 (t : Fin 4) (i : Fin 2) : Bool := (BitVec.ofFin t).getLsb i
private def hprod2 (r : UnitaryWitness) (t : Fin 4) : Fin 4 :=
  zxor (if b2 t 0 then hcode r 4 else 0)
    (if b2 t 1 then hcode r 5 else 0)

private theorem source_prod (r : UnitaryWitness) (t : Fin 16) :
    (∏ i : Fin 4, if (BitVec.ofFin t).getLsb i then
      quotientGenerators r ⟨i.val, by omega⟩ else 1) = vector (gprod4 r t) := by
  fin_cases t <;>
    simp [Fin.prod_univ_succ, quotientGenerators, gcode, gprod4, b4,
      vector_zero, vector_mul_vector, vxor]

private theorem central_prod (r : UnitaryWitness) (t : Fin 4) :
    (∏ i : Fin 2, if (BitVec.ofFin t).getLsb i then
      centralGenerators r ⟨i.val + 4, by omega⟩ else 1) = central (hprod2 r t) := by
  fin_cases t <;>
    simp [Fin.prod_univ_succ, centralGenerators, hcode, hprod2, b2,
      central_zero, central_mul_central, zxor]



private abbrev fastProp (r : UnitaryWitness) : Prop :=
  (∀ i : Fin 6, qcode r.1 (gcode r i) =
      (unitaryTable.square i).foldr (fun j a => zxor (hcode r j) a) 0) ∧
  (∀ i j : Fin 6, i < j → pcode r.1 (gcode r j) (gcode r i) =
      (unitaryTable.commutator j i).foldr (fun k a => zxor (hcode r k) a) 0) ∧
  (∀ n : Fin 16, ∃ t : Fin 16, n = gprod4 r t) ∧
  (∀ n : Fin 4, ∃ t : Fin 4, n = hprod2 r t)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000000 in
private theorem fast_all : (unitaryWitnesses.all (fun r => decide (fastProp r))) = true := by
  decide +kernel


private theorem rowChecks_of_fast (r : UnitaryWitness) (h : fastProp r) : rowChecks r = true := by
  apply decide_eq_true
  obtain ⟨hs, hp, hv, hz⟩ := h
  refine ⟨square_check r hs, polar_check r hp, ?_, ?_⟩
  · intro n
    obtain ⟨t, ht⟩ := hv n
    refine ⟨t, ?_⟩
    rw [source_prod]
    exact congrArg vector ht
  · intro n
    obtain ⟨t, ht⟩ := hz n
    refine ⟨t, ?_⟩
    rw [central_prod]
    exact congrArg central ht

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000000 in
public theorem witnesses_sound : (unitaryWitnesses.all rowChecks) = true := by
  apply List.all_eq_true.mpr
  intro r hr
  apply rowChecks_of_fast
  apply of_decide_eq_true
  exact List.all_eq_true.mp fast_all r hr

end MacWilliamsSylow.QuadraticCertificate
