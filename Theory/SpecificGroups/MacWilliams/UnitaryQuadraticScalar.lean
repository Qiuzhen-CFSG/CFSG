module

public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticValidity

/-!
# Scalar truth tables for the balanced binary quadratic certificate

Projecting the binary two-space onto either coordinate produces a scalar
quadratic polynomial with ten binary coefficients. Its sixteen values are the
XOR of the ten monomial truth tables below. The projection is proved to agree
with the existing coordinate polynomial, and pairing the projections recovers
the original packed code. Balanced nonzero fibres give each scalar table weight
ten; anisotropy says their union contains exactly the fifteen nonzero vectors.

This reduces the exhaustive check from 4^10 codes to pairs of scalar tables.
Source: MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace MacWilliamsSylow.QuadraticCertificate

@[expose] public def scalarCode (c : QuadraticCoefficients) (j : Fin 2) : Fin 1024 :=
  ((BitVec.ofBoolListLE (List.ofFn fun i : Fin 10 => decide ((c i).toAdd j = 1))).cast
    (by simp) : BitVec 10).toFin

@[expose] public def scalarTable (a : Fin 1024) : BitVec 16 :=
  (if (BitVec.ofFin (w := 10) a).getLsbD 0 then 43690#16 else 0#16) ^^^
  (if (BitVec.ofFin (w := 10) a).getLsbD 1 then 52428#16 else 0#16) ^^^
  (if (BitVec.ofFin (w := 10) a).getLsbD 2 then 61680#16 else 0#16) ^^^
  (if (BitVec.ofFin (w := 10) a).getLsbD 3 then 65280#16 else 0#16) ^^^
  (if (BitVec.ofFin (w := 10) a).getLsbD 4 then 34952#16 else 0#16) ^^^
  (if (BitVec.ofFin (w := 10) a).getLsbD 5 then 41120#16 else 0#16) ^^^
  (if (BitVec.ofFin (w := 10) a).getLsbD 6 then 49344#16 else 0#16) ^^^
  (if (BitVec.ofFin (w := 10) a).getLsbD 7 then 43520#16 else 0#16) ^^^
  (if (BitVec.ofFin (w := 10) a).getLsbD 8 then 52224#16 else 0#16) ^^^
  (if (BitVec.ofFin (w := 10) a).getLsbD 9 then 61440#16 else 0#16)

public theorem scalarCode_bit (c : QuadraticCoefficients) (j : Fin 2) (i : Fin 10) :
    (scalarCode c j).val.testBit i.val =
      decide ((c i).toAdd j = 1) := by
  change (((BitVec.ofBoolListLE (List.ofFn fun i : Fin 10 =>
    decide ((c i).toAdd j = 1))).cast (by simp) : BitVec 10)).getLsbD i.val = _
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  fin_cases i <;> rfl

private def bitValue (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem bitValue_xor (a b : Bool) : bitValue (a ^^ b) = bitValue a + bitValue b :=
  by decide +revert +kernel

private theorem bitValue_decide (a : ZMod 2) : bitValue (decide (a = 1)) = a :=
  by decide +revert +kernel

private theorem selected_bit (b : Bool) (v : BitVec 16) (i : Nat) :
    (if b then v else 0#16).getLsbD i = (b && v.getLsbD i) := by
  cases b <;> simp

private theorem scalar_value (c : QuadraticCoefficients) (j : Fin 2) (x : Fin 16) :
    (coordinateSquare c (vector x)).toAdd j =
      bitValue ((scalarTable (scalarCode c j)).getLsbD x.val) := by
  have h0 : (scalarCode c j).val.testBit 0 = decide ((c 0).toAdd j = 1) :=
    scalarCode_bit c j 0
  have h1 : (scalarCode c j).val.testBit 1 = decide ((c 1).toAdd j = 1) :=
    scalarCode_bit c j 1
  have h2 : (scalarCode c j).val.testBit 2 = decide ((c 2).toAdd j = 1) :=
    scalarCode_bit c j 2
  have h3 : (scalarCode c j).val.testBit 3 = decide ((c 3).toAdd j = 1) :=
    scalarCode_bit c j 3
  have h4 : (scalarCode c j).val.testBit 4 = decide ((c 4).toAdd j = 1) :=
    scalarCode_bit c j 4
  have h5 : (scalarCode c j).val.testBit 5 = decide ((c 5).toAdd j = 1) :=
    scalarCode_bit c j 5
  have h6 : (scalarCode c j).val.testBit 6 = decide ((c 6).toAdd j = 1) :=
    scalarCode_bit c j 6
  have h7 : (scalarCode c j).val.testBit 7 = decide ((c 7).toAdd j = 1) :=
    scalarCode_bit c j 7
  have h8 : (scalarCode c j).val.testBit 8 = decide ((c 8).toAdd j = 1) :=
    scalarCode_bit c j 8
  have h9 : (scalarCode c j).val.testBit 9 = decide ((c 9).toAdd j = 1) :=
    scalarCode_bit c j 9
  fin_cases x <;>
    simp only [coordinateSquare] <;>
    dsimp [vector] <;>
    simp only [scalarTable, BitVec.getLsbD_xor, selected_bit] <;>
    dsimp <;>
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      Bool.and_true, Bool.and_false, Bool.false_xor, Bool.xor_false,
      bitValue_xor, bitValue_decide, show bitValue false = 0 from rfl,
      add_zero, zero_add]

public theorem scalar_eval (c : QuadraticCoefficients) (j : Fin 2) (x : Fin 16) :
    decide ((coordinateSquare c (vector x)).toAdd j = 1) =
      (scalarTable (scalarCode c j)).getLsbD x.val := by
  rw [scalar_value]
  exact (show ∀ b : Bool, decide (bitValue b = 1) = b by decide +kernel) _

@[expose] public def scalarWeight (a : Fin 1024) : Nat :=
  (Finset.univ.filter fun x : Fin 16 => (scalarTable a).getLsbD x.val = true).card

@[expose] public def pairedCode (a b : Fin 1024) : Fin 1048576 :=
  pack fun i => if a.val.testBit i.val then (if b.val.testBit i.val then 3 else 1)
    else (if b.val.testBit i.val then 2 else 0)

public theorem coefficients_pairedCode (c : QuadraticCoefficients) :
    coefficients (pairedCode (scalarCode c 0) (scalarCode c 1)) = c := by
  funext i
  simp only [coefficients, pairedCode, digit_pack, scalarCode_bit]
  exact (show ∀ z : BinaryCoordinates 2,
    central (if decide (z.toAdd 0 = 1) then (if decide (z.toAdd 1 = 1) then 3 else 1)
      else (if decide (z.toAdd 1 = 1) then 2 else 0)) = z by decide +kernel) (c i)

private theorem pack_digits (n : Fin 1048576) : pack (digit n) = n := by
  apply Fin.ext
  have hn := n.isLt
  norm_num [pack, digit, Fin.sum_univ_succ, Fin.succ]
  omega

public theorem pairedCode_scalarCode (n : Fin 1048576) :
    pairedCode (scalarCode (coefficients n) 0) (scalarCode (coefficients n) 1) = n := by
  have he := coefficients_pairedCode (coefficients n)
  have hd : ∀ i, digit (pairedCode (scalarCode (coefficients n) 0)
      (scalarCode (coefficients n) 1)) i = digit n i := fun i =>
    central_bijective.1 (congrFun he i)
  have hp := congrArg pack (funext hd)
  simpa only [pack_digits] using hp

public theorem scalarWeight_of_balanced (n : Fin 1048576) (hb : balanced n = true)
    (j : Fin 2) : scalarWeight (scalarCode (coefficients n) j) = 10 := by
  have hb' := of_decide_eq_true hb
  let f := fun x => coordinateSquare (coefficients n) (vector x)
  let u : Fin 4 := if j = 0 then 1 else 2
  have hu : u ≠ 0 := by dsimp [u]; split <;> decide
  have hu3 : u ≠ 3 := by dsimp [u]; split <;> decide
  have hf : ∀ z : BinaryCoordinates 2, z.toAdd j = 1 ↔
      z = central u ∨ z = central 3 := by
    dsimp [u]
    exact (show ∀ (j : Fin 2) (z : BinaryCoordinates 2), z.toAdd j = 1 ↔
      z = central (if j = 0 then 1 else 2) ∨ z = central 3 by decide +kernel) j
  have hs : (Finset.univ.filter fun x : Fin 16 => (f x).toAdd j = 1) =
      (Finset.univ.filter fun x => f x = central u) ∪
        (Finset.univ.filter fun x => f x = central 3) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hf]
  have hd : Disjoint (Finset.univ.filter fun x : Fin 16 => f x = central u)
      (Finset.univ.filter fun x => f x = central 3) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hu3 (central_bijective.1 ((Finset.mem_filter.mp hx).2.symm.trans
      (Finset.mem_filter.mp hy).2))
  simp only [scalarWeight, ← scalar_eval, decide_eq_true_eq]
  change (Finset.univ.filter fun x : Fin 16 => (f x).toAdd j = 1).card = 10
  rw [hs, Finset.card_union_of_disjoint hd, hb' u hu, hb' 3 (by decide)]

public theorem scalar_union_of_anisotropic (n : Fin 1048576) (ha : anisotropic n = true) :
    (scalarTable (scalarCode (coefficients n) 0) |||
      scalarTable (scalarCode (coefficients n) 1)) = 65534#16 := by
  have ha' := of_decide_eq_true ha
  have hnonzero : ∀ z : BinaryCoordinates 2,
      (decide (z.toAdd 0 = 1) || decide (z.toAdd 1 = 1)) = decide (z ≠ 1) :=
    by decide +kernel
  have hmask : ∀ x : Fin 16, (65534#16).getLsbD x.val = decide (x ≠ 0) :=
    by decide +kernel
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let x : Fin 16 := ⟨i, hi⟩
  change _ = (65534#16).getLsbD x.val
  rw [BitVec.getLsbD_or, ← scalar_eval (coefficients n) 0 x,
    ← scalar_eval (coefficients n) 1 x, hnonzero, hmask]
  by_cases hx : x = 0
  · rw [hx]
    have hzero : coordinateSquare (coefficients n) (vector 0) = 1 := by
      rw [vector_zero]
      simp [coordinateSquare]
    simp only [hzero, ne_eq, not_true_eq_false, decide_false]
  · have hq : coordinateSquare (coefficients n) (vector x) ≠ 1 := fun hq => hx (ha' x hq)
    exact (decide_eq_true hq).trans (decide_eq_true hx).symm

end MacWilliamsSylow.QuadraticCertificate

