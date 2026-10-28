module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.ReferenceBound.Frames.Reflection
/-!
# Integral action certificates in the Leech lattice basis

The existing reciprocal-basis formula is evaluated over the integers, using
array access checked against the published dual basis.
A residue modulo sixteen proves the quotient by eight modulo two, simultaneously
for an action and its global negative. All scalar computations remain kernel
checked; no assumption of candidate validity or coverage is used.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
-/

open Atlas.Codes
open scoped BigOperators Matrix
@[expose] public section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound
namespace FrameCheck

def sum24 {α : Type*} [AddMonoid α] (f : Fin 24 → α) : α :=
  f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 + (f 22 + (f 23 + 0)))))))))))))))))))))))

theorem sum24_eq {α : Type*} [AddCommMonoid α] (f : Fin 24 → α) :
    (∑ i, f i) = sum24 f := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rfl

def dualArray : Vector (Vector ℤ 24) 24 := ⟨#[⟨#[8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[-4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[-4,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[-4,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[-4,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[-4,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[-4,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[10,-2,-2,-2,-2,-2,-2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[-4,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[-4,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[-4,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[10,-2,-2,-2,0,0,0,0,-2,-2,-2,2,0,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[-4,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[10,-2,0,0,-2,-2,0,0,-2,-2,0,0,-2,2,0,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[12,-2,-2,0,-2,0,-2,0,0,-2,-2,0,-2,0,2,0,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[12,-2,0,-2,0,-2,-2,0,-2,0,-2,0,-2,0,0,2,0,0,0,0,0,0,0,0], rfl⟩,
⟨#[-4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0], rfl⟩,
⟨#[10,0,-2,0,-2,0,-2,0,-2,-2,0,0,0,0,0,0,-2,2,0,0,0,0,0,0], rfl⟩,
⟨#[10,0,0,-2,-2,-2,0,0,-2,0,-2,0,0,0,0,0,-2,0,2,0,0,0,0,0], rfl⟩,
⟨#[10,-2,0,0,0,-2,-2,0,0,-2,-2,0,0,0,0,0,-2,0,0,2,0,0,0,0], rfl⟩,
⟨#[12,-2,-2,-2,-2,0,0,0,-2,0,0,0,-2,0,0,0,-2,0,0,0,2,0,0,0], rfl⟩,
⟨#[12,0,0,-2,-2,-2,-2,0,0,-2,0,0,-2,0,0,0,-2,0,0,0,0,2,0,0], rfl⟩,
⟨#[12,0,-2,0,0,-2,0,0,-2,-2,-2,0,-2,0,0,0,-2,0,0,0,0,0,2,0], rfl⟩,
⟨#[-59,7,5,5,7,7,5,-1,7,7,5,-1,5,-1,-1,-1,5,-1,-1,-1,-1,-1,-1,1], rfl⟩], rfl⟩

set_option Elab.async false in
theorem dualArray_check : all24 (fun i => all24 (fun j =>
    decide (StandardCoordinates.dualMatrix i j = (dualArray.get i).get j))) = true := by
  decide +kernel

theorem dualArray_eq : StandardCoordinates.dualMatrix = (fun i j => (dualArray.get i).get j) := by
  funext i j
  exact of_decide_eq_true ((all24_iff _).mp ((all24_iff _).mp dualArray_check i) j)

def numerator (s : ℕ) (p : Vector (Fin 24) 24) (i j : Fin 24) : ℤ :=
  sum24 fun k => (dualArray.get i).get k *
    (if s.testBit k.val then -(basisArray.get (p.get k)).get j
      else (basisArray.get (p.get k)).get j)

theorem signed_bit (b : Bool) (z : ℤ) :
    (if bitVal b = 0 then z else -z) = if b then -z else z := by
  cases b <;> norm_num [bitVal]

theorem signed_complement (b : Bool) (z : ℤ) :
    (if 1 - bitVal b = 0 then z else -z) = -(if b then -z else z) := by
  cases b <;> norm_num [bitVal]

theorem raw_numerator (s : ℕ) (p : Vector (Fin 24) 24) :
    rawMatrix (maskBit s) p.get = fun i j => ((numerator s p i j / 8 : ℤ) : Bit) := by
  funext i j
  unfold rawMatrix numerator
  change (((∑ k : Fin 24, StandardCoordinates.dualMatrix i k *
    (if bitVal (s.testBit k.val) = 0 then StandardCoordinates.basisMatrix (p.get k) j
      else -StandardCoordinates.basisMatrix (p.get k) j)) / 8 : ℤ) : Bit) = _
  simp_rw [signed_bit]
  rw [basisArray_eq, dualArray_eq, sum24_eq]

theorem raw_complement_numerator (s : ℕ) (p : Vector (Fin 24) 24) :
    rawMatrix (fun k => 1 - maskBit s k) p.get =
      fun i j => (((-numerator s p i j) / 8 : ℤ) : Bit) := by
  funext i j
  unfold rawMatrix numerator
  change (((∑ k : Fin 24, StandardCoordinates.dualMatrix i k *
    (if 1 - bitVal (s.testBit k.val) = 0 then StandardCoordinates.basisMatrix (p.get k) j
      else -StandardCoordinates.basisMatrix (p.get k) j)) / 8 : ℤ) : Bit) = _
  simp_rw [signed_complement, mul_neg]
  rw [Finset.sum_neg_distrib, basisArray_eq, dualArray_eq, sum24_eq]

def actionCheck (s : ℕ) (p : Vector (Fin 24) 24) (rows : Vector ℕ 24) : Bool :=
  all24 fun i => all24 fun j =>
    numerator s p i j % 16 == if (rows.get i).testBit j.val then 8 else 0

theorem action_of_check (s : ℕ) (p : Vector (Fin 24) 24) (rows : Vector ℕ 24)
    (h : actionCheck s p rows = true) :
    rawMatrix (maskBit s) p.get = rowMatrix rows ∧
      rawMatrix (fun k => 1 - maskBit s k) p.get = rowMatrix rows := by
  have hc (i j : Fin 24) : numerator s p i j % 16 =
      if (rows.get i).testBit j.val then 8 else 0 := by
    exact beq_iff_eq.mp ((all24_iff _).mp ((all24_iff _).mp h i) j)
  rw [raw_numerator, raw_complement_numerator]
  constructor <;> apply Matrix.ext <;> intro i j
  · exact (mod16_to_bit _ _ (hc i j)).1
  · exact (mod16_to_bit _ _ (hc i j)).2

end FrameCheck
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound
