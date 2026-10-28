module
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Representation
public import Theory.SpecificGroups.Triality.LeviRankOneMatrices.Entries

/-!
# Pinning the characteristic-two D4 rank-one representation

The integral degree-one matrices reduce to the natural root-string operators
and the Cartan incidence entries. Their degree-two terms connect the two roots
±α, and their degree-three terms vanish. Comparing these polynomial entries with
the explicit SL₂ action proves both transvection formulas on the full lattice.
The finite coefficient checks take place over ℤ and are checked by the kernel;
only their specialization uses characteristic two.

Source: the common-representation, common-lattice argument in GLS3 §2.6,
Proposition 2.6.2 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup RootPairing.IntegralGeckConstruction
namespace Triality.Standard.Parabolics.RankOneMatrices
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

/-- Join the block coordinates into the Cartan and ordered-root coordinates. -/
def blockToFlat : BlockIndex ≃ FlatIndex :=
  (Equiv.sumAssoc _ _ _).trans
    (Equiv.sumCongr (Equiv.refl _) rootBlockEnumeration)

lemma flatEquiv_blockToFlat (i : Fin 4) (r : BlockIndex) :
    flatEquiv i (blockToFlat r) = latticeEquiv i r := by
  rcases r with (r | r) | r <;> rfl

variable {F : Type*} [CommRing F] [CharP F 2]

omit [CharP F 2] in
lemma positiveMatrix_entry (i : Fin 4) (t : F) (r s : FlatIndex) :
    positiveMatrix (typeDRootPairing_baseEquiv 2 i) t (flatEquiv i r) (flatEquiv i s) =
      (if r = s then 1 else 0) + t * (eData i r s : F) +
        t ^ 2 * (if r = .inr 0 ∧ s = .inr 1 then 1 else 0) := by
  rw [positiveMatrix_formula]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    eDividedPower_one, eMatrix_entry, eTwo_entry, eThree_entry, Matrix.one_apply,
    (flatEquiv i).injective.eq_iff, smul_eq_mul, map_zero, mul_zero, add_zero]
  split_ifs <;> simp

omit [CharP F 2] in
lemma negativeMatrix_entry (i : Fin 4) (t : F) (r s : FlatIndex) :
    negativeMatrix (typeDRootPairing_baseEquiv 2 i) t (flatEquiv i r) (flatEquiv i s) =
      (if r = s then 1 else 0) + t * (fData i r s : F) +
        t ^ 2 * (if r = .inr 1 ∧ s = .inr 0 then 1 else 0) := by
  rw [negativeMatrix_formula]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    fDividedPower_one, fMatrix_entry, fTwo_entry, fThree_entry, Matrix.one_apply,
    (flatEquiv i).injective.eq_iff, smul_eq_mul, map_zero, mul_zero, add_zero]
  split_ifs <;> simp

def positiveCoefficient (i : Fin 4) : Matrix BlockIndex BlockIndex ℤ
  | .inl (.inl k), .inl (.inr s) => if k = i ∧ s = 1 then 1 else 0
  | .inl (.inr r), .inl (.inl j) => if r = 0 ∧ adjacent i j then 1 else 0
  | .inr (.inl (r, k)), .inr (.inl (s, l)) =>
      if r = 0 ∧ s = 1 ∧ k = l then 1 else 0
  | _, _ => 0

def negativeCoefficient (i : Fin 4) : Matrix BlockIndex BlockIndex ℤ
  | .inl (.inl k), .inl (.inr s) => if k = i ∧ s = 0 then 1 else 0
  | .inl (.inr r), .inl (.inl j) => if r = 1 ∧ adjacent i j then 1 else 0
  | .inr (.inl (r, k)), .inr (.inl (s, l)) =>
      if r = 1 ∧ s = 0 ∧ k = l then 1 else 0
  | _, _ => 0

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma eData_mod_two (i : Fin 4) (r s : BlockIndex) :
    eData i (blockToFlat r) (blockToFlat s) % 2 = positiveCoefficient i r s := by
  revert i r s
  simp only [Sum.forall, Prod.forall]
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma fData_mod_two (i : Fin 4) (r s : BlockIndex) :
    fData i (blockToFlat r) (blockToFlat s) % 2 = negativeCoefficient i r s := by
  revert i r s
  simp only [Sum.forall, Prod.forall]
  decide +kernel

lemma blockToFlat_eq_root (r : BlockIndex) (s : Fin 2) :
    blockToFlat r = .inr (⟨s.val, by omega⟩ : Fin 24) ↔
      r = .inl (.inr s) := by
  revert r s
  decide +kernel

lemma blockToFlat_eq_zero (r : BlockIndex) :
    blockToFlat r = .inr 0 ↔ r = .inl (.inr 0) := by
  simpa using blockToFlat_eq_root r 0

lemma blockToFlat_eq_one (r : BlockIndex) :
    blockToFlat r = .inr 1 ↔ r = .inl (.inr 1) := by
  simpa using blockToFlat_eq_root r 1

set_option maxHeartbeats 1000000 in
omit [CharP F 2] in
lemma blockMatrix_positive (i : Fin 4) (t : F) (r s : BlockIndex) :
    blockMatrix i (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
      (by decide) t) r s =
      (if r = s then 1 else 0) + t * (positiveCoefficient i r s : F) +
        t ^ 2 * (if r = .inl (.inr 0) ∧ s = .inl (.inr 1) then 1 else 0) := by
  rcases r with (r | r) | (⟨r, k⟩ | r) <;>
    rcases s with (s | s) | (⟨s, l⟩ | s)
  all_goals
    simp [blockMatrix, specialBlock, positiveCoefficient,
      SpecialLinearGroup.transvection, Matrix.transvection, Matrix.one_apply, Matrix.single_apply,
      Matrix.blockDiagonal]
  all_goals try (guard_hyp r : Fin 2; fin_cases r)
  all_goals try (guard_hyp s : Fin 2; fin_cases s)
  all_goals simp

set_option maxHeartbeats 1000000 in
omit [CharP F 2] in
lemma blockMatrix_negative (i : Fin 4) (t : F) (r s : BlockIndex) :
    blockMatrix i (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0)
      (by decide) t) r s =
      (if r = s then 1 else 0) + t * (negativeCoefficient i r s : F) +
        t ^ 2 * (if r = .inl (.inr 1) ∧ s = .inl (.inr 0) then 1 else 0) := by
  rcases r with (r | r) | (⟨r, k⟩ | r) <;>
    rcases s with (s | s) | (⟨s, l⟩ | s)
  all_goals
    simp [blockMatrix, specialBlock, negativeCoefficient,
      SpecialLinearGroup.transvection, Matrix.transvection, Matrix.one_apply, Matrix.single_apply,
      Matrix.blockDiagonal]
  all_goals try (guard_hyp r : Fin 2; fin_cases r)
  all_goals try (guard_hyp s : Fin 2; fin_cases s)
  all_goals simp


/-- The upper transvection is the genuine positive integral Geck curve. -/
lemma ambientHom_positive (i : Fin 4) (t : F) :
    ambientHom i (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
      (by decide) t) = positiveUnit (typeDRootPairing_baseEquiv 2 i) t := by
  apply Units.ext
  ext r s
  obtain ⟨r, rfl⟩ := (latticeEquiv i).surjective r
  obtain ⟨s, rfl⟩ := (latticeEquiv i).surjective s
  rw [ambientHom_entry, positiveUnit_val, ← flatEquiv_blockToFlat,
    ← flatEquiv_blockToFlat, positiveMatrix_entry, blockMatrix_positive]
  rw [CharTwo.intCast_eq_mod (R := F) (eData i (blockToFlat r) (blockToFlat s)),
    eData_mod_two]
  simp only [blockToFlat.injective.eq_iff, blockToFlat_eq_zero, blockToFlat_eq_one]

/-- The lower transvection is the genuine negative integral Geck curve. -/
lemma ambientHom_negative (i : Fin 4) (t : F) :
    ambientHom i (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0)
      (by decide) t) = negativeUnit (typeDRootPairing_baseEquiv 2 i) t := by
  apply Units.ext
  ext r s
  obtain ⟨r, rfl⟩ := (latticeEquiv i).surjective r
  obtain ⟨s, rfl⟩ := (latticeEquiv i).surjective s
  rw [ambientHom_entry, negativeUnit_val, ← flatEquiv_blockToFlat,
    ← flatEquiv_blockToFlat, negativeMatrix_entry, blockMatrix_negative]
  rw [CharTwo.intCast_eq_mod (R := F) (fData i (blockToFlat r) (blockToFlat s)),
    fData_mod_two]
  simp only [blockToFlat.injective.eq_iff, blockToFlat_eq_zero, blockToFlat_eq_one]

/-- Both pinning formulas, proved for the constructed faithful representation. -/
lemma curveComparison : CurveComparison (F := F) :=
  ⟨ambientHom_positive, ambientHom_negative⟩

end
end Triality.Standard.Parabolics.RankOneMatrices
