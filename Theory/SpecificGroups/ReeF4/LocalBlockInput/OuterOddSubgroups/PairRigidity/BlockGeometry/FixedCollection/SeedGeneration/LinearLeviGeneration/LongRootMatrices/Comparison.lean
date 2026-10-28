module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.LinearLeviGeneration.LongRootMatrices.Representation
public import Theory.SpecificGroups.ReeF4.CartanFieldAction.FieldSeparation.TraceValues.DividedPowers

/-!
# The two pinned F₄ root curves

The certified integral end-root tables, reindexed into fourteen natural
strings and the Cartan/±α block, coincide with the two transvection
operators. Their quadratic terms connect ±α; the cubic terms vanish.
Reduction of the integral linear coefficients modulo two proves both
identities for every parameter over any commutative ring of characteristic two.

Source: GLS3 §§2.3–2.4, Table 2.4 type VI, and §2.6;
`refs/KGroup/GLS3/chapter2.tex`. The block argument adapts
`Triality.LeviRankOneMatrices.Comparison` to the actual F₄ operators.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.LongRootMatrices
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup RootPairing.IntegralGeckConstruction
open ReeF4.Cartan.FieldSeparation.TraceValues
local instance : DecidableEq Basis := fun a b => instDecidableEqSum a b

def positiveCoefficient : Matrix BlockIndex BlockIndex ℤ
  | .inl (.inl k), .inl (.inr s) => if k = 0 ∧ s = 1 then 1 else 0
  | .inl (.inr r), .inl (.inl j) => if r = 0 ∧ adjacent j then 1 else 0
  | .inr (.inl (r, k)), .inr (.inl (s, l)) =>
      if r = 0 ∧ s = 1 ∧ k = l then 1 else 0
  | _, _ => 0

def negativeCoefficient : Matrix BlockIndex BlockIndex ℤ
  | .inl (.inl k), .inl (.inr s) => if k = 0 ∧ s = 0 then 1 else 0
  | .inl (.inr r), .inl (.inl j) => if r = 1 ∧ adjacent j then 1 else 0
  | .inr (.inl (r, k)), .inr (.inl (s, l)) =>
      if r = 1 ∧ s = 0 ∧ k = l then 1 else 0
  | _, _ => 0

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma positive_linear_mod_two (r s : BlockIndex) :
    matrix positive0Linear (numberedEquiv r) (numberedEquiv s) % 2 =
      positiveCoefficient r s := by
  revert r s
  simp only [Sum.forall, Prod.forall]
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma negative_linear_mod_two (r s : BlockIndex) :
    matrix negative0Linear (numberedEquiv r) (numberedEquiv s) % 2 =
      negativeCoefficient r s := by
  revert r s
  simp only [Sum.forall, Prod.forall]
  decide +kernel

lemma positive_linear_entry (r s : BlockIndex) :
    eMatrix (typeF4RootPairing_baseEquiv 0) (latticeEquiv r) (latticeEquiv s) =
      matrix positive0Linear (numberedEquiv r) (numberedEquiv s) :=
  congrArg (fun A : Matrix (Fin 52) (Fin 52) ℤ =>
    A (numberedEquiv r) (numberedEquiv s)) eMatrix_0

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma positive_quadratic_entry (r s : BlockIndex) :
    eDividedPower (typeF4RootPairing_baseEquiv 0) 2 (latticeEquiv r) (latticeEquiv s) =
      if r = .inl (.inr 0) ∧ s = .inl (.inr 1) then 1 else 0 := by
  have h := congrArg (fun A : Matrix (Fin 52) (Fin 52) ℤ =>
    A (numberedEquiv r) (numberedEquiv s)) eDividedPower_0_two
  refine h.trans ?_
  clear h
  revert r s
  simp only [Sum.forall, Prod.forall]
  decide +kernel

lemma positive_cubic_entry (r s : BlockIndex) :
    eDividedPower (typeF4RootPairing_baseEquiv 0) 3 (latticeEquiv r) (latticeEquiv s) = 0 :=
  congrArg (fun A : Matrix (Fin 52) (Fin 52) ℤ =>
    A (numberedEquiv r) (numberedEquiv s)) eDividedPower_0_three

lemma negative_linear_entry (r s : BlockIndex) :
    fMatrix (typeF4RootPairing_baseEquiv 0) (latticeEquiv r) (latticeEquiv s) =
      matrix negative0Linear (numberedEquiv r) (numberedEquiv s) :=
  congrArg (fun A : Matrix (Fin 52) (Fin 52) ℤ =>
    A (numberedEquiv r) (numberedEquiv s)) fMatrix_0

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma negative_quadratic_entry (r s : BlockIndex) :
    fDividedPower (typeF4RootPairing_baseEquiv 0) 2 (latticeEquiv r) (latticeEquiv s) =
      if r = .inl (.inr 1) ∧ s = .inl (.inr 0) then 1 else 0 := by
  have h := congrArg (fun A : Matrix (Fin 52) (Fin 52) ℤ =>
    A (numberedEquiv r) (numberedEquiv s)) fDividedPower_0_two
  refine h.trans ?_
  clear h
  revert r s
  simp only [Sum.forall, Prod.forall]
  decide +kernel

lemma negative_cubic_entry (r s : BlockIndex) :
    fDividedPower (typeF4RootPairing_baseEquiv 0) 3 (latticeEquiv r) (latticeEquiv s) = 0 :=
  congrArg (fun A : Matrix (Fin 52) (Fin 52) ℤ =>
    A (numberedEquiv r) (numberedEquiv s)) fDividedPower_0_three

variable {F : Type*} [CommRing F] [CharP F 2]

set_option maxHeartbeats 1000000 in
omit [CharP F 2] in
lemma blockMatrix_positive (t : F) (r s : BlockIndex) :
    blockMatrix (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
      (by decide) t) r s =
      (if r = s then 1 else 0) + t * (positiveCoefficient r s : F) +
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
lemma blockMatrix_negative (t : F) (r s : BlockIndex) :
    blockMatrix (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0)
      (by decide) t) r s =
      (if r = s then 1 else 0) + t * (negativeCoefficient r s : F) +
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

lemma positiveMatrix_entry (t : F) (r s : BlockIndex) :
    positiveMatrix (typeF4RootPairing_baseEquiv 0) t (latticeEquiv r) (latticeEquiv s) =
      (if r = s then 1 else 0) + t * (positiveCoefficient r s : F) +
        t ^ 2 * (if r = .inl (.inr 0) ∧ s = .inl (.inr 1) then 1 else 0) := by
  rw [positiveMatrix_formula]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    eDividedPower_one, positive_linear_entry, positive_quadratic_entry,
    positive_cubic_entry, Matrix.one_apply, latticeEquiv.injective.eq_iff,
    smul_eq_mul, Int.coe_castRingHom]
  rw [CharTwo.intCast_eq_mod (R := F)
    (matrix positive0Linear (numberedEquiv r) (numberedEquiv s)),
    positive_linear_mod_two]
  split_ifs <;> simp

/-- The upper transvection is the actual positive F₄ Geck root curve. -/
lemma ambientHom_positive (t : F) :
    ambientHom (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
      (by decide) t) = positiveUnit (typeF4RootPairing_baseEquiv 0) t := by
  apply Units.ext
  ext r s
  obtain ⟨r, rfl⟩ := latticeEquiv.surjective r
  obtain ⟨s, rfl⟩ := latticeEquiv.surjective s
  rw [ambientHom_entry, positiveUnit_val, positiveMatrix_entry, blockMatrix_positive]

lemma negativeMatrix_entry (t : F) (r s : BlockIndex) :
    negativeMatrix (typeF4RootPairing_baseEquiv 0) t (latticeEquiv r) (latticeEquiv s) =
      (if r = s then 1 else 0) + t * (negativeCoefficient r s : F) +
        t ^ 2 * (if r = .inl (.inr 1) ∧ s = .inl (.inr 0) then 1 else 0) := by
  rw [negativeMatrix_formula]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    fDividedPower_one, negative_linear_entry, negative_quadratic_entry,
    negative_cubic_entry, Matrix.one_apply, latticeEquiv.injective.eq_iff,
    smul_eq_mul, Int.coe_castRingHom]
  rw [CharTwo.intCast_eq_mod (R := F)
    (matrix negative0Linear (numberedEquiv r) (numberedEquiv s)),
    negative_linear_mod_two]
  split_ifs <;> simp

/-- The lower transvection is the actual negative F₄ Geck root curve. -/
lemma ambientHom_negative (t : F) :
    ambientHom (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0)
      (by decide) t) = negativeUnit (typeF4RootPairing_baseEquiv 0) t := by
  apply Units.ext
  ext r s
  obtain ⟨r, rfl⟩ := latticeEquiv.surjective r
  obtain ⟨s, rfl⟩ := latticeEquiv.surjective s
  rw [ambientHom_entry, negativeUnit_val, negativeMatrix_entry, blockMatrix_negative]

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.LongRootMatrices
