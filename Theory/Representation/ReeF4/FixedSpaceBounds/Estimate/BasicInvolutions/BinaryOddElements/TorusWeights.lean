module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle.Weights

/-!
# Coroot weights in the displacement space

A nonfixed coroot weight vector lies in the range of the torus action minus
one: divide the vector by its nonzero eigenvalue minus one. Distinct weight
vectors remain independent in this range, giving an absolute rank bound over
the original algebraically closed field. The actual product of the four
positive-convention coroot words is retained throughout.

The inverse of the F4 Cartan matrix recovers all four torus parameters from
the simple-root characters. Thus every nonidentity parameter has a nontrivial
simple-root character. No finite-group conjugacy is asserted here.

Source: GLS3, Section 1.14, with the coroot convention of `BasicWeights`.
These lemmas supply the linear step for the odd-element calculation used in
Guralnick--Malle, Classification of 2F-modules II, Lemma 8.8.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Representation Subgroup
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle

namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements
variable {F : Type*} [Field F] [IsAlgClosed F]

@[expose] noncomputable def corootTorusElement (t : Fin 4 → Fˣ) :
    Variety.Point (F4Chevalley.Carrier (k := F)) :=
  algebraicCorootElement (typeF4SimpleRootIndex 0) (t 0) *
  algebraicCorootElement (typeF4SimpleRootIndex 1) (t 1) *
  algebraicCorootElement (typeF4SimpleRootIndex 2) (t 2) *
  algebraicCorootElement (typeF4SimpleRootIndex 3) (t 3)

@[expose] def corootCharacter (t : Fin 4 → Fˣ) (μ : CorootWeight) : Fˣ :=
  t 0 ^ μ 0 * t 1 ^ μ 1 * t 2 ^ μ 2 * t 3 ^ μ 3

omit [IsAlgClosed F] in
theorem corootCharacter_sub (t : Fin 4 → Fˣ) (μ ν : CorootWeight) :
    corootCharacter t (μ - ν) = corootCharacter t μ / corootCharacter t ν := by
  simp only [corootCharacter, Pi.sub_apply, zpow_sub]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

theorem torus_action_weight (B : AlgebraicFactor F) (t : Fin 4 → Fˣ)
    {μ : CorootWeight} {v : B.Space} (hv : IsCorootWeightVector B μ v) :
    (B.action.action (corootTorusElement t) : Module.End F B.Space) v =
      (corootCharacter t μ : F) • v := by
  simp only [corootTorusElement, map_mul, Units.val_mul, Module.End.mul_apply,
    hv.2, map_smul, smul_smul, corootCharacter, Units.val_mul,
    Units.val_zpow_eq_zpow_val]
  congr 1
  ring

theorem displacement_ge_of_weights {ι : Type*} [Fintype ι]
    (B : AlgebraicFactor F) (t : Fin 4 → Fˣ) (μ : ι → CorootWeight)
    (hμ : Function.Injective μ) (hocc : ∀ i, ∃ v, IsCorootWeightVector B (μ i) v)
    (hmove : ∀ i, corootCharacter t (μ i) ≠ 1) :
    Fintype.card ι ≤ Module.finrank F (LinearMap.range
      ((B.action.action (corootTorusElement t) : Module.End F B.Space) - 1)) := by
  classical
  choose v hv using hocc
  let D : Module.End F B.Space :=
    (B.action.action (corootTorusElement t) : Module.End F B.Space) - 1
  have hr (i : ι) : v i ∈ LinearMap.range D := by
    have hc : (corootCharacter t (μ i) : F) - 1 ≠ 0 := by
      intro he
      apply hmove i
      apply Units.ext
      exact sub_eq_zero.mp he
    refine ⟨((corootCharacter t (μ i) : F) - 1)⁻¹ • v i, ?_⟩
    simp only [map_smul, D, LinearMap.sub_apply, Module.End.one_apply,
      torus_action_weight B t (hv i)]
    rw [show (corootCharacter t (μ i) : F) • v i - v i =
      ((corootCharacter t (μ i) : F) - 1) • v i by rw [sub_smul, one_smul]]
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  let w : ι → LinearMap.range D := fun i => ⟨v i, hr i⟩
  have hw : LinearIndependent F w :=
    LinearIndependent.of_comp (LinearMap.range D).subtype
      (corootWeightVectors_linearIndependent B μ hμ v hv)
  exact hw.fintype_card_le_finrank

theorem highestWeight_word_occurs (B : AlgebraicFactor F)
    (a : Fin 2 × Fin 2) (ha : B.HasBasicHighestWeight a) (w : List (Fin 4)) :
    ∃ v, IsCorootWeightVector B
      (reflectWord w (fun i => (basicCoefficient a i : ℤ))) v := by
  obtain ⟨v, hv⟩ := ha
  apply exists_corootWeightVector_word
  refine ⟨v, hv.1, ?_⟩
  intro i t
  simpa only [zpow_natCast] using hv.2.2 i t

omit [IsAlgClosed F] in
theorem exists_nontrivial_rootCharacter (t : Fin 4 → Fˣ) (ht : t ≠ 1) :
    ∃ i, corootCharacter t (typeF4CartanMatrix i) ≠ 1 := by
  by_contra hn
  have he : ∀ i, corootCharacter t (typeF4CartanMatrix i) = 1 := by simpa using hn
  let r := fun i => corootCharacter t (typeF4CartanMatrix i)
  have hrec : t = ![r 0 ^ 2 * r 1 ^ 3 * r 2 ^ 4 * r 3 ^ 2,
      r 0 ^ 3 * r 1 ^ 6 * r 2 ^ 8 * r 3 ^ 4,
      r 0 ^ 2 * r 1 ^ 4 * r 2 ^ 6 * r 3 ^ 3,
      r 0 * r 1 ^ 2 * r 2 ^ 3 * r 3 ^ 2] := by
    funext i
    fin_cases i <;> apply Units.ext
    all_goals simp [r, corootCharacter, typeF4CartanMatrix]
    all_goals field_simp
  apply ht
  rw [hrec]
  funext i
  fin_cases i <;> simp [r, he]

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements
