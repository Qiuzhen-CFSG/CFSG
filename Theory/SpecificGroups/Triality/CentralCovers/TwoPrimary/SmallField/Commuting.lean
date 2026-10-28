module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.HighestLift
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Pairs
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.PairCalculations
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.TorusMotion.Weights

/-!
# The ten commuting positive-root pairs in central covers of ³D₄(2)

The actual arms torus fixes all three long roots: its norm belongs to GF(2),
so every nonzero norm is one. A generator of GF(8)ˣ acts on the three short
roots with weights t², t², and t⁻¹, all different from one. The checked D₄
root sums show that each mixed pair except the first short and first long
root commutes in the base group.

To lift this commutation, write a short-root value as a commutator with the
moving torus element. A lift of the long root commutes with that commutator,
since it centralizes both entries modulo the central kernel. Independence
of commutators from lift choices then gives exact commutation upstairs.
For the two long pairs, use the highest root's already constructed expression
as a commutator of short roots. This proves the ten pairs in both orders for
any additive sections of any central extension, hence for the literal
`universalRootSections`.

The final application discharges the commuting-pair premise of the existing
canonical-kernel consumer. Its independent normalization premise remains
explicit; no triality multiplier table is assumed.

Sources: GLS3 §2.4.5(b), especially clause (6), and §6.1
(`refs/KGroup/GLS3/chapter2.tex`, `chapter6.tex`); Aschbacher–Smith A.2.4
and I.1.3 (`refs/quasithin.pdf`, PDF pp.44 and 418).
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.PositiveCoordinates
open Triality.Standard.ConcreteBruhat.TorusCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Triality.Standard.RadicalCoordinates.LeviCommutators
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section

private theorem base_short_long_commute (P : Parameters) (hp : P.prime = 2)
    (i j : Fin 3) (hij : i ≠ 0 ∨ j ≠ 0) (s : ExtensionField P) (t : fixedField P) :
    Commute (short P hp i s) (long P hp j t) := by
  have hc (k : Fin 3) (u : ExtensionField P) :
      Commute (curve P (shortPosition i k) u) (curve P (longPosition j) t.val) := by
    apply nonsumCommute_parameters P _ _
    · have h : ∀ i j k : Fin 3, shortPosition i k ≠ longPosition j := by decide +kernel
      exact h i j k
    · rintro ⟨l, hl⟩
      have h : ∀ i j k : Fin 3, i ≠ 0 ∨ j ≠ 0 → ∀ l : Fin 12,
          (shortPosition i k, longPosition j, l) ∉ sumTriples := by decide +kernel
      exact h i j k hij l ((mem_sumTriples_iff _ _ _).mpr ((root_sum_iff _ _ _).mp hl))
  have he : Commute (shortElementary P hp i s) (longElementary P hp j t) := by
    change _ * _ = _ * _
    apply elementaryInclusion_injective P
    simp only [map_mul, shortElementary_val, longElementary_val, shortSplit, longSplit]
    exact (((hc 0 _).mul_left (hc 1 _)).mul_left (hc 2 _)).eq
  exact he.map (toCarrier P)

private def weightTable : Fin 12 → Fin 4 → ℤ :=
  ![![2, -1, 0, 0], ![0, -1, 2, 0], ![0, -1, 0, 2], ![-1, 2, -1, -1],
    ![1, 1, -1, -1], ![-1, 1, 1, -1], ![-1, 1, -1, 1],
    ![1, 0, 1, -1], ![-1, 0, 1, 1], ![1, 0, -1, 1],
    ![1, -1, 1, 1], ![0, 1, 0, 0]]

private theorem pairing_table (j : Fin 12) (i : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex j) (typeDSimpleRootIndex 2 i) =
      weightTable j i := by
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (weightTable j i : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing]
  fin_cases j <;> fin_cases i <;>
    norm_num [weightTable, rootIndex, difference, sumRoot, typeDSimpleRootIndex,
      typeDRootEmbedding, typeDRootVector, basisVector, dot, Fin.sum_univ_succ]
  all_goals norm_num [Pi.single_apply, Fin.ext_iff]

private theorem torus_curve (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (t : (ExtensionField P)ˣ) (j : Fin 12) (u : ExtensionField P) :
    torusWord P i t * curve P j u * (torusWord P i t)⁻¹ =
      curve P j (t.val ^ weightTable j i * u) := by
  rw [torusWord_curve_conjugate P hp, pairing_table]

private theorem conjugate_product {G : Type*} [Group G] (g h x : G) :
    (g*h)*x*(g*h)⁻¹ = g*(h*x*h⁻¹)*g⁻¹ := by group
private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g*(x*y)*g⁻¹ = (g*x*g⁻¹)*(g*y*g⁻¹) := by group

private theorem torus_short_zero (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (u : ExtensionField P) :
    elementaryInclusion P (torusElementary P hp .arms t) * shortSplit P 0 u *
      (elementaryInclusion P (torusElementary P hp .arms t))⁻¹ =
      shortSplit P 0 (t.val ^ 2 * u) := by
  simp only [torusElementary_arms_val, shortSplit, conjugate_mul, conjugate_product,
    torus_curve P hp]
  simp [shortPosition, weightTable, TorusCoordinates.frobenius, map_mul, map_pow, -fieldFrobenius_apply]

private theorem torus_long_two (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (u : fixedField P) :
    elementaryInclusion P (torusElementary P hp .arms t) * longSplit P 2 u *
      (elementaryInclusion P (torusElementary P hp .arms t))⁻¹ = longSplit P 2 u := by
  simp only [torusElementary_arms_val, longSplit, conjugate_product, torus_curve P hp]
  simp [longPosition, weightTable]


private def armShortWeight (P : Parameters) (t : (ExtensionField P)ˣ) :
    Fin 3 → ExtensionField P :=
  ![t.val ^ 2, t.val / (fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val)),
    t.val * fieldFrobenius P t.val / fieldFrobenius P (fieldFrobenius P t.val)]

private theorem torus_short_scaling (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (i : Fin 3) (x : ExtensionField P) :
    torusActor P hp .arms t * short P hp i x * (torusActor P hp .arms t)⁻¹ =
      short P hp i (armShortWeight P t i * x) := by
  simp only [torusActor, short, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, shortElementary_val]
  fin_cases i
  · exact torus_short_zero P hp t x
  · exact torus_arms_short_one_conjugate P hp t x
  · exact torus_arms_short_two_conjugate P hp t x

private theorem torus_fixes_longs (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) (hnorm : cubicNorm P t.val = 1)
    (j : Fin 3) (u : fixedField P) :
    torusActor P hp .arms t * long P hp j u * (torusActor P hp .arms t)⁻¹ =
      long P hp j u := by
  simp only [torusActor, long, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, longElementary_val]
  fin_cases j
  · have h : (cubicNorm P t.val)⁻¹ * u = u := by rw [hnorm, inv_one, one_mul]
    exact (torus_arms_long_zero_conjugate P hp t u).trans (congrArg (longSplit P 0) h)
  · have h : cubicNorm P t.val * u = u := by rw [hnorm, one_mul]
    exact (torus_arms_long_one_conjugate P hp t u).trans (congrArg (longSplit P 1) h)
  · exact torus_long_two P hp t u

local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "hP" => binaryParameters_prime 1 Nat.zero_lt_one
local notation "F" => ExtensionField P

private theorem small_norm (t : Fˣ) : cubicNorm P t.val = 1 := by
  rcases fixedField_cases (cubicNorm P t.val) with h | h
  · have hv := congrArg Subtype.val h
    change t.val * fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val) = 0 at hv
    exact False.elim ((mul_ne_zero (mul_ne_zero t.ne_zero
      ((map_ne_zero (fieldFrobenius P)).mpr t.ne_zero))
      ((map_ne_zero (fieldFrobenius P)).mpr ((map_ne_zero (fieldFrobenius P)).mpr t.ne_zero))) hv)
  · exact h

private theorem small_weights (t : Fˣ) :
    t.val / (fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val)) = t.val ^ 2 ∧
    t.val * fieldFrobenius P t.val / fieldFrobenius P (fieldFrobenius P t.val) = t.val⁻¹ := by
  have hn := congrArg Subtype.val (small_norm t)
  change t.val * fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val) = 1 at hn
  have hF (x : F) : fieldFrobenius P x = x ^ 2 := rfl
  simp only [hF, ← pow_mul] at hn ⊢
  have ht := t.ne_zero
  constructor
  · field_simp
    linear_combination -hn
  · field_simp

private theorem small_torus_motion (i : Fin 3) :
    ∃ (t : Fˣ) (c : F), c ≠ 1 ∧
      (∀ x, torusActor P hP .arms t * short P hP i x *
        (torusActor P hP .arms t)⁻¹ = short P hP i (c*x)) ∧
      (∀ j u, torusActor P hP .arms t * long P hP j u *
        (torusActor P hP .arms t)⁻¹ = long P hP j u) := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have ht1 : t.val ≠ 1 := by
    intro h
    have : t = 1 := Units.ext h
    rw [this, orderOf_one, Nat.card_units, card_extensionField] at ht
    change 1 = 7 at ht
    contradiction
  have ht2 : t.val ^ 2 ≠ 1 := by
    intro h
    have hh := orderOf_dvd_of_pow_eq_one (show t ^ 2 = 1 from Units.ext h)
    rw [ht, Nat.card_units, card_extensionField] at hh
    change 7 ∣ 2 at hh
    norm_num at hh
  refine ⟨t, armShortWeight P t i, ?_, torus_short_scaling P hP t i,
    torus_fixes_longs P hP t (small_norm t)⟩
  fin_cases i
  · exact ht2
  · change t.val / (fieldFrobenius P t.val * fieldFrobenius P (fieldFrobenius P t.val)) ≠ 1
    rw [(small_weights t).1]
    exact ht2
  · change t.val * fieldFrobenius P t.val / fieldFrobenius P (fieldFrobenius P t.val) ≠ 1
    rw [(small_weights t).2]
    exact inv_ne_one.mpr ht1

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField

open scoped commutatorElement
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
private theorem commute_commutator_of_images {E B : Type*} [Group E] [Group B]
    (f : E →* B) (hk : f.ker ≤ Subgroup.center E) (a b c : E)
    (ha : Commute (f c) (f a)) (hb : Commute (f c) (f b)) :
    Commute c ⁅a, b⁆ := by
  have h : c * ⁅a, b⁆ * c⁻¹ = ⁅a, b⁆ := by
    rw [conjugate_commutatorElement]
    apply CentralExtension.commutator_eq_of_image_eq f hk
    · simp only [map_mul, map_inv]
      rw [ha.eq, mul_inv_cancel_right]
    · simp only [map_mul, map_inv]
      rw [hb.eq, mul_inv_cancel_right]
  exact mul_inv_eq_iff_eq_mul.mp h

/-- A moving scalar and a fixed commuting root kill the central commutator defect. -/
private theorem commute_lifts_of_scalar_fixed {F E B : Type*} [Field F] [Group E] [Group B]
    (f : E →* B) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (u : Multiplicative F →* B) (t : B) (c : F) (hc : c ≠ 1)
    (hscale : ∀ z : F, t * u (.ofAdd z) * t⁻¹ = u (.ofAdd (c*z)))
    (x y : E) (a : F) (hx : f x = u (.ofAdd a))
    (hfix : Commute (f y) t) (hcomm : ∀ z : F, Commute (f y) (u (.ofAdd z))) :
    Commute x y := by
  let z := a / (c - 1)
  obtain ⟨v, hv⟩ := hf t
  obtain ⟨w, hw⟩ := hf (u (.ofAdd z))
  have he : f ⁅v,w⁆ = f x := by
    rw [map_commutatorElement, hv, hw, commutatorElement_def, hscale, hx,
      ← map_inv, ← map_mul]
    congr 1
    change c*z + -z = a
    dsimp [z]
    have hne : c - 1 ≠ 0 := sub_ne_zero.mpr hc
    field_simp
    ring
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← CentralExtension.commutator_eq_of_image_eq f hk he rfl]
  exact (commute_commutator_of_images f hk v w y
    (by simpa only [hv] using hfix) (by simpa only [hw] using hcomm z)).symm.commutator_eq
end Triality.Standard.CentralCovers.TwoPrimary.SmallField

open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates.LeviCommutators
open PerfectCentralCovering
open scoped commutatorElement
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "hP" => binaryParameters_prime 1 Nat.zero_lt_one
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one

private theorem short_long_lifts_commute {E : Type*} [Group E]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (i j : Fin 3) (hij : i ≠ 0 ∨ j ≠ 0) (x y : E)
    (a : ExtensionField P) (b : fixedField P)
    (hx : f x = short P hP i a) (hy : f y = long P hP j b) : Commute x y := by
  obtain ⟨t, c, hc, hs, hl⟩ := small_torus_motion i
  let u : Multiplicative (ExtensionField P) →* G :=
    { toFun := fun a => short P hP i a.toAdd
      map_one' := short_zero P hP i
      map_mul' := fun a b => short_add P hP i a.toAdd b.toAdd }
  apply commute_lifts_of_scalar_fixed f hf hk u (torusActor P hP .arms t) c hc hs x y a hx
  · rw [hy]
    exact (show Commute (torusActor P hP .arms t) (long P hP j b) from
      mul_inv_eq_iff_eq_mul.mp (hl j b)).symm
  · intro z
    rw [hy]
    exact (base_short_long_commute P hP i j hij z b).symm

private theorem long_highest_lifts_commute {E : Type*} [Group E]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (j : Fin 3) (x y : E) (a b : fixedField P)
    (hx : f x = long P hP j a) (hy : f y = long P hP 2 b) : Commute x y := by
  rcases fixedField_cases b with rfl | rfl
  · have hc : y ∈ Subgroup.center E := hk (by
      rw [MonoidHom.mem_ker, hy, long_zero])
    exact Subgroup.mem_center_iff.mp hc x
  · have h : Commute x (highestLift f hf hk) := by
      apply commute_commutator_of_images f hk
      · rw [hx, shortRootLift_project]
        exact (base_short_long_commute P hP 1 j (Or.inl (by decide)) 1 a).symm
      · rw [hx, shortRootLift_project]
        exact (base_short_long_commute P hP 2 j (Or.inl (by decide)) 1 a).symm
    apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl
      (hy.trans (highestLift_spec f hf hk).2.symm)]
    exact h.commutator_eq

/-- Every system of additive sections in a central extension has the ten
required exact commuting pairs, including their reversed orders. -/
theorem commutingPairs_of_central_extension {E : Type*} [Group E]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) : CommutingPairs L := by
  have hm (i j : Fin 3) (hij : i ≠ 0 ∨ j ≠ 0) (a : ExtensionField P) (b : fixedField P) :
      Commute (L.shortRoot i (.ofAdd a)) (L.longRoot j (.ofAdd b)) :=
    short_long_lifts_commute f hf hk i j hij _ _ a b (L.project_short i a) (L.project_long j b)
  have hl (j : Fin 3) (a b : fixedField P) :
      Commute (L.longRoot j (.ofAdd a)) (L.longRoot 2 (.ofAdd b)) :=
    long_highest_lifts_commute f hf hk j _ _ a b (L.project_long j a) (L.project_long 2 b)
  intro i j a b hij hroot
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals try exact False.elim (hroot (by unfold interactingPair; decide +kernel))
  all_goals dsimp only [RootSections.factor]
  all_goals first
    | exact hm _ _ (by decide) _ _
    | exact (hm _ _ (by decide) _ _).symm
    | exact hl _ _ _
    | exact (hl _ _ _).symm

/-- The actual six sections in the canonical cover satisfy all commuting pairs. -/
theorem universal_commutingPairs : CommutingPairs universalRootSections :=
  commutingPairs_of_central_extension (universalProjection G) (universalProjection_surjective G)
    (universalProjection_ker_le_center G) universalRootSections

/-- Discharge the commuting-pair premise of the existing canonical-kernel consumer.
The independent normalization calculation remains explicit. -/
theorem universal_not_two_dvd_kernel_of_normalization
    (hnormalize : CommutingPairs universalRootSections →
      ∃ A : CentralAdjustment (universalProjection G),
        (A.adjusted (universalProjection_ker_le_center G)
          universalRootSections).HigherCommutators) :
    ¬ 2 ∣ Nat.card (universalProjection G).ker :=
  smallField_universal_not_two_dvd_kernel_of_pair_calculations
    universal_commutingPairs hnormalize

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
