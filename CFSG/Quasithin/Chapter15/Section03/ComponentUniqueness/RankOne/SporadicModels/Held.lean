module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.LocalConfiguration
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.Held.Reduction
public import CFSG.Quasithin.MainConverse.SporadicLocal.He
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupCoverage
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

/-!
# The Held rank-one obstruction

Transport the source plane and the component's Sylow intersection along the
actual equivalence with Held. The normalizer reduction, using the proved even
characteristic of this concrete carrier, produces a Sylow-normal four-group
whose normalizer is neither a two-group nor of order divisible by nine.

The intrinsic normal elementary enumeration and the certified cardinality
filter conjugate this four-group to one of three literal rows. Each full row
normalizer is a two-group or has order divisible by nine, giving the required
contradiction. `LocalConfiguration.not_held` discharges every concrete premise;
`reduced_not_held` applies it to the actual component image in I/C_I(L).
The conditional reductions remain available separately.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.43,
sporadic paragraph on printed p.1140, and 1.1.5(3)(f), printed p.502.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
variable {G : Type*} [Group G] [Finite G]
namespace HeldReduction

/-- The source configuration gives an actual Sylow-normal four-group in
Held whose full inner normalizer is neither a two-group nor divisible by nine.
The argument includes every ambient two-group extension of the component. -/
theorem held_four_group_witness {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V) (e : K ≃* Held.He) :
    ∃ (T : Sylow 2 Held.He) (W : Subgroup Held.He),
      W ≤ (T : Subgroup Held.He) ∧ IsElementaryAbelian 2 W ∧ Nat.card W = 4 ∧
      (T : Subgroup Held.He) ≤ normalizer (W : Set Held.He) ∧
      ¬ IsPGroup 2 (normalizer (W : Set Held.He)) ∧
      ¬ 9 ∣ Nat.card (normalizer (W : Set Held.He)) := by
  let : K.Normal := c.normal
  let : IsElementaryAbelian 2 V := c.plane_elementary
  have hVK := plane_le_component c
  let W₀ := V.subgroupOf K
  let W := W₀.map e.toMonoidHom
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.subgroupOf hVK
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  obtain ⟨P, hP⟩ := c.sylow
  obtain ⟨T₀, hT₀⟩ := P.exists_subgroupOf_eq_of_normal K
  let T := T₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hWT : W₀ ≤ (T₀ : Subgroup K) := by
    rw [hT₀, hP]
    exact fun _ hx => c.plane_le_sylow hx
  have hTN : (T₀ : Subgroup K) ≤ normalizer (W₀ : Set K) := by
    rw [hT₀, hP, ← subgroupOf_normalizer_eq hVK]
    exact fun _ hx => local_le_plane_normalizer c (c.sylow_le_local hx)
  let en : normalizer (W₀ : Set K) ≃* normalizer (W : Set Held.He) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_equiv_normalizer_eq W₀ e))
  refine ⟨T, W, map_mono hWT, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [card_map_of_injective e.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv).trans c.plane_card
  · change (T₀ : Subgroup K).map e.toMonoidHom ≤ normalizer (W : Set Held.He)
    rw [← map_equiv_normalizer_eq W₀ e]
    exact map_mono hTN
  · exact fun hp => inner_plane_normalizer_not_two_group c (hp.of_injective en.toMonoidHom en.injective)
  · rw [← Nat.card_congr en.toEquiv]
    exact inner_plane_normalizer_nine_not_dvd c
      (MainConverse.SporadicLocal.he_evenCharacteristic_of_equiv e)

end HeldReduction

/-- Conditional assembly of the Held exclusion from the concrete four-group
normalizer calculation, discharged below in `LocalConfiguration.not_held`. -/
theorem LocalConfiguration.not_held_of_four_normalizer_arithmetic
    {K S M Y V : Subgroup G} (c : LocalConfiguration K S M Y V) (e : K ≃* Held.He)
    (hcalc : ∀ (T : Sylow 2 Held.He) (W : Subgroup Held.He),
      W ≤ (T : Subgroup Held.He) → IsElementaryAbelian 2 W → Nat.card W = 4 →
      (T : Subgroup Held.He) ≤ normalizer (W : Set Held.He) →
      IsPGroup 2 (normalizer (W : Set Held.He)) ∨
        9 ∣ Nat.card (normalizer (W : Set Held.He))) : False := by
  obtain ⟨T, W, hWT, hWE, hWc, hTN, htwo, hnine⟩ := HeldReduction.held_four_group_witness c e
  exact (hcalc T W hWT hWE hWc hTN).elim htwo hnine

/-- Assembly from the actual three-row conjugacy cover and the three inner
normalizer calculations, both discharged below in `LocalConfiguration.not_held`. -/
theorem LocalConfiguration.not_held_of_four_group_rows
    {K S M Y V : Subgroup G} (c : LocalConfiguration K S M Y V) (e : K ≃* Held.He)
    (hcover : ∀ (T : Sylow 2 Held.He) (W : Subgroup Held.He),
      W ≤ (T : Subgroup Held.He) → IsElementaryAbelian 2 W → Nat.card W = 4 →
      (T : Subgroup Held.He) ≤ normalizer (W : Set Held.He) →
      ∃ (j : Fin 22) (g : Held.He), (j = 1 ∨ j = 2 ∨ j = 3) ∧
        W.map (MulAut.conj g).toMonoidHom =
          Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ambient j)
    (hrows : ∀ j : Fin 22, (j = 1 ∨ j = 2 ∨ j = 3) →
      IsPGroup 2 (normalizer
        (Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ambient j : Set Held.He)) ∨
      9 ∣ Nat.card (normalizer
        (Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ambient j : Set Held.He))) :
    False := by
  apply c.not_held_of_four_normalizer_arithmetic e
  intro T W hWT hWE hWc hTN
  obtain ⟨j, g, hj, hg⟩ := hcover T W hWT hWE hWc hTN
  let en : normalizer (W : Set Held.He) ≃* normalizer
      (Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ambient j : Set Held.He) :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr
      ((map_equiv_normalizer_eq W (MulAut.conj g)).trans (congrArg (fun U : Subgroup Held.He =>
        normalizer (U : Set Held.He)) hg)))
  rcases hrows j hj with hp | hd
  · exact Or.inl (hp.of_injective en.toMonoidHom en.injective)
  · exact Or.inr ((Nat.card_congr en.toEquiv).symm ▸ hd)

/-- A normal Held component in any allowed ambient two-group extension cannot
support the source residual, S₃ quotient and fully moved normal four-group.
The concrete enumeration, conjugacy cover and full normalizer calculations
are all discharged. -/
theorem LocalConfiguration.not_held {K S M Y V : Subgroup G}
    (c : LocalConfiguration K S M Y V) (e : K ≃* Held.He) : False := by
  apply c.not_held_of_four_group_rows e
  · exact Held.TwoLocalCandidates.MaximalNormalizerCatalogue.four_group_conjugate_rows_of_enumeration
      (Held.TwoLocalCandidates.MaximalNormalizerCatalogue.intrinsicEnumeration
        Held.LocalPairs.SylowGeometry.Calculations.representative_isPGroup)
  · exact Held.TwoLocalCandidates.MaximalNormalizerCatalogue.four_group_normalizer_arithmetic

/-- Exclude Held for the actual component image in I/C_I(L), preserving the
original component and its possible central two-cover in the source input. -/
theorem reduced_not_held {Y S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Y S M I L V₁ V₂)
    (e : c.toComponentAction.image L ≃* Held.He) : False :=
  (localConfiguration_of_reduced c).not_held e

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels
