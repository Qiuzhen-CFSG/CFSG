module
public import Theory.SpecificGroups.Rudvalis.SylowLowerCentral
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.Model.SylowInvariantPair
public import Theory.GroupTheory.CompleteCentralQuotientCharacteristic
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# The characteristic subgroup used to exclude an ordinary Rudvalis component

The marked eight-group is the sixth lower-central term of the model Sylow.
It contains the Sylow center and is normalized by the actual max4 subgroup.
Conjugating this geometry and lifting through a normal perfect central cover
produces a nontrivial characteristic subgroup of the original full Sylow,
normalized by the aligned max4 preimage. All covering centers are retained.

Source: Aschbacher--Smith 15.1.22, printed p.1100; GLS3 Table 5.3r.
-/

public section
open Subgroup Theory.GroupTheory
namespace Rudvalis.OrdinaryCharacteristic
open SylowOvergroups RadicalCoverage.LocalCover

/-- The actual lower-central geometry, at any conjugate of the original marking. -/
theorem marked_geometry (γ : MulAut Model) :
    (center (localP.map γ.toMonoidHom)).map (localP.map γ.toMonoidHom).subtype ≤
      (localP.map γ.toMonoidHom).lowerCentralSeries 5 ∧
    max4.map γ.toMonoidHom ≤ normalizer ((localP.map γ.toMonoidHom).lowerCentralSeries 5 : Set Model) ∧
    (localP.map γ.toMonoidHom).lowerCentralSeries 5 ≠ ⊥ := by
  rw [←map_lowerCentralSeries,SylowLowerCentral.lowerCentral_five]
  refine ⟨?_,?_,?_⟩
  · rw [map_center_image_of_injective localP γ.toMonoidHom γ.injective,←map_map,
      ←SylowInvariantPair.elementary_zero_eq_center]
    exact map_mono (closure_mono (by simp [Set.subset_def]))
  · rw [←map_equiv_normalizer_eq]
    exact map_mono RankOneEightAction.max4_le_normalizer_eight
  · intro hh
    have hb := (map_eq_bot_iff_of_injective _ γ.injective).mp hh
    have hc := RankOneEightCharacteristic.elementary_two_card
    rw [hb,card_bot] at hc
    omega

variable {G : Type*} [Group G] [Finite G]

/-- An aligned max4 preimage normalizes a nontrivial characteristic subgroup
of the full ambient Sylow, through any normal perfect central two-cover. -/
theorem exists_full_sylow_characteristic [IsSimpleGroup Model]
    (L : Subgroup G) [L.Normal] [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* Model) (hZ : IsPGroup 2 (center L))
    (S : Sylow 2 G) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = (S : Subgroup G) ⊓ L)
    (B : Subgroup G) (hBL : B ≤ L) (γ : MulAut Model)
    (hγP : (P : Subgroup L).map (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) =
      localP.map γ.toMonoidHom)
    (hγB : (B.subgroupOf L).map (e.toMonoidHom.comp (QuotientGroup.mk' (center L))) =
      max4.map γ.toMonoidHom) :
    ∃ C : Subgroup (S : Subgroup G), C.Characteristic ∧ C ≠ ⊥ ∧
      B ≤ normalizer (C.map (S : Subgroup G).subtype : Set G) := by
  obtain ⟨hc,hn,hne⟩ := marked_geometry γ
  apply characteristic_of_normal_complete_quotient L e hZ
    LowCentralizers.model_center_eq_bot component_conj_surjective S P hP 5 B hBL
  · rwa [hγP]
  · rwa [hγP,hγB]
  · rwa [hγP]
end Rudvalis.OrdinaryCharacteristic
