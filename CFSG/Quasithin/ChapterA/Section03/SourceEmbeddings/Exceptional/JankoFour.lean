module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.FaithfulSylow
public import CFSG.Quasithin.MainConverse.SporadicLocal.J4.SylowCenterEven

/-!
# A proper exceptional section in J₄ has nontrivial two-core

The original full Sylow acts faithfully on a local component with trivial
two-core. For the three exceptional simple carriers this bounds its order
by256, whereas the actual J₄ order has a factor512. Thus the original
subgroup has nontrivial two-core, and its characteristic two-core places
both the subgroup and the full Sylow in an actual two-local normalizer.

This is the entry to the remaining local-overgroup inspection; it makes
no claim that the three maximal Sylow overgroups have been classified.
Source: Aschbacher–Smith A.3.12(17), pp.47–48, and13.6.27, p.934.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
variable {G : Type*} [Group G] [Finite G]

/-- Every original exceptional section in J₄ has nontrivial intrinsic two-core. -/
theorem jankoFour_core_ne_bot (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B)) (e : G ≃* Janko4.Model) : pCore 2 B ≠ ⊥ := by
  intro hc
  have hd : 512 ∣ Nat.card G := by
    rw [Nat.card_congr e.toEquiv, Janko4.Cardinality.model_card]
    decide
  have hs := S.pow_dvd_card_of_pow_dvd_card (n := 9) hd
  have hb := sylow_card_dvd_of_core_eq_bot S B hB hn h hc
    (MainConverse.SporadicLocal.J4SylowCenterEven.evenCharacteristic_of_equiv e S)
  have hh : 512 ∣ 256 := hs.trans hb
  norm_num at hh

/-- The actual characteristic-core normalizer is a common two-local
overgroup of the original component and its full Sylow actor. -/
theorem jankoFour_exists_twoLocal (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (h : IsModel (B ⧸ pCore 2 B)) (e : G ≃* Janko4.Model) :
    ∃ N : Subgroup G, IsTwoLocal N ∧ B ≤ N ∧ (S : Subgroup G) ≤ N := by
  let U := (pCore 2 B).map B.subtype
  have hU : U ≠ ⊥ := fun he => jankoFour_core_ne_bot S B hB hn h e
    ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hnU := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  exact ⟨normalizer (U : Set G), ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩,
    B.le_normalizer.trans hnU, hn.trans hnU⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
