module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.UniformPair
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Stellmacher.BaumannMap
public import Stellmacher.BaumannNormalizer
/-!
# The central seed of one universal characteristic pair

For the original Baumann subgroup, restrict the first characteristic
member to the central involutions of T. The normal-subgroup fixed-point
argument proves that this restriction is nontrivial. The second member
is unchanged. The full C.1.18 alternatives on this SAME pair then force
a residual block in every marked local subgroup outside the join of the
first member's centralizer and the second member's normalizer.

The uniform pair is selected before every overgroup. In particular no
containment of the full characteristic-normalizer closure is assumed.
This is the fixed-pair reduction used in 14.1.11; constructing the escaping
local-class subgroup and lifting its block are subsequent source steps.
Source: Aschbacher–Smith C.1.18–19, C.1.28 and 14.1.11, pp.126–134,978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPair
open CFSG.Quasithin.ChapterB CFSG.Quasithin.ChapterC.GlaubermanNiles
universe u v
variable {G : Type u} [Group G] [Finite G]

@[expose] noncomputable def firstSeed (T : Sylow 2 G) (D : CharacteristicPair (baumann (T : Subgroup G))) :
    Subgroup G := omegaOneCenterAmbient (T : Subgroup G) ⊓ D.first.map (baumann (T : Subgroup G)).subtype

theorem firstSeed_ne_bot (T : Sylow 2 G) (D : CharacteristicPair (baumann (T : Subgroup G))) :
    firstSeed T D ≠ ⊥ := by
  let B := baumann (T : Subgroup G)
  let C := D.first.map B.subtype
  let E := C.subgroupOf (T : Subgroup G)
  let : D.first.Characteristic := D.first_characteristic
  have hCT : C ≤ (T : Subgroup G) := (map_subtype_le D.first).trans inf_le_left
  have hTN : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)).trans
      (normalizer_le_normalizer_characteristic_image _ D.first)
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hCT).mpr hTN
  have hE : E ≠ ⊥ := by
    intro he
    have hm := congrArg (map (T : Subgroup G).subtype) he
    rw [map_subgroupOf_eq_of_le hCT,Subgroup.map_bot] at hm
    exact D.first_ne_bot ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp hm)
  let F := (center (T : Subgroup G) ⊓ E).map (T : Subgroup G).subtype
  have hF : F ≠ ⊥ := by
    intro he
    exact center_inf_ne_bot_of_normal T.isPGroup' E hE
      ((map_eq_bot_iff_of_injective _ (T : Subgroup G).subtype_injective).mp he)
  have hFC : F ≤ C := (map_mono inf_le_right).trans_eq (map_subgroupOf_eq_of_le hCT)
  have hFS : F ≤ firstSeed T D := by
    refine le_inf ?_ hFC
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨b,hb,he⟩ := hFC (mem_map_of_mem (T : Subgroup G).subtype hy)
    have hexp : (y : G)^2=1 := by
      change (b : G) = (y : G) at he
      rw [← he]
      exact congrArg B.subtype ((mem_omegaCenter_iff b).mp (D.first_le_omegaCenter hb)).1
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨y.property,hexp,fun t ht => congrArg Subtype.val ((mem_center_iff.mp hy.1) ⟨t,ht⟩)⟩
  exact fun he => hF (bot_unique (he ▸ hFS))

/-- In the noncentral source branch, a binary omega-center makes the
restricted first member equal to the entire original central seed. -/
theorem firstSeed_eq_omega_of_card_two (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    firstSeed T D = omegaOneCenterAmbient (T : Subgroup G) := by
  apply eq_of_le_of_card_ge inf_le_left
  rw [hZ]
  exact Nat.succ_le_of_lt ((firstSeed T D).one_lt_card_iff_ne_bot.mpr (firstSeed_ne_bot T D))

theorem fixed_pair_block_of_escape (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u})
    (M N : Subgroup G) (hNM : N ≤ M) (hBN : baumann (T : Subgroup G) ≤ N)
    (hlocal : InLocalClass (inclusion hBN))
    (hout : ¬ N ≤ (M ⊓ centralizer (firstSeed T D : Set G)) ⊔
      (M ⊓ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G))) :
    BlockAlternative N := by
  rcases hD N (inclusion hBN) hlocal with hc | hn | hb
  · apply False.elim
    apply hout
    apply le_sup_of_le_left
    apply le_inf hNM
    intro n hn z hz
    obtain ⟨b,hb,rfl⟩ := hz.2
    have h := mem_center_iff.mp (hc (mem_map_of_mem (inclusion hBN) hb)) (⟨n,hn⟩ : N)
    exact (congrArg N.subtype h).symm
  · apply False.elim
    apply hout
    apply le_sup_of_le_right
    apply le_inf hNM
    let : (D.second.map (inclusion hBN)).Normal := hn
    have h := (D.second.map (inclusion hBN)).le_normalizer_map N.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,map_map] at h
    exact h
  · exact hb
/-- Source C.1.18 chooses one pair, with the genuine nontrivial central seed. -/
theorem exists_uniform_pair (T : Sylow 2 G) (hne : (T : Subgroup G) ≠ ⊥) :
    ∃ D : CharacteristicPair (baumann (T : Subgroup G)),
      D.Universal.{u,v} ∧ firstSeed T D ≠ ⊥ := by
  obtain ⟨D,hD⟩ := ChapterC.RankOne.ChiProduct.SelectedRankOne.exists_baumann_universal_pair
    (T : Subgroup G) T.isPGroup' hne
  exact ⟨D,hD,firstSeed_ne_bot T D⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPair
