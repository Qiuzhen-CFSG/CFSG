module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonActors
public import CFSG.Quasithin.ChapterD.Section02.ThompsonGeneration
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.TwoSubgroups

/-!
# Source Thompson image generation for the singleton and orthogonal cases

The literal image of J₁(M) is the normal closure of the image of J₁(T).
The marked singleton core has odd kernel and index two; its Sylow intersection
therefore has order two and equals the nontrivial Thompson image. In the actual
natural Omega-four case the Sylow image has order four, so its nontrivial
Thompson image is either the whole Sylow image or has order two.

The final helpers retain the individual Thompson actors and the normalization
needed for the exchanged-factor case. Source: Aschbacher--Smith15.1.13(4),
printed p.1091. Nonzero movement is the established15.1.13(2) premise.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped ENNReal IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem chosen_global_thompson_image_eq_Jhat
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (he : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
        ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
          Jhat (imageRepresentation M V hn)) :
    ((ChapterB.thompsonJ M 1).subgroupOf M).map (actionHom M V hn).rangeRestrict =
      Jhat (imageRepresentation M V hn) := by
  have hh := thompson_image_eq_Jhat_of_sylow_inf (imageRepresentation M V hn)
    (T.subtype hTM) (actionHom M V hn).rangeRestrict
    (actionHom M V hn).rangeRestrict_surjective 1 (by
      change (ChapterB.thompsonJ ((T : Subgroup G).subgroupOf M) 1).map _ = _
      rw [ChapterB.thompsonJ_subgroupOf M _ hTM 1]
      exact he)
  have ht := ChapterB.thompsonJ_subgroupOf M M le_rfl 1
  rw [subgroupOf_self] at ht
  rwa [ht] at hh

theorem chosen_thompson_images_of_order_two_intersection
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hm : ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ≠ ⊥)
    (hstar : ∀ A ∈ ChapterB.thompsonFamily (T : Subgroup G) 1,
      let B := (A.subgroupOf M).map (actionHom M V hn).rangeRestrict
      B ≠ ⊥ → B ∈ QhatStar (imageRepresentation M V hn))
    (hc : Nat.card (((T : Subgroup G).subgroupOf M).map
      (actionHom M V hn).rangeRestrict ⊓ Jhat (imageRepresentation M V hn) : Subgroup _) = 2) :
    ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
        ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
          Jhat (imageRepresentation M V hn) ∧
    ((ChapterB.thompsonJ M 1).subgroupOf M).map (actionHom M V hn).rangeRestrict =
      Jhat (imageRepresentation M V hn) := by
  have he := chosen_thompson_image_ne_bot _ _ _ hTM hn hm
  have hl := chosen_thompson_image_le_Jhat _ _ _ hTM hn hstar
  have hi := eq_of_le_of_card_ge hl (by
    rw [hc]
    have hp := (one_lt_card_iff_ne_bot _).mpr he
    omega)
  exact ⟨hi,chosen_global_thompson_image_eq_Jhat T hTM hn hi⟩

private theorem subgroup_of_four_card_or_eq {D : Type*} [Group D] [Finite D]
    (S H : Subgroup D) (hS : Nat.card S = 4) (hH : H ≠ ⊥) (hle : H ≤ S) :
    Nat.card H = 2 ∨ H = S := by
  have hd : Nat.card H ∣ 2^2 := by simpa [hS] using card_dvd_of_le hle
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases k
  · exfalso
    apply hH
    exact (eq_bot_iff_card H).mpr (by simpa using he)
  · exact Or.inl (by simpa using he)
  · exact Or.inr (eq_of_le_of_card_ge hle (by rw [hS,he]; norm_num))

theorem chosen_thompson_images_in_four_exception
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hm : ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ≠ ⊥)
    (hJ : Jhat (imageRepresentation M V hn) = ⊤)
    (hc : Nat.card (((T : Subgroup G).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) = 4) :
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
        ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
          Jhat (imageRepresentation M V hn) ∧
      ((ChapterB.thompsonJ M 1).subgroupOf M).map (actionHom M V hn).rangeRestrict =
        Jhat (imageRepresentation M V hn)) ∨
    Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) = 2 := by
  have he := chosen_thompson_image_ne_bot _ _ _ hTM hn hm
  have hl := map_mono (f := (actionHom M V hn).rangeRestrict)
    (subgroupOf_mono M (ChapterB.thompsonJ_le (T : Subgroup G) 1))
  rcases subgroup_of_four_card_or_eq _ _ hc he hl with hcard | heq
  · exact Or.inr hcard
  · have hi : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict =
          ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
            Jhat (imageRepresentation M V hn) := by
      exact heq.trans ((congrArg (fun K : Subgroup (internalActionImage M V hn) =>
        ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓ K) hJ).trans
          (inf_top_eq _)).symm
    exact Or.inl ⟨hi,chosen_global_thompson_image_eq_Jhat T hTM hn hi⟩
end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem chosen_thompson_images_of_source_omega
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hm : ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ≠ ⊥)
    (ho : SourceCases.Omega (imageRepresentation M V hn)) :
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
        ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
          Jhat (imageRepresentation M V hn) ∧
      ((ChapterB.thompsonJ M 1).subgroupOf M).map (actionHom M V hn).rangeRestrict =
        Jhat (imageRepresentation M V hn)) ∨
    Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict) = 2 := by
  apply chosen_thompson_images_in_four_exception T hTM hn hm ho.1
  let S := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  have hd : Nat.card (internalActionImage M V hn) = 36 := by
    rw [Nat.card_congr ho.2.2.2.1.some.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm]
  change Nat.card S = 4
  have hd' : Nat.card (actionHom M V hn).range = 36 := hd
  have h4 : 4 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 2) (by rw [hd']; decide)
  obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card S) 9 := by
    rw [hk]
    exact (by decide : Nat.Coprime 2 9).pow_left k
  have hdiv : Nat.card S ∣ 4 * 9 := by
    change Nat.card S ∣ 36
    rw [←hd']
    exact card_subgroup_dvd_card _
  exact Nat.dvd_antisymm (hcop.dvd_of_dvd_mul_right hdiv) h4
end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem chosen_thompson_images_of_source_singleton
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hm : ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ≠ ⊥)
    (hstar : ∀ A ∈ ChapterB.thompsonFamily (T : Subgroup G) 1,
      let B := (A.subgroupOf M).map (actionHom M V hn).rangeRestrict
      B ≠ ⊥ → B ∈ QhatStar (imageRepresentation M V hn))
    (hcases : SourceCases.Dihedral (imageRepresentation M V hn) ∨
      SourceCases.Extraspecial (imageRepresentation M V hn)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict) ∨
      SourceCases.Nine (imageRepresentation M V hn)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict)) :
    ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
        ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
          Jhat (imageRepresentation M V hn) ∧
    ((ChapterB.thompsonJ M 1).subgroupOf M).map (actionHom M V hn).rangeRestrict =
      Jhat (imageRepresentation M V hn) := by
  obtain ⟨l⟩ : Nonempty (CyclicSource.LocalGeneration
      ((imageRepresentation M V hn).comp (Jhat (imageRepresentation M V hn)).subtype)) := by
    rcases hcases with ⟨l,_,_,_,_⟩ | ⟨l,_⟩ | ⟨l,_⟩ <;> exact ⟨l⟩
  apply chosen_thompson_images_of_order_two_intersection T hTM hn hm hstar
  have hb := l.two_subgroup_inf_card_le_two (Jhat (imageRepresentation M V hn))
    (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict)
    ((T.subtype hTM).isPGroup'.map (actionHom M V hn).rangeRestrict)
  have he := chosen_thompson_image_ne_bot _ _ _ hTM hn hm
  have hl := chosen_thompson_image_le_Jhat _ _ _ hTM hn hstar
  have hp := (one_lt_card_iff_ne_bot _).mpr
    (fun hz => he (bot_unique (hl.trans_eq hz)))
  exact Nat.le_antisymm hb hp
end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem chosen_thompson_image_le_of_actors
    (T M V : Subgroup G) (hTM : T ≤ M) (hn : M ≤ normalizer (V : Set G))
    (K : Subgroup (internalActionImage M V hn))
    (hactors : ∀ A ∈ ChapterB.thompsonFamily T 1,
      (A.subgroupOf M).map (actionHom M V hn).rangeRestrict ≤ K) :
    ((ChapterB.thompsonJ T 1).subgroupOf M).map (actionHom M V hn).rangeRestrict ≤ K := by
  let f := (actionHom M V hn).rangeRestrict
  have hj : ChapterB.thompsonJ T 1 ≤ (K.comap f).map M.subtype := by
    apply sSup_le
    intro A hA a ha
    exact ⟨⟨a,hTM (hA.1 ha)⟩,hactors A hA (mem_map_of_mem f ha),rfl⟩
  rintro _ ⟨g,hg,rfl⟩
  obtain ⟨x,hx,hxg⟩ := hj hg
  have he : x = g := Subtype.ext hxg
  change f g ∈ K
  change f x ∈ K at hx
  rwa [he] at hx

theorem exists_chosen_thompson_actor_of_moves
    (T M V : Subgroup G) (hTM : T ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hm : ⁅V,ChapterB.thompsonJ T 1⁆ ≠ ⊥) :
    ∃ A ∈ ChapterB.thompsonFamily T 1,
      (A.subgroupOf M).map (actionHom M V hn).rangeRestrict ≠ ⊥ := by
  by_contra! hh
  apply chosen_thompson_image_ne_bot T M V hTM hn hm
  exact bot_unique (chosen_thompson_image_le_of_actors T M V hTM hn ⊥
    (fun A hA => (hh A hA).le))

theorem chosen_thompson_image_normalized
    (T M V : Subgroup G) (hTM : T ≤ M) (hn : M ≤ normalizer (V : Set G)) :
    (T.subgroupOf M).map (actionHom M V hn).rangeRestrict ≤
      normalizer (↑(((ChapterB.thompsonJ T 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict) : Set _) := by
  rw [←ChapterB.thompsonJ_subgroupOf M T hTM 1]
  exact (map_mono (ChapterB.le_normalizer_thompsonJ (T.subgroupOf M) 1)).trans
    (le_normalizer_map (actionHom M V hn).rangeRestrict)
end CFSG.Quasithin.Chapter15.Section01
