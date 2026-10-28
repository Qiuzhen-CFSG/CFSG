module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonGeneration
public import Theory.GroupTheory.TwoFactorSylowGeneration

/-!
# Thompson image generation in the two exchanged source factors

Each nontrivial Thompson image is a starred order-two actor and hence lies
in one of the actual factors of the source partition. The original Sylow
swapping element sends it into the other factor and normalizes the Thompson
image. The two disjoint commuting order-two groups generate order four.
Since the core has order four times an odd square, this fills its Sylow
intersection. Normal generation gives the whole-group Thompson image.

Source: Aschbacher--Smith15.1.13(4), case(6), printed p.1091.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped ENNReal IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem chosen_thompson_images_of_source_decomposable
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hm : ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ≠ ⊥)
    (hstar : ∀ A ∈ ChapterB.thompsonFamily (T : Subgroup G) 1,
      let B := (A.subgroupOf M).map (actionHom M V hn).rangeRestrict
      B ≠ ⊥ → Nat.card B = 2 ∧ B ∈ QhatStar (imageRepresentation M V hn))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor)
    (hcases : SourceCases.Decomposable (imageRepresentation M V hn) (T : Subgroup G) M
      (actionHom M V hn).rangeRestrict c d π) :
    ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
        ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
          Jhat (imageRepresentation M V hn) ∧
    ((ChapterB.thompsonJ M 1).subgroupOf M).map (actionHom M V hn).rangeRestrict =
      Jhat (imageRepresentation M V hn) := by
  let ρ := imageRepresentation M V hn
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  let H := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  obtain ⟨hcount,p,m,hpm,hmark,i,j,hij,hall,hgen,hdis,hcom,hcompl,t,ht,hijT,hjiT⟩ := hcases
  have hodd : Odd p := by
    rcases (CyclicSource.primeDimensionOptions_iff p m).mp hpm with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  have hc (k : d.Index) : Nat.card (c.ambientFactor d k).actor = 2*p := by
    obtain ⟨l,hl⟩ := hmark k
    exact (Nat.card_range_of_injective (c.ambientFactor d k).embedding.group_injective).trans
      ((Nat.card_congr hl.dihedral.some.toEquiv).trans (DihedralGroup.nat_card (n := p)))
  have hnorm : (c.ambientFactor d j).actor ≤ normalizer ((c.ambientFactor d i).actor : Set _) := by
    apply le_normalizer_iff.mpr
    intro b hb a ha
    rw [(hcom a ha b hb).symm.eq,mul_inv_cancel_right]
    exact ha
  have hcard : Nat.card (Jhat ρ) = 4*(p*p) := by
    rw [←hgen,card_sup_eq_mul_of_normalizes_of_disjoint _ _ hnorm hdis,hc,hc]
    ring
  have hbound : Nat.card (S ⊓ Jhat ρ : Subgroup _) ≤ 4 :=
    two_group_card_le_four_of_odd_factor _ _
      (((T.subtype hTM).isPGroup'.map f).to_inf_left) inf_le_right (p*p) (hodd.mul hodd) hcard
  obtain ⟨A,hA,hAne⟩ := exists_chosen_thompson_actor_of_moves (T : Subgroup G) M V hTM hn hm
  let B : Subgroup (internalActionImage M V hn) := (A.subgroupOf M).map f
  obtain ⟨hcB,hsB⟩ := hstar A hA hAne
  have hBH : B ≤ H := map_mono (subgroupOf_mono M (le_sSup hA))
  have hcover := (c.ambientBlock_stars rfl d).symm ▸ hsB
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hcover
  have hBk : B ≤ (c.ambientFactor d k).actor := by
    rw [←c.ambientBlock_generates d k]
    exact le_sSup hk
  have hH : H ≤ S ⊓ Jhat ρ :=
    chosen_thompson_image_le_Jhat _ _ _ hTM hn (fun A hA hB => (hstar A hA hB).2)
  have htS : f t ∈ S := mem_map_of_mem f ht
  have htH : f t ∈ normalizer (H : Set _) := chosen_thompson_image_normalized _ _ _ hTM hn htS
  have hswapI : (c.ambientFactor d i).actor.map (MulAut.conj (f t)).toMonoidHom =
      (c.ambientFactor d j).actor := (hp (f t) i).trans (congrArg (fun k => (c.ambientFactor d k).actor) hijT)
  have hswapJ : (c.ambientFactor d j).actor.map (MulAut.conj (f t)).toMonoidHom =
      (c.ambientFactor d i).actor := (hp (f t) j).trans (congrArg (fun k => (c.ambientFactor d k).actor) hjiT)
  have he : H = S ⊓ Jhat ρ := by
    rcases hall k with rfl | rfl
    · exact eq_intersection_of_swapped_order_two S H (Jhat ρ) _ _ B hH hbound hBk hBH hcB
        hdis hcom (f t) htH hswapI
    · exact eq_intersection_of_swapped_order_two S H (Jhat ρ) _ _ B hH hbound hBk hBH hcB
        hdis.symm (fun a ha b hb => (hcom b hb a ha).symm) (f t) htH hswapJ
  exact ⟨he,chosen_global_thompson_image_eq_Jhat T hTM hn he⟩
end CFSG.Quasithin.Chapter15.Section01
