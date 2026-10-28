module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.Transport

/-!
# Lifting the Sylow controls for the extraspecial plane

Generation and Sylow intersection lift through the original conjugation
image. Normality is pulled back only inside the prescribed Sylow T.
The plane itself is fixed by J₁(T), but need not be T-invariant.

Source: Aschbacher--Smith 15.1.16--18, printed pp.1092--1093.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Thompson fixedness and generation lift for a whole marked subspace. -/
theorem fixed_and_generation
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (W : Submodule (ZMod 2) (Additive V))
    (hfixed : W ≤ fixedSpace (imageRepresentation M V hn)
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict))
    (hgen : subspaceKernel (imageRepresentation M V hn) W ⊤ ⊔
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict = ⊤) :
    let Z := (binarySubgroup W).map V.subtype
    Z ≤ thompsonFixed T V ∧ M = (M ⊓ centralizer (Z : Set G)) ⊔ (T : Subgroup G) := by
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let K := subspaceKernel (imageRepresentation M V hn) W ⊤
  have hf : Function.Surjective f := (actionHom M V hn).rangeRestrict_surjective
  constructor
  · rintro z ⟨v,hv,rfl⟩
    refine ⟨v.property,?_⟩
    intro j hj
    have hjM := hTM (ChapterB.thompsonJ_le _ _ hj)
    have hjf : f ⟨j,hjM⟩ ∈ ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f :=
      mem_map_of_mem f hj
    have he := congrArg (fun w : Additive V => (w.toMul : G))
      (hfixed hv ⟨_,hjf⟩)
    change j * (v : G) * j⁻¹ = v at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · have hmap : (K.comap f ⊔ (T : Subgroup G).subgroupOf M).map f = ⊤ := by
      rw [Subgroup.map_sup,map_comap_eq_self_of_surjective hf]
      exact hgen
    have htop : K.comap f ⊔ (T : Subgroup G).subgroupOf M = ⊤ := by
      have he := congrArg (Subgroup.comap f) hmap
      rwa [comap_map_eq_self ((K.ker_le_comap f).trans le_sup_left),comap_top] at he
    have he := congrArg (Subgroup.map M.subtype) htop
    have hU : (K.comap f).map M.subtype =
        M ⊓ centralizer ((binarySubgroup W).map V.subtype : Set G) :=
      stabilizer_preimage M V hn W
    rw [Subgroup.map_sup,hU,
      map_subgroupOf_eq_of_le hTM,←MonoidHom.range_eq_map,M.range_subtype] at he
    exact he.symm

/-- The prescribed Sylow intersection lifts through an arbitrary action kernel. -/
theorem local_sylow
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (W : Submodule (ZMod 2) (Additive V))
    (hsyl : let K := subspaceKernel (imageRepresentation M V hn) W ⊤
      ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype =
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict) ⊓ K) :
    let Z := (binarySubgroup W).map V.subtype
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z : Set G))
      (M ⊓ centralizer (Z : Set G)) := by
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let K := subspaceKernel (imageRepresentation M V hn) W ⊤
  let U := K.comap f
  let C := M ⊓ centralizer ((binarySubgroup W).map V.subtype : Set G)
  have hUC : U.map M.subtype = C := stabilizer_preimage M V hn W
  let e : U ≃* C := (U.equivMapOfInjective M.subtype M.subtype_injective).trans
    (MulEquiv.subgroupCongr hUC)
  obtain ⟨P,hP⟩ := hsyl
  obtain ⟨Q,hQ⟩ := exists_sylow_preimage_inf_of_image (T.subtype hTM) f
    (actionHom M V hn).rangeRestrict_surjective K P hP
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  have he : C.subtype.comp e.toMonoidHom = M.subtype.comp U.subtype := by
    ext x
    rfl
  change ((Q : Subgroup U).map e.toMonoidHom).map C.subtype = _
  rw [Subgroup.map_map,he,←Subgroup.map_map,hQ,
    Subgroup.map_inf _ _ _ M.subtype_injective,Sylow.coe_subtype,
    map_subgroupOf_eq_of_le hTM,hUC]
  exact le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_right))
    (le_inf inf_le_left (le_inf (inf_le_left.trans hTM) inf_le_right))

omit [Finite G] in
/-- Normality is relative to T, without requiring T to normalize the plane. -/
theorem sylow_normal
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (W : Submodule (ZMod 2) (Additive V))
    (hnorm : let K := subspaceKernel (imageRepresentation M V hn) W ⊤
      let S := ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict
      ((S ⊓ K).subgroupOf S).Normal) :
    let Z := (binarySubgroup W).map V.subtype
    (((T : Subgroup G) ⊓ centralizer (Z : Set G)).subgroupOf (T : Subgroup G)).Normal := by
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  let K := subspaceKernel (imageRepresentation M V hn) W ⊤
  let g : T →* S := (f.comp (inclusion hTM)).codRestrict S
    (fun t => mem_map_of_mem f t.property)
  let := hnorm
  have he : ((S ⊓ K).subgroupOf S).comap g =
      (((T : Subgroup G) ⊓ centralizer
        ((binarySubgroup W).map V.subtype : Set G)).subgroupOf (T : Subgroup G)) := by
    ext t
    change f (inclusion hTM t) ∈ S ∧ f (inclusion hTM t) ∈ K ↔
      (t : G) ∈ (T : Subgroup G) ∧
        (t : G) ∈ centralizer ((binarySubgroup W).map V.subtype : Set G)
    exact ⟨fun ht => ⟨t.property,(image_mem_kernel_iff M V hn W _).mp ht.2⟩,
      fun ht => ⟨mem_map_of_mem f t.property,(image_mem_kernel_iff M V hn W _).mpr ht.2⟩⟩
  change (((T : Subgroup G) ⊓ centralizer
    ((binarySubgroup W).map V.subtype : Set G)).subgroupOf (T : Subgroup G)).Normal
  rw [←he]
  exact hnorm.comap g

end CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
