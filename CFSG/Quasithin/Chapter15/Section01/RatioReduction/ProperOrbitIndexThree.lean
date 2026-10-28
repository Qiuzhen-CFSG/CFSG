module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.OrbitSeed
public import Theory.Representation.BinaryOffender.KernelPairIndexThree

/-!
# The index-three proper-orbit endpoint

For the proper orbit in Aschbacher--Smith 15.1.2, the marked six-group acts
faithfully on a binary support and the support image has order 36.  The two
pointwise action kernels, together with the selected Sylow subgroup, therefore
have index dividing 3.  The unique partner maximal local subgroup contains
both kernel centralizers and the Sylow subgroup; maximality makes the index
exactly 3.  The final theorem records the literal centralizer factorization
from printed p.1085.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem kernel_pair_comap {D : Type*} [Group D]
    (f : G →* D) (hf : Function.Surjective f) (C E : Subgroup D) (S : Subgroup G) :
    (C ⊔ E ⊔ S.map f).comap f = C.comap f ⊔ E.comap f ⊔ S := by
  let L := C.comap f ⊔ E.comap f ⊔ S
  have hk : f.ker ≤ L := (ker_le_comap f C).trans (le_sup_left.trans le_sup_left)
  have hm : L.map f = C ⊔ E ⊔ S.map f := by
    dsimp only [L]
    rw [Subgroup.map_sup, Subgroup.map_sup, map_comap_eq_self_of_surjective hf,
      map_comap_eq_self_of_surjective hf]
  exact (congrArg (Subgroup.comap f) hm.symm).trans (comap_map_eq_self hk)

omit [Finite G] in
private theorem map_normal_pair_product {D : Type*} [Group D]
    (C E S : Subgroup G) [C.Normal] [E.Normal] (f : G →* D) :
    (((C ⊔ E ⊔ S).map f : Subgroup D) : Set D) =
      (C.map f : Set D) * (E.map f : Set D) * (S.map f : Set D) := by
  rw [coe_map, normal_mul, Set.image_mul, normal_mul, Set.image_mul,
    ←coe_map, ←coe_map, ←coe_map]

omit [Finite G] in
private theorem action_kernel_centralizer (M V : Subgroup G)
    (hMV : M ≤ normalizer (V : Set G)) [IsElementaryAbelian 2 V]
    (W : Submodule (ZMod 2) (Additive V)) :
    (subspaceKernel (imageRepresentation M V hMV) W ⊤).comap
      (actionHom M V hMV).rangeRestrict =
      (centralizer (((Subgroup.toAddSubgroup.symm W.toAddSubgroup).map V.subtype) : Set G)).subgroupOf M := by
  ext m
  constructor
  · rintro ⟨_,hm⟩ v ⟨w,hw,rfl⟩
    have he := congrArg (fun y : Additive V => (y.toMul : G))
      (hm (Additive.ofMul w) hw)
    change (m:G) * (w:G) * (m:G)⁻¹ = (w:G) at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hm
    refine ⟨mem_top _,?_⟩
    intro w hw
    have he := hm (w.toMul : G) (mem_map_of_mem V.subtype hw)
    apply Additive.toMul.injective
    apply Subtype.ext
    change (m:G) * (w.toMul:G) * (m:G)⁻¹ = (w.toMul:G)
    exact (congrArg (fun x : G => x * (m:G)⁻¹) he.symm).trans (mul_inv_cancel_right _ _)


theorem source_localAction_proper_orbit_index_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    let := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let S := (T.subtype hM.1.2 : Subgroup M).map f
    ∀ (H : Subgroup D) [H.Normal] (W : Submodule (ZMod 2) (Additive V)),
      (⊤ : Subgroup D) ≤ subspaceStabilizer ρ W → W ≠ ⊥ →
      fixedSpace ρ H ≠ ⊥ → W ⊔ fixedSpace ρ H = ⊤ →
      Nat.card H = 6 → Nat.card (subspaceActionImage ρ W) = 36 →
      let K := subspaceKernel ρ W ⊤ ⊔ subspaceKernel ρ (fixedSpace ρ H) ⊤ ⊔ S
      (K.comap f).map M.subtype = M ⊓ Mc ∧ (K.comap f).index = 3 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let S := (T.subtype hM.1.2 : Subgroup M).map f
  have hf : Function.Surjective f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
  dsimp only
  intro H hHN W hW hW0 hF0 hsup hH hI
  let := hHN
  let C := subspaceKernel ρ W ⊤
  let E := subspaceKernel ρ (fixedSpace ρ H) ⊤
  let K := C ⊔ E ⊔ S
  let B := Mc.subgroupOf M
  have hCN : C.Normal := by
    change (subspaceKernel ρ W ⊤).Normal
    rw [← invariantActionHom_ker ρ W hW]
    infer_instance
  have hEN : E.Normal := by
    change (subspaceKernel ρ (fixedSpace ρ H) ⊤).Normal
    rw [← invariantActionHom_ker ρ (fixedSpace ρ H) (fixedSpace_stable_of_normal ρ H)]
    infer_instance
  let := hCN
  let := hEN
  have hC0 : fixedSpace ρ C ≠ ⊥ := by
    intro hb
    exact hW0 (le_bot_iff.mp (hb ▸ le_fixedSpace_subspaceKernel ρ W ⊤))
  have hE0 : fixedSpace ρ E ≠ ⊥ := by
    intro hb
    exact hF0 (le_bot_iff.mp (hb ▸ le_fixedSpace_subspaceKernel ρ (fixedSpace ρ H) ⊤))
  have hCMc := source_localAction_normal_actor_le_partner hG T hM hu C hC0
  have hEMc := source_localAction_normal_actor_le_partner hG T hM hu E hE0
  have hCB : C.comap f ≤ B := by
    intro m hm
    exact hCMc (mem_map_of_mem M.subtype hm)
  have hEB : E.comap f ≤ B := by
    intro m hm
    exact hEMc (mem_map_of_mem M.subtype hm)
  have hMc := (show Mc ∈ maximalTwoLocalOvergroups
    (centralizer (centralInvolutions T : Set G)) from hu ▸ Set.mem_singleton Mc)
  have hTMc : (T : Subgroup G) ≤ Mc := by
    apply le_trans _ hMc.2
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm
  have hSB : S ≤ B.map f := by
    rintro s ⟨t,ht,rfl⟩
    exact mem_map_of_mem f (hTMc ht)
  have hCK : C ≤ B.map f := by
    rw [← map_comap_eq_self_of_surjective hf C]
    exact map_mono hCB
  have hEK : E ≤ B.map f := by
    rw [← map_comap_eq_self_of_surjective hf E]
    exact map_mono hEB
  have hKB : K ≤ B.map f := sup_le (sup_le hCK hEK) hSB
  have hkerB : f.ker ≤ B := by
    intro m hm
    apply hCB
    change f m ∈ C
    rw [show f m = 1 from hm]
    exact C.one_mem
  have hpreB : K.comap f ≤ B := by
    have hh := comap_mono (f := f) hKB
    rwa [comap_map_eq_self hkerB] at hh
  have hB0 : B ≠ ⊤ := by
    intro hb
    have hMMc : M ≤ Mc := fun m hm => (hb ▸ mem_top (⟨m,hm⟩ : M) : (⟨m,hm⟩ : M) ∈ B)
    exact hne (hM.1.1.eq_of_le hMc.1.1 hMMc)
  have hd : (K.comap f).index ∣ 3 := by
    exact (K.index_comap_of_surjective hf).symm ▸ kernel_pair_sylow_index_dvd_three ρ (imageRepresentation_injective _ _ _)
      H W hW hsup hH hI ((T.subtype hM.1.2).mapSurjective hf)
  have hi : (K.comap f).index = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h1 | h3
    · exact (hB0 (top_unique ((index_eq_one.mp h1) ▸ hpreB))).elim
    · exact h3
  have hBi : B.index = 3 := by
    have hdB : B.index ∣ 3 := hi ▸ index_dvd_of_le hpreB
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdB with h1 | h3
    · exact (hB0 (index_eq_one.mp h1)).elim
    · exact h3
  have he : K.comap f = B := by
    have hh := relIndex_mul_index hpreB
    rw [hi,hBi] at hh
    have hr : (K.comap f).relIndex B = 1 := by omega
    exact le_antisymm hpreB (relIndex_eq_one.mp hr)
  refine ⟨?_,hi⟩
  rw [he]
  exact (subgroupOf_map_subtype Mc M).trans (inf_comm _ _)

theorem source_localAction_proper_orbit_intersection_index_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (H : Subgroup D) [H.Normal] (W : Submodule (ZMod 2) (Additive V)),
      (⊤ : Subgroup D) ≤ subspaceStabilizer ρ W → W ≠ ⊥ →
      fixedSpace ρ H ≠ ⊥ → W ⊔ fixedSpace ρ H = ⊤ →
      Nat.card H = 6 → Nat.card (subspaceActionImage ρ W) = 36 →
      (M ⊓ Mc).relIndex M = 3 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro H hHN W hW hW0 hF0 hsup hH hI
  let := hHN
  obtain ⟨he,hi⟩ := source_localAction_proper_orbit_index_three
    hG T hM hu hne H W hW hW0 hF0 hsup hH hI
  have he' := congrArg (Subgroup.comap M.subtype) he
  have hi' : ((M ⊓ Mc).subgroupOf M).index = 3 := by
    change ((M ⊓ Mc).comap M.subtype).index = 3
    rw [←he']
    rw [comap_map_eq_self_of_injective M.subtype_injective]
    exact hi
  exact hi'

theorem source_localAction_proper_orbit_kernel_product
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    let := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (H : Subgroup D) [H.Normal] (W : Submodule (ZMod 2) (Additive V)),
      (⊤ : Subgroup D) ≤ subspaceStabilizer ρ W → W ≠ ⊥ →
      fixedSpace ρ H ≠ ⊥ → W ⊔ fixedSpace ρ H = ⊤ →
      Nat.card H = 6 → Nat.card (subspaceActionImage ρ W) = 36 →
      let L := (subspaceKernel ρ W ⊤).comap f ⊔
        (subspaceKernel ρ (fixedSpace ρ H) ⊤).comap f ⊔
        (T.subtype hM.1.2 : Subgroup M)
      L.map M.subtype = M ⊓ Mc ∧ L.index = 3 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro H hHN W hW hW0 hF0 hsup hH hI
  let := hHN
  obtain ⟨he,hi⟩ := source_localAction_proper_orbit_index_three
    hG T hM hu hne H W hW hW0 hF0 hsup hH hI
  have hpre := kernel_pair_comap
    (actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    (actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
    (subspaceKernel (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) W ⊤)
    (subspaceKernel (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _))
      (fixedSpace (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) H) ⊤)
    (T.subtype hM.1.2 : Subgroup M)
  exact hpre ▸ ⟨he,hi⟩

theorem source_localAction_proper_orbit_centralizer_product
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    let := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (H : Subgroup D) [H.Normal] (W : Submodule (ZMod 2) (Additive V)),
      (⊤ : Subgroup D) ≤ subspaceStabilizer ρ W → W ≠ ⊥ →
      fixedSpace ρ H ≠ ⊥ → W ⊔ fixedSpace ρ H = ⊤ →
      Nat.card H = 6 → Nat.card (subspaceActionImage ρ W) = 36 →
      let Wg := (Subgroup.toAddSubgroup.symm W.toAddSubgroup).map V.subtype
      let Fg := (Subgroup.toAddSubgroup.symm (fixedSpace ρ H).toAddSubgroup).map V.subtype
      (M ⊓ centralizer (Wg : Set G)) ⊔ (M ⊓ centralizer (Fg : Set G)) ⊔
        (T : Subgroup G) = M ⊓ Mc ∧ (M ⊓ Mc).relIndex M = 3 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro H hHN W hW hW0 hF0 hsup hH hI
  let := hHN
  obtain ⟨he,_⟩ := source_localAction_proper_orbit_kernel_product
    hG T hM hu hne H W hW hW0 hF0 hsup hH hI
  have hc := action_kernel_centralizer M (localModule T M)
    (le_normalizer_conjugateSpanBy _ _) W
  have hd := action_kernel_centralizer M (localModule T M)
    (le_normalizer_conjugateSpanBy _ _)
    (fixedSpace (imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)) H)
  have hh := congrArg₂ (fun C E : Subgroup M =>
    (C ⊔ E ⊔ (T.subtype hM.1.2 : Subgroup M)).map M.subtype) hc hd
  have he' := hh.symm.trans he
  rw [Subgroup.map_sup, Subgroup.map_sup, subgroupOf_map_subtype,
    subgroupOf_map_subtype, Sylow.coe_subtype, subgroupOf_map_subtype,
    inf_of_le_left hM.1.2, inf_comm _ M, inf_comm _ M] at he'
  exact ⟨he',source_localAction_proper_orbit_intersection_index_three
    hG T hM hu hne H W hW hW0 hF0 hsup hH hI⟩

theorem source_localAction_proper_orbit_centralizer_factorization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    let := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (H : Subgroup D) [H.Normal] (W : Submodule (ZMod 2) (Additive V)),
      (⊤ : Subgroup D) ≤ subspaceStabilizer ρ W → W ≠ ⊥ →
      fixedSpace ρ H ≠ ⊥ → W ⊔ fixedSpace ρ H = ⊤ →
      Nat.card H = 6 → Nat.card (subspaceActionImage ρ W) = 36 →
      let Wg := (Subgroup.toAddSubgroup.symm W.toAddSubgroup).map V.subtype
      let Fg := (Subgroup.toAddSubgroup.symm (fixedSpace ρ H).toAddSubgroup).map V.subtype
      ((M ⊓ centralizer (Wg : Set G) : Subgroup G) : Set G) *
        ((M ⊓ centralizer (Fg : Set G) : Subgroup G) : Set G) * (T : Set G) =
        (M ⊓ Mc : Subgroup G) ∧ (M ⊓ Mc).relIndex M = 3 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro H hHN W hW hW0 hF0 hsup hH hI
  let := hHN
  have hcn : (subspaceKernel ρ W ⊤).Normal := by
    rw [← invariantActionHom_ker ρ W hW]
    infer_instance
  have hen : (subspaceKernel ρ (fixedSpace ρ H) ⊤).Normal := by
    rw [← invariantActionHom_ker ρ (fixedSpace ρ H) (fixedSpace_stable_of_normal ρ H)]
    infer_instance
  have hc := action_kernel_centralizer M V (le_normalizer_conjugateSpanBy _ _) W
  have hd := action_kernel_centralizer M V (le_normalizer_conjugateSpanBy _ _) (fixedSpace ρ H)
  let C := (centralizer (((Subgroup.toAddSubgroup.symm W.toAddSubgroup).map V.subtype) : Set G)).subgroupOf M
  let E := (centralizer (((Subgroup.toAddSubgroup.symm (fixedSpace ρ H).toAddSubgroup).map V.subtype) : Set G)).subgroupOf M
  let : C.Normal := by
    change ((centralizer (((Subgroup.toAddSubgroup.symm W.toAddSubgroup).map V.subtype) : Set G)).subgroupOf M).Normal
    exact hc ▸ hcn.comap f
  let : E.Normal := by
    change ((centralizer (((Subgroup.toAddSubgroup.symm (fixedSpace ρ H).toAddSubgroup).map V.subtype) : Set G)).subgroupOf M).Normal
    exact hd ▸ hen.comap f
  have hp := map_normal_pair_product C E (T.subtype hM.1.2 : Subgroup M) M.subtype
  dsimp only [C,E] at hp
  rw [Subgroup.map_sup,Subgroup.map_sup,subgroupOf_map_subtype,
    subgroupOf_map_subtype,Sylow.coe_subtype,subgroupOf_map_subtype,
    inf_of_le_left hM.1.2,inf_comm _ M,inf_comm _ M] at hp
  obtain ⟨he,hi⟩ := source_localAction_proper_orbit_centralizer_product
    hG T hM hu hne H W hW hW0 hF0 hsup hH hI
  exact ⟨hp.symm.trans (congrArg (fun Q : Subgroup G => (Q : Set G)) he),hi⟩

end CFSG.Quasithin.Chapter15.Section01
