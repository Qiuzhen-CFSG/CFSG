module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSecondLayer
public import Theory.GroupTheory.ConjugatePairKernelGeneration

/-!
# The original pair generates its two-core from the marked intersections

The literal quotient map of the selected K onto A₅ sends U_H to a Sylow
four-group. Its kernel is O₂(K), and the ambient O₂(L) normalizes U_H.
The transfer lemma therefore gives O₂(K)=W W^g for the same internal
conjugator, where W=U_H∩O₂(K). Together with the preceding second-layer
collapse this supplies the structural inputs for the natural upper section.

Source: Aschbacher–Smith,G.2.3(3) and G.2.4(3,8), printed pp.333–335,
as applied to the original normal branch in13.5.14–15, printed pp.919–920.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCoreProduct
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceFiveModule
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
include d

theorem closure_image_card (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hK : NormalBranch.K D g.val ≤ D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    Nat.card ((D.UH.subgroupOf (NormalBranch.K D g.val)).map (restrictedActor d hK a hi)) = 4 := by
  let U := D.UH.subgroupOf (NormalBranch.K D g.val)
  let f := restrictedActor d hK a hi
  let q := (localMap d).comp (inclusion hK)
  have he : f.ker=q.ker := restrictedActor_ker d hK a hi
  rw [←relIndex_ker,he,relIndex_ker]
  have hmap : U.map (inclusion hK) = D.UH.subgroupOf D.L := by
    apply map_injective D.L.subtype_injective
    rw [map_map]
    change U.map (NormalBranch.K D g.val).subtype = _
    rw [map_subgroupOf_eq_of_le (show D.UH≤NormalBranch.K D g.val from le_sup_left),
      map_subgroupOf_eq_of_le (closure_reduction h hseed hn).2.2]
  change Nat.card (U.map q)=4
  rw [show U.map q = (D.UH.subgroupOf D.L).map (localMap d) by change U.map ((localMap d).comp (inclusion hK)) = _; rw [←map_map,hmap]]
  obtain ⟨b,hb,_⟩ := QuadraticSource.source_even_flag d
  rw [SourcePointCore.closure_image_eq_point_core d h e hseed hn hU b hb,
    card_map_of_injective (MulAut.conj b.val).injective,pointCoreEven_card]

theorem core_le_local_core
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    (NormalBranch.K D g.val).pCoreIn 2 ≤ D.L.pCoreIn 2 := by
  rintro _ ⟨s,hs,rfl⟩
  have hsL : inclusion hK s ∈ (localMap d).ker :=
    (restrictedActor_ker d hK a hi).le
      ((restrictedActor_ker_eq_twoCore d hK a hi e).symm.le hs)
  rw [SourceBarred.local_kernel_eq_core d e] at hsL
  exact mem_map_of_mem D.L.subtype hsL

theorem core_normalizes_closure (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val ≤ D.L) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    (NormalBranch.K D g.val).pCoreIn 2 ≤ normalizer (D.UH : Set G) := by
  apply (core_le_local_core d e g hK a hi).trans
  exact ((SourcePairResidual.local_core_le_LT_core h).trans
    (h.sylow_centralizer.symm.le.trans inf_le_left)).trans
      (h.T_le_H.trans (le_normalizer_conjugateSpanBy D.Vplus D.H))

theorem core_generated (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) (g : D.L)
    (hg : g.val ∈ NormalBranch.K D g.val) (hK : NormalBranch.K D g.val ≤ D.L)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
      FivePair.five.map (MulAut.conj a.val).toMonoidHom) :
    (NormalBranch.K D g.val).pCoreIn 2 =
      (D.UH ⊓ (NormalBranch.K D g.val).pCoreIn 2) ⊔
      ChapterG.Section02.Setup.conjugate (D.UH ⊓ (NormalBranch.K D g.val).pCoreIn 2) g.val := by
  let J := NormalBranch.K D g.val
  let U := D.UH.subgroupOf J
  let f := restrictedActor d hK a hi
  let k : J := ⟨g.val,hg⟩
  have hk : f.ker=pCore 2 J := restrictedActor_ker_eq_twoCore d hK a hi e
  have hUp : IsPGroup 2 U := (show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup).comap_subtype
  have hcard : Nat.card (U.map f)=4 := closure_image_card d h e hseed hn hU g hK a hi
  have hidx : (U.map f).index=15 := by
    have hh := (U.map f).card_mul_index
    rw [hcard,nat_card_alternatingGroup,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  let P : Sylow 2 (alternatingGroup (Fin 5)) :=
    (hUp.map f).toSylow (by rw [hidx];decide)
  have hnorm : f.ker ≤ normalizer (U : Set J) := by
    intro x hx
    have hxL : inclusion hK x ∈ (localMap d).ker := (restrictedActor_ker d hK a hi).le hx
    rw [SourceBarred.local_kernel_eq_core d e] at hxL
    have hxH : x.val ∈ D.H := h.T_le_H
      (h.sylow_centralizer.symm.le (SourcePairResidual.local_core_le_LT_core h
        (mem_map_of_mem D.L.subtype hxL))).1
    apply mem_normalizer_iff.mpr
    intro u
    exact mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H hxH) u.val
  have hconj : (U.map (MulAut.conj k⁻¹).toMonoidHom).map J.subtype =
      ChapterG.Section02.Setup.conjugate D.UH g.val := by
    rw [map_map]
    change U.map (((MulAut.conj g.val⁻¹).toMonoidHom).comp J.subtype) = _
    rw [←map_map,map_subgroupOf_eq_of_le (show D.UH≤J from le_sup_left)]
    rfl
  have hgen : U ⊔ U.map (MulAut.conj k⁻¹).toMonoidHom = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,hconj,map_subgroupOf_eq_of_le (show D.UH≤J from le_sup_left),
      ←MonoidHom.range_eq_map,range_subtype]
    rfl
  have hh := kernel_eq_intersection_pair_of_twoPerfect hp f (hk ▸ pCore_isPGroup)
    U hUp k⁻¹ hgen hnorm P rfl
  simp only [hk] at hh
  have hm := congrArg (Subgroup.map J.subtype) hh
  rw [Subgroup.map_sup,map_inf _ _ _ J.subtype_injective,
    map_subgroupOf_eq_of_le (show D.UH≤J from le_sup_left)] at hm
  have hmap : ((U⊓pCore 2 J).map (MulAut.conj k⁻¹).toMonoidHom).map J.subtype =
      ChapterG.Section02.Setup.conjugate (D.UH⊓J.pCoreIn 2) g.val := by
    rw [map_map]
    change (U⊓pCore 2 J).map (((MulAut.conj g.val⁻¹).toMonoidHom).comp J.subtype) = _
    rw [←map_map,map_inf _ _ _ J.subtype_injective,
      map_subgroupOf_eq_of_le (show D.UH≤J from le_sup_left)]
    rfl
  exact hm.trans (congrArg (fun B : Subgroup G => (D.UH ⊓ J.pCoreIn 2) ⊔ B) hmap)

/-- The original selected pair supplies both structural upper-section inputs. -/
theorem exists_original_core_pair (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) :
    ∃ (a : alternatingGroup (Fin 6)) (g : D.L), g.val ∉ D.Gz ∧
      g.val ∈ NormalBranch.K D g.val ∧ NormalBranch.K D g.val ≤ D.L ∧
      D.L₁ ≤ NormalBranch.K D g.val ∧ IsPPerfect 2 (NormalBranch.K D g.val) ∧
      blockResidual D g.val = NormalBranch.K D g.val ∧
      conjugateSpanBy D.V₁ (NormalBranch.K D g.val) = D.V ∧
      ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
        FivePair.five.map (MulAut.conj a.val).toMonoidHom ∧
      D.V ⊔ (D.UH ⊓ ChapterG.Section02.Setup.conjugate D.UH g.val : Subgroup G) = D.V ∧
      (NormalBranch.K D g.val).pCoreIn 2 =
        (D.UH ⊓ (NormalBranch.K D g.val).pCoreIn 2) ⊔
        ChapterG.Section02.Setup.conjugate (D.UH ⊓ (NormalBranch.K D g.val).pCoreIn 2) g.val := by
  obtain ⟨a,g,hg,hgK,hK,hL,hp,hr,hs,hi⟩ :=
    SourceInternalMover.exists_original_internal_pair d h e hseed hn hU
  exact ⟨a,g,hg,hgK,hK,hL,hp,hr,hs,hi,
    SourceSecondLayer.second_eq_module d h e hseed hn hU g hK hL,
    core_generated d h e hseed hn hU g hgK hK hp a hi⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCoreProduct
end
