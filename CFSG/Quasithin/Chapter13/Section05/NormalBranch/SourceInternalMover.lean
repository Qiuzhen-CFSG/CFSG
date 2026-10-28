module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceFiveSpan
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceBarred

/-!
# An internal conjugator for the original selected pair

Two representatives of the natural quotient differ by O₂(L), which
normalizes the original U_H. Hence they give the same conjugate subgroup.
The selected mover lies in the pair image; lifting it from that image
puts a replacement inside the same K, without changing any original
pair, quotient, residual or span conclusion. This is the internal
conjugator needed by the direct G.2.4 core-product argument.

Source: Aschbacher–Smith,13.5.14(3–4), printed p.919, and G.2.4(2–3).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceInternalMover
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

include d in
theorem same_action_same_pair (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g k : D.L) (he : localMap d k = localMap d g) :
    ChapterG.Section02.Setup.conjugate D.UH k.val =
      ChapterG.Section02.Setup.conjugate D.UH g.val := by
  have hk : g*k⁻¹ ∈ (localMap d).ker := by
    change localMap d (g*k⁻¹)=1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  rw [SourceBarred.local_kernel_eq_core d e] at hk
  have ht : g.val*k.val⁻¹ ∈ D.H := h.T_le_H
    (h.sylow_centralizer.symm.le (SourcePairResidual.local_core_le_LT_core h
      (mem_map_of_mem D.L.subtype hk))).1
  have hn : g.val*k.val⁻¹ ∈ normalizer (D.UH : Set G) :=
    le_normalizer_conjugateSpanBy D.Vplus D.H ht
  have hm := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (D.UH : Set G)).inv_mem hn)
  change D.UH.map (MulAut.conj k.val⁻¹).toMonoidHom =
    D.UH.map (MulAut.conj g.val⁻¹).toMonoidHom
  calc
    _ = (D.UH.map (MulAut.conj (g.val*k.val⁻¹)⁻¹).toMonoidHom).map
        (MulAut.conj k.val⁻¹).toMonoidHom := congrArg (Subgroup.map (MulAut.conj k.val⁻¹).toMonoidHom) hm.symm
    _ = _ := ?_
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change k.val⁻¹*((g.val*k.val⁻¹)⁻¹*x*((g.val*k.val⁻¹)⁻¹)⁻¹)*(k.val⁻¹)⁻¹ =
    g.val⁻¹*x*(g.val⁻¹)⁻¹
  group

include d in
theorem exists_internal_mover (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L)
    (hi : localMap d g ∈ ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d))
    (hg : g.val ∉ D.Gz) :
    ∃ k : D.L, k.val ∈ NormalBranch.K D g.val ∧ k.val ∉ D.Gz ∧
      localMap d k = localMap d g ∧ NormalBranch.K D k.val = NormalBranch.K D g.val := by
  obtain ⟨k,hk,he⟩ := hi
  have hc := same_action_same_pair d h e g k he
  refine ⟨k,hk,?_,he,congrArg (D.UH ⊔ ·) hc⟩
  intro hkz
  apply hg
  apply h.normalizer_point_eq.le
  apply (ReturningPlane.localNormalizer_mem d D.V₁ (h.point_lt.le.trans h.plus_le) g).mpr
  rw [←he]
  exact (ReturningPlane.localNormalizer_mem d D.V₁ (h.point_lt.le.trans h.plus_le) k).mp
    (h.normalizer_point_eq.symm.le hkz)

include d in
theorem exists_original_internal_pair (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬ IsMulCommutative D.UH) :
    ∃ (a : alternatingGroup (Fin 6)) (g : D.L), g.val ∉ D.Gz ∧
      g.val ∈ NormalBranch.K D g.val ∧ NormalBranch.K D g.val ≤ D.L ∧
      D.L₁ ≤ NormalBranch.K D g.val ∧ IsPPerfect 2 (NormalBranch.K D g.val) ∧
      blockResidual D g.val = NormalBranch.K D g.val ∧
      conjugateSpanBy D.V₁ (NormalBranch.K D g.val) = D.V ∧
      ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) =
        FivePair.five.map (MulAut.conj a.val).toMonoidHom := by
  obtain ⟨a,ha,g,hg,hgn,hfix,hKL,hi⟩ := SourceFivePair.exists_original_five_pair d h e hseed hn hU
  have hgi : localMap d g ∈ ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d) := by
    rw [hi,hg]
    exact mem_map_of_mem (MulAut.conj a.val).toMonoidHom FivePair.mover_mem
  obtain ⟨k,hk,hkn,he,hpair⟩ := exists_internal_mover d h e g hgi hgn
  have hLK := SourcePairResidual.local_le_pair d h e g a ha hi
  have hgnK := SourcePairResidual.mover_normalizes_pair d h e g hgi
  have hp := SourcePairResidual.pair_twoPerfect h hseed hn g hLK hgnK
  have hr := SourcePairResidual.blockResidual_eq_pair h hseed hn g hLK hgnK
  have hs := SourceFiveSpan.point_span d hKL a hi h
  refine ⟨a,k,hkn,hpair.symm ▸ hk,hpair.symm ▸ hKL,hpair.symm ▸ hLK,
    hpair.symm ▸ hp,?_,hpair.symm ▸ hs,?_⟩
  · change (pResidual 2 (D.LT.pCoreIn 2 ⊔ NormalBranch.K D k.val : Subgroup G)).map _ = _
    rw [hpair]
    exact hr
  · rw [hpair]
    exact hi

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceInternalMover
end
