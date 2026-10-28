module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceQuaternionCentralizer
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.ResidualCentralizer

/-!
# The original quaternion core meets the A₆ local subgroup in U_H

After O₂(LT)=V, also O₂(L)=V. The literal six-letter action sends L₁
onto its marked A₄ point residual, whose centralizer inside A₆ is trivial.
Hence C_T(L₁)∩L lies in V∩Q_H=V₊, and the quaternion center identifies
this intersection with V₁. Factoring Q_H=U_H C_T(L₁) then gives Q_H∩L=U_H.

Source: Aschbacher–Smith 13.5.15(9), printed pp.920–921.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCoreIntersection
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

theorem local_core_eq_module (hQ : D.LT.pCoreIn 2 = D.V) : D.L.pCoreIn 2 = D.V := by
  apply le_antisymm ((SourcePairResidual.local_core_le_LT_core h).trans hQ.le)
  rw [←(SourceSixBlock.source13_5_15_four d h e hseed hn hU).2.1]
  exact map_mono ChapterC.blockU_le_core

theorem local_centralizer_inf_local (hQ : D.LT.pCoreIn 2 = D.V) :
    ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)) ⊓ D.L = D.V₁ := by
  obtain ⟨a,ha,_⟩ := QuadraticSource.source_even_flag d
  have hmark := SourcePointCore.local_residual_marking d h a ha
  have hUL : D.UH ≤ D.L₁ := (closure_reduction h hseed hn).2.1.trans (pCoreIn_le 2 D.L₁)
  have hpoint : D.V₁ ≤ D.V := h.point_lt.le.trans h.plus_le
  apply le_antisymm
  · rintro x ⟨⟨hxT,hxc⟩,hxL⟩
    let xl : D.L := ⟨x,hxL⟩
    have hxcU : x ∈ centralizer (D.UH : Set G) := centralizer_le hUL hxc
    have hxQ : x ∈ D.QH := by
      rw [←h.kernel_UH_eq_QH]
      exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨h.T_le_H hxT,fun u hu => by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr (hxcU u hu)]
        exact D.V₁.one_mem⟩
    have hxcore : xl ∈ pCore 2 D.L := by
      rw [←SourceBarred.local_kernel_eq_core d e]
      change localMap d xl = 1
      apply mem_bot.mp
      rw [←even_inf_conjugate_residual_centralizer a]
      refine ⟨(localMap_range d).le ⟨xl,rfl⟩,?_⟩
      rw [←hmark]
      rintro _ ⟨y,hy,rfl⟩
      change localMap d y * localMap d xl = localMap d xl * localMap d y
      rw [←map_mul,←map_mul]
      exact congrArg (localMap d) (Subtype.ext (hxc y hy))
    have hxV : x ∈ D.V := (local_core_eq_module d h e hseed hn hU hQ) ▸
      mem_map_of_mem D.L.subtype hxcore
    have hxplus : x ∈ D.Vplus :=
      (LocalGeometry.seed_eq_intersection_core h
        (SourceOrthogonal.seed_index d) hU).le ⟨hxV,hxQ⟩
    exact (SourceQuaternionCentralizer.closure_inf_centralizer d h e hseed hn hU).le
      ⟨le_conjugateSpanBy _ _ hxplus,hxcU⟩
  · refine le_inf (le_inf (hpoint.trans h.V_le_T) ?_) ?_
    · exact le_centralizer_iff.mp ((le_sup_left.trans h.local_le).trans h.H_centralizes)
    · exact hpoint.trans ((local_core_eq_module d h e hseed hn hU hQ).symm.le.trans (pCoreIn_le 2 D.L))

theorem core_inf_local (hQ : D.LT.pCoreIn 2 = D.V) : D.QH ⊓ D.L = D.UH := by
  let C := (D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)
  have hUC : C ≤ centralizer (D.UH : Set G) := inf_le_right.trans
    (centralizer_le ((closure_reduction h hseed hn).2.1.trans (pCoreIn_le 2 D.L₁)))
  have hUL := (closure_reduction h hseed hn).2.2
  apply le_antisymm ?_ (le_inf h.UH_le_QH hUL)
  rintro x ⟨hxQ,hxL⟩
  have hx : x ∈ (D.UH : Set G) * (C : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left D.UH C (hUC.trans (Subgroup.centralizer_le_normalizer _))]
    exact (SourceQuaternionCentralizer.core_eq_closure_sup_local_centralizer d h e hseed hn hU).le hxQ
  obtain ⟨u,hu,c,hc,huc⟩ := hx
  have hcL : c ∈ D.L := by
    have hh := D.L.mul_mem (D.L.inv_mem (hUL hu)) hxL
    rwa [←huc,inv_mul_cancel_left] at hh
  have hcp := (local_centralizer_inf_local d h e hseed hn hU hQ).le ⟨hc,hcL⟩
  rw [←huc]
  exact D.UH.mul_mem hu (le_conjugateSpanBy _ _ (h.point_lt.le hcp))

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCoreIntersection
