module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizer.GeneratedCore
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Kernel

/-!
# The original quaternion core and local centralizer

An element of Q_H induces an inner automorphism on the extraspecial U_H,
so correcting it by an element of U_H leaves an element centralizing U_H.
The two-perfect local residual centralizes this remaining subgroup: its
commutator lies in the fixed central line V₁. Thus the original core is
U_H C_T(L₁), with no additional core-collapse or maximality hypothesis.

Source: Aschbacher–Smith 13.5.15(9), printed pp.920–921.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceQuaternionCentralizer
open Section08.SourceCompletion SourceOrthogonal
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬ IsMulCommutative D.UH)
include d h e hseed hn hU

theorem closure_inf_centralizer :
    D.UH ⊓ centralizer (D.UH : Set G) = D.V₁ := by
  rw [←center_map d h e hseed hn hU]
  ext x
  constructor
  · rintro ⟨hx,hc⟩
    exact ⟨⟨x,hx⟩,mem_center_iff.mpr (fun y => Subtype.ext (hc y y.property)),rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property, fun y hy => congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)⟩

theorem core_eq_closure_sup_centralizer :
    D.QH = D.UH ⊔ (D.QH ⊓ centralizer (D.UH : Set G)) := by
  apply le_antisymm ?_ (sup_le h.UH_le_QH inf_le_left)
  intro q hq
  have hqH : q ∈ D.H := (pCoreIn_le 2 D.H) hq
  let α := D.UH.normalizerMonoidHom ⟨q,le_normalizer_conjugateSpanBy D.Vplus D.H hqH⟩
  have ha : quotientAut (center D.UH) α = 1 := by
    apply MulEquiv.ext
    intro v
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (center D.UH) v
    rw [quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply (mem_map_iff_mem D.UH.subtype_injective).mp
    rw [center_map d h e hseed hn hU]
    have hh := (h.mem_kernel_iff h.UH_le_H).mp (h.kernel_UH_eq_QH.symm ▸ hq)
    have hh' : ⁅q,(u:G)⁆ ∈ D.V₁ := by
      rw [←commutatorElement_inv]
      exact D.V₁.inv_mem (hh.2 u u.property)
    rw [map_div, div_eq_mul_inv]
    change (α u : G) * (u : G)⁻¹ ∈ D.V₁
    simpa only [α, normalizerMonoidHom_apply_apply_coe, commutatorElement_def] using hh'
  obtain ⟨u,hu⟩ := ((quaternion d h e hseed hn hU).quotientAut_eq_one_iff_inner α).mp ha
  have hc : (u:G)⁻¹ * q ∈ centralizer (D.UH : Set G) := by
    intro x hx
    have he := congrArg (fun a : MulAut D.UH => (a ⟨x,hx⟩ : G)) hu
    change (u:G)*x*(u:G)⁻¹ = q*x*q⁻¹ at he
    calc
      x * ((u:G)⁻¹*q) = (u:G)⁻¹*((u:G)*x*(u:G)⁻¹)*q := by group
      _ = (u:G)⁻¹*(q*x*q⁻¹)*q := by rw [he]
      _ = ((u:G)⁻¹*q)*x := by group
  have hp := mul_mem_sup u.property
    (show (u:G)⁻¹*q ∈ D.QH ⊓ centralizer (D.UH : Set G) from
      ⟨D.QH.mul_mem (D.QH.inv_mem (h.UH_le_QH u.property)) hq,hc⟩)
  simpa only [mul_inv_cancel_left] using hp

theorem local_centralizes_core_centralizer :
    D.L₁ ≤ centralizer ((D.QH ⊓ centralizer (D.UH : Set G) : Subgroup G) : Set G) := by
  let C := D.QH ⊓ centralizer (D.UH : Set G)
  have hLH : D.L₁ ≤ D.H := le_sup_left.trans h.local_le
  have hHC : D.H ≤ normalizer (C : Set G) := by
    apply (le_inf ?_ ?_).trans inf_normalizer_le_normalizer_inf
    · exact D.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image D.H (pCore 2 D.H))
    · exact (le_normalizer_conjugateSpanBy D.Vplus D.H).trans
        (normalizer_le_normalizer_centralizer D.UH)
  have hHL : D.H ≤ normalizer (D.L₁ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLH).mp hn
  have hcomm : ⁅D.L₁,C⁆ ≤ D.V₁ := by
    rw [←closure_inf_centralizer d h e hseed hn hU]
    have hcC : ⁅D.L₁,C⁆ ≤ C :=
      le_normalizer_iff_commutator_le_right.mp (hLH.trans hHC)
    have hcL : ⁅D.L₁,C⁆ ≤ D.L₁ :=
      le_normalizer_iff_commutator_le_left.mp ((inf_le_left.trans (pCoreIn_le 2 D.H)).trans hHL)
    have hcore := (le_inf hcL (hcC.trans inf_le_left)).trans
      (local_core_intersection h hn).le
    rw [(SourceQuaternion.source13_5_15_five d h e hseed hn hU).1] at hcore
    exact le_inf hcore (hcC.trans inf_le_right)
  have hr := residual_centralizes_of_two_layer D.L₁ C D.V₁
    (h.elementary.isPGroup.to_le (h.point_lt.le.trans h.plus_le))
    (hLH.trans h.H_centralizes) hcomm
  have hres : (pResidual 2 D.L₁).map D.L₁.subtype = D.L₁ := by
    rw [(pResidual_eq_top_iff 2 D.L₁).mpr
      (isPPerfect_embedded_pResidual 2 (D.L ⊓ D.Gz)), ←MonoidHom.range_eq_map, range_subtype]
  rw [hres] at hr
  exact hr

theorem core_eq_closure_sup_local_centralizer :
    D.QH = D.UH ⊔ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)) := by
  rw [core_eq_closure_sup_centralizer d h e hseed hn hU]
  congr 1
  apply le_antisymm
  · exact le_inf (inf_le_left.trans h.QH_le_T)
      (le_centralizer_iff.mp (local_centralizes_core_centralizer d h e hseed hn hU))
  · intro x hx
    have hxc : x ∈ centralizer (D.UH : Set G) :=
      centralizer_le (((SourceQuaternion.source13_5_15_five d h e hseed hn hU).1).ge.trans
        (pCoreIn_le 2 D.L₁)) hx.2
    refine ⟨?_,hxc⟩
    rw [←h.kernel_UH_eq_QH]
    apply (h.mem_kernel_iff h.UH_le_H).mpr
    refine ⟨h.T_le_H hx.1,?_⟩
    intro u hu
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hxc u hu)]
    exact D.V₁.one_mem

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceQuaternionCentralizer
