module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceQuaternionCentralizer
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The original point-group core in the normal A₆ branch

The original G.2.1 seed interval also applies with the full point centralizer
G_z as its local overgroup. Even characteristic gives F*(G_z)=O₂(G_z), so
G.2.2 places the G_z-conjugate span of V₃ in O₂(G_z). This includes the
closure for every subgroup of G_z, in particular the original U_H.

The common Sylow subgroup gives O₂(G_z)≤Q_H. Intersecting the proved
factorization Q_H=U_H C_T(L₁) then yields the literal commuting product
O₂(G_z)=U_H (O₂(G_z)∩C_T(L₁)), with overlap V₁. No centrality or order bound
for the second factor is asserted here; these use the later core equality
in the assembly of clause (6).

Source: Aschbacher–Smith, proof of 13.5.15(6), printed p.921, using G.2.2
and A.1.6. The arbitrary-subgroup span bound also supplies the containment
needed for the final uniqueness argument.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCentralizerCore
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis)

include d h in
theorem point_group_characteristic : generalizedFitting D.Gz = pCore 2 D.Gz := by
  have hz : D.V₁ ≠ ⊥ := by
    intro he
    have hc := h.point_card
    rw [he, card_bot] at hc
    contradiction
  have hp : IsPGroup 2 D.V₁ :=
    h.elementary.isPGroup.to_le (h.point_lt.le.trans h.plus_le)
  have ht : (D.T : Subgroup G) ≤ D.Gz := h.T_le_H.trans h.H_centralizes
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply Chapter1.mem_He_iff.mp
  exact Chapter1.twoLocal_mem_He_of_sylow_le D.T
    (d.counterexample.qtke.evenCharacteristic D.T)
    ⟨D.V₁, hz, hp, h.normalizer_point_eq.symm⟩ ht

include d h

/-- G.2.1 applies to the full original point group, with the same seed interval. -/
theorem point_group_g2 :
    ({D.g2 with H := D.Gz} : ChapterG.Section02.Setup G).Hypothesis := by
  let B : ChapterG.Section02.Setup G := {D.g2 with H := D.Gz}
  have ho := h.g2_hypothesis
  have hlocal : B.L₁ ⊔ B.T ≤ B.H := by
    change D.g2.L₁ ⊔ (D.T : Subgroup G) ≤ D.Gz
    rw [h.g2_L₁]
    exact h.local_le.trans h.H_centralizes
  refine {
    elementary := ho.elementary
    point_ne_bot := ho.point_ne_bot
    point_le := ho.point_le
    residual := ho.residual
    V_le_T := ho.V_le_T
    T_normalizes_point := ho.T_normalizes_point
    T_normalizes_V := ho.T_normalizes_V
    T_normalizes_L := ho.T_normalizes_L
    sylow_LT := ho.sylow_LT
    H_le := ?_
    local_le := hlocal
    sylow_H := ?_
    characteristic_two := point_group_characteristic d h
    local_normalizes_V := ho.local_normalizes_V
    quotient_nonzero := ho.quotient_nonzero
    irreducible := ho.irreducible }
  · exact Subgroup.centralizer_le_normalizer _
  · exact ⟨D.T.subtype (h.T_le_H.trans h.H_centralizes),
      map_subgroupOf_eq_of_le (h.T_le_H.trans h.H_centralizes)⟩

theorem point_span_le_point_core :
    conjugateSpanBy D.Vplus D.Gz ≤ D.Gz.pCoreIn 2 := by
  have hb := point_group_g2 d h
  have hp : IsPGroup 2 (conjugateSpanBy D.Vplus D.Gz) := hb.U_isPGroup
  exact le_pCoreIn_of_normalizes hp hb.U_le_H (le_normalizer_conjugateSpanBy _ _)

theorem span_le_point_core (J : Subgroup G) (hJ : J ≤ D.Gz) :
    conjugateSpanBy D.Vplus J ≤ D.Gz.pCoreIn 2 :=
  (conjugateSpanBy_mono le_rfl hJ).trans (point_span_le_point_core d h)

theorem closure_le_point_core : D.UH ≤ D.Gz.pCoreIn 2 :=
  span_le_point_core d h D.H h.H_centralizes

omit d in
theorem point_core_le_core : D.Gz.pCoreIn 2 ≤ D.QH := by
  have ht : D.Gz.pCoreIn 2 ≤ (D.T : Subgroup G) :=
    (pCoreIn_le_sylow D.Gz (D.T.subtype (h.T_le_H.trans h.H_centralizes))).trans_eq
      (map_subgroupOf_eq_of_le (h.T_le_H.trans h.H_centralizes))
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 D.Gz) (ht.trans h.T_le_H)
    (h.H_centralizes.trans (D.Gz.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D.Gz (pCore 2 D.Gz))))

variable (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬ IsMulCommutative D.UH)
include d h e hseed hn hU

theorem point_core_factorization :
    D.Gz.pCoreIn 2 = D.UH ⊔
      (D.Gz.pCoreIn 2 ⊓ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G))) := by
  let P := D.Gz.pCoreIn 2
  let C := (D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)
  have hu : D.UH ≤ P := closure_le_point_core d h
  have hc : C ≤ centralizer (D.UH : Set G) := inf_le_right.trans
    (centralizer_le ((closure_reduction h hseed hn).2.1.trans (pCoreIn_le 2 D.L₁)))
  apply le_antisymm ?_ (sup_le hu inf_le_left)
  intro x hx
  have hm : x ∈ (D.UH : Set G) * (C : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left D.UH C
      (hc.trans (Subgroup.centralizer_le_normalizer _))]
    exact (SourceQuaternionCentralizer.core_eq_closure_sup_local_centralizer
      d h e hseed hn hU).le (point_core_le_core h hx)
  obtain ⟨u,huU,c,hcC,huc⟩ := hm
  have hcP : c ∈ P := by
    have hh := P.mul_mem (P.inv_mem (hu huU)) hx
    rwa [←huc, inv_mul_cancel_left] at hh
  rw [←huc]
  exact mul_mem_sup huU ⟨hcP,hcC⟩

omit d e hU in
theorem point_core_factor_commutes :
    D.Gz.pCoreIn 2 ⊓ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G)) ≤
      centralizer (D.UH : Set G) :=
  (inf_le_right.trans inf_le_right).trans
    (centralizer_le ((closure_reduction h hseed hn).2.1.trans (pCoreIn_le 2 D.L₁)))

theorem point_core_factor_overlap :
    D.UH ⊓ (D.Gz.pCoreIn 2 ⊓ ((D.T : Subgroup G) ⊓ centralizer (D.L₁ : Set G))) = D.V₁ := by
  apply le_antisymm
  · exact (inf_le_inf_left D.UH (point_core_factor_commutes h hseed hn)).trans
      (SourceQuaternionCentralizer.closure_inf_centralizer d h e hseed hn hU).le
  · have hzU : D.V₁ ≤ D.UH := h.point_lt.le.trans (le_conjugateSpanBy _ _)
    apply le_inf hzU
    apply le_inf (hzU.trans (closure_le_point_core d h))
    apply le_inf (hzU.trans (h.UH_le_QH.trans h.QH_le_T))
    exact le_centralizer_iff.mp ((le_sup_left.trans h.local_le).trans h.H_centralizes)

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceCentralizerCore
