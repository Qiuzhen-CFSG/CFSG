module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector.NaturalModel.ElementaryCore
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The central block factor and the derived line in C.6.4

The index-two escape makes Q elementary and factors it as U times the
centralizer of Uˣ. Commutators of D=C_R(K) with Uˣ lie in D ∩ U=1,
so D centralizes R. It follows that [Q,R]=[U,R], and the elementary
factorization R=Q Uˣ identifies R′ with this same two-element line.
Every element normalizing R therefore fixes that line pointwise.

Source: Aschbacher–Smith C.6.4(2),(6), printed p.168. Centrality under
the whole Λ still requires the subsequent maximal-dihedral argument.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
variable {G : Type*} [Group G] [Finite G] {K R S Λ : Subgroup G}

/-- C.6.4(6): the block centralizer is central in the original R. -/
theorem Input.block_centralizer_centralizes_R (d : Input K R S Λ) :
    R ⊓ centralizer (K : Set G) ≤ centralizer (R : Set G) := by
  let U := (blockU K).map K.subtype
  let Q := (K ⊔ S).pCoreIn 2
  let D := R ⊓ centralizer (K : Set G)
  obtain ⟨x,hx,_,hR,hQ,_,_,hE,_⟩ := d.exists_elementary_factorization
  let V := U.map (MulAut.conj x⁻¹ : G →* G)
  change R = V ⊔ Q at hR
  change Q = U ⊔ (Q ⊓ centralizer (V : Set G)) at hQ
  let := hE
  have hRU : R ≤ normalizer (U : Set G) :=
    (d.R_le_S.trans le_sup_right).trans d.normalizes_module
  have hVR : V ≤ R := hR ▸ le_sup_left
  have hRD : R ≤ normalizer (D : Set G) :=
    (le_inf R.le_normalizer
      (((d.R_le_S.trans le_sup_right).trans d.normalizes_block).trans
        (normalizer_le_normalizer_centralizer K))).trans inf_normalizer_le_normalizer_inf
  have hDU : Disjoint D U := d.core_direct_split.2.1
  have hDVU : ⁅D,V⁆ ≤ U := by
    apply commutator_le.mpr
    intro a ha v hv
    have haQ : a ∈ Q := d.block_centralizer_le_core ha
    rw [hQ] at haQ
    obtain ⟨u,hu,c,hc,rfl⟩ := (show ∃ u ∈ U, ∃ c ∈ Q ⊓ centralizer (V : Set G),
        u * c = a from by
      change a ∈ ((U ⊔ (Q ⊓ centralizer (V : Set G)) : Subgroup G) : Set G) at haQ
      rw [coe_mul_of_right_le_normalizer_left U _
        ((inf_le_left.trans d.core_le).trans hRU)] at haQ
      exact haQ)
    have hcv : ⁅c,v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hc.2 v hv).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hcv,mul_one,mul_inv_cancel,one_mul]
    exact (le_normalizer_iff_commutator_le_left.mp hRU)
      (commutator_mem_commutator hu (hVR hv))
  have hDV : D ≤ centralizer (V : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp (hVR.trans hRD)) hDVU).trans
      (disjoint_iff.mp hDU).le
  change D ≤ centralizer (R : Set G)
  apply le_centralizer_iff.mpr
  conv_lhs => rw [hR]
  refine sup_le (le_centralizer_iff.mp hDV) ?_
  exact (le_centralizer Q).trans (centralizer_le d.block_centralizer_le_core)

/-- C.6.4(2): adjoining the block-centralizer factor adds no commutators. -/
theorem Input.core_commutator_eq_module_commutator (d : Input K R S Λ) :
    ⁅(K ⊔ S).pCoreIn 2,R⁆ = ⁅(blockU K).map K.subtype,R⁆ := by
  let U := (blockU K).map K.subtype
  let D := R ⊓ centralizer (K : Set G)
  apply le_antisymm ?_ (commutator_mono d.module_le_core le_rfl)
  apply commutator_le.mpr
  intro a ha r hr
  rw [d.core_direct_split.1,sup_comm] at ha
  have hDU : D ≤ normalizer (U : Set G) :=
    inf_le_left.trans ((d.R_le_S.trans le_sup_right).trans d.normalizes_module)
  obtain ⟨u,hu,c,hc,rfl⟩ := (show ∃ u ∈ U, ∃ c ∈ D, u * c = a from by
    change a ∈ ((U ⊔ D : Subgroup G) : Set G) at ha
    rwa [coe_mul_of_right_le_normalizer_left U D hDU] at ha)
  have hcr : ⁅c,r⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (d.block_centralizer_centralizes_R hc r hr).symm
  rw [commutatorElement_mul_left_eq_conj_mul,hcr,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator hu hr

/-- The derived subgroup is exactly the marked two-element line. -/
theorem Input.derived_eq_module_commutator (d : Input K R S Λ) :
    ⁅R,R⁆ = ⁅(blockU K).map K.subtype,R⁆ := by
  let U := (blockU K).map K.subtype
  let Q := (K ⊔ S).pCoreIn 2
  let Z := ⁅U,R⁆
  obtain ⟨x,hx,_,hR,_,_,_,hE,_⟩ := d.exists_elementary_factorization
  let V := U.map (MulAut.conj x⁻¹ : G →* G)
  change R = V ⊔ Q at hR
  let := d.block.2.1.elementary.map K.subtype
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hn : R ≤ normalizer (Z : Set G) :=
    d.R_le_S.trans ((le_centralizer_iff.mp d.commutator_centralizes_S).trans
      (Subgroup.centralizer_le_normalizer _))
  have hVR : V ≤ R := hR ▸ le_sup_left
  have hQV : ⁅Q,V⁆ ≤ Z := (commutator_mono le_rfl hVR).trans_eq
    d.core_commutator_eq_module_commutator
  have hVRZ : ⁅V,R⁆ ≤ Z := by
    rw [commutator_comm]
    conv_lhs => rw [hR]
    exact commutator_sup_le_of_relative_normal R V Q V Z hn hVR d.core_le
      ((commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer V)).le.trans bot_le) hQV
  apply le_antisymm ?_ (commutator_mono (d.module_le_core.trans d.core_le) le_rfl)
  conv_lhs => lhs; rw [hR]
  exact commutator_sup_le_of_relative_normal R V Q R Z hn hVR d.core_le hVRZ
    d.core_commutator_eq_module_commutator.le

/-- Every normalizer of R fixes the marked commutator vector. -/
theorem Input.commutator_centralizes_normalizer (d : Input K R S Λ) :
    ⁅(blockU K).map K.subtype,R⁆ ≤ centralizer (normalizer (R : Set G) : Set G) := by
  obtain ⟨e,he⟩ := d.exists_marked_coordinates
  let U := (blockU K).map K.subtype
  let z : G := e.symm (Multiplicative.ofAdd SevenMarkedAction.pairVector)
  have hz : orderOf z = 2 := by
    change orderOf (U.subtype (e.symm (Multiplicative.ofAdd SevenMarkedAction.pairVector))) = 2
    rw [orderOf_injective U.subtype U.subtype_injective,e.symm.orderOf_eq]
    exact SevenMarkedAction.pairVector_order
  have hline : ⁅R,R⁆ = zpowers z := by
    rw [d.derived_eq_module_commutator,d.commutator_eq_marked_line e he,MonoidHom.map_zpowers]
    rfl
  have hn : normalizer (R : Set G) ≤ normalizer (⁅R,R⁆ : Subgroup G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp hx]
  rw [hline,normalizer_zpowers_eq_centralizer_of_order_two z hz] at hn
  rw [← d.derived_eq_module_commutator,hline]
  apply zpowers_le.mpr
  intro x hx
  exact (hn hx z (Set.mem_singleton z)).symm

end CFSG.Quasithin.ChapterC.Section06.AlternatingCentralVector
