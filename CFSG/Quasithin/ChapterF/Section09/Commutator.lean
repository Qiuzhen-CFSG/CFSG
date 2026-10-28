module
public import CFSG.Quasithin.ChapterF.Section09.Basic

/-!
# The original moved seed in F.9.5(2)

For a seed of index two, nontrivial V-image modulo O₂(H) forces
V∩O₂(H)=V₊. Hence [O₂(H),V] lies in V₊. The subgroup
V₁[U_H,V] is invariant under the original L₁T and is larger than V₁,
since the action kernel on U_H/V₁ is O₂(H). Irreducibility now identifies
it with V₊. The last theorem takes the literal quotient U_H/V₁.
Source: Aschbacher–Smith F.9.5(1–2), printed p.319.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

/-- The seed is the actual core intersection whenever V escapes that core. -/
theorem seed_eq_intersection_of_not_le_core
    (hi : D.Vplus.relIndex D.V = 2) (hn : ¬ D.V ≤ D.QH) :
    D.V ⊓ D.QH = D.Vplus := by
  have hs : D.Vplus ≤ D.V ⊓ D.QH :=
    le_inf h.plus_le ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hm := relIndex_mul_relIndex D.Vplus (D.V ⊓ D.QH) D.V hs inf_le_left
  rw [hi] at hm
  have hd : D.Vplus.relIndex (D.V ⊓ D.QH) ∣ 2 := ⟨_,hm.symm⟩
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with ho | ht
  · exact le_antisymm (relIndex_eq_one.mp ho) hs
  · rw [ht] at hm
    have he : (D.V ⊓ D.QH).relIndex D.V = 1 := by omega
    exact (hn ((relIndex_eq_one.mp he).trans inf_le_right)).elim

/-- The full two-core displacements lie in the original seed. -/
theorem core_module_commutator_le_seed
    (hi : D.Vplus.relIndex D.V = 2) (hn : ¬ D.V ≤ D.QH) :
    ⁅D.QH,D.V⁆ ≤ D.Vplus := by
  rw [←h.seed_eq_intersection_of_not_le_core hi hn]
  refine le_inf ?_ ?_
  · exact le_normalizer_iff_commutator_le_right.mp (h.QH_le_T.trans h.T_normalizes_V)
  · exact le_normalizer_iff_commutator_le_left.mp
      (h.V_le_H.trans (H_normalizes_QH (D := D)))

/-- Original F.9.5(2), before taking the point quotient. -/
theorem seed_eq_point_sup_commutator
    (hi : D.Vplus.relIndex D.V = 2) (hn : ¬ D.V ≤ D.QH) :
    D.Vplus = D.V₁ ⊔ ⁅D.UH,D.V⁆ := by
  let W := D.V₁ ⊔ ⁅D.UH,D.V⁆
  have hW : W ≤ D.Vplus := sup_le h.point_lt.le
    ((commutator_mono h.UH_le_QH le_rfl).trans (h.core_module_commutator_le_seed hi hn))
  have hlocalLT : D.L₁ ⊔ (D.T : Subgroup G) ≤ D.LT :=
    sup_le ((map_subtype_le _).trans (inf_le_left.trans le_sup_left)) le_sup_right
  have hlocalV : D.L₁ ⊔ (D.T : Subgroup G) ≤ normalizer (D.V : Set G) :=
    hlocalLT.trans ((normal_subgroupOf_iff_le_normalizer h.V_le_LT).mp h.reduced.normal)
  have hlocalU : D.L₁ ⊔ (D.T : Subgroup G) ≤ normalizer (D.UH : Set G) :=
    h.local_le.trans (le_normalizer_conjugateSpanBy D.Vplus D.H)
  have hlocalZ : D.L₁ ⊔ (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G) :=
    h.local_le.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hlocalW : D.L₁ ⊔ (D.T : Subgroup G) ≤ normalizer (W : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (D.V₁ ⊔ ⁅D.UH,D.V⁆).map (MulAut.conj g).toMonoidHom = _
    have hz : D.V₁.map (MulAut.conj g).toMonoidHom = D.V₁ :=
      mem_normalizer_iff_map_conj_eq.mp (hlocalZ hg)
    have hu : D.UH.map (MulAut.conj g).toMonoidHom = D.UH :=
      mem_normalizer_iff_map_conj_eq.mp (hlocalU hg)
    have hv : D.V.map (MulAut.conj g).toMonoidHom = D.V :=
      mem_normalizer_iff_map_conj_eq.mp (hlocalV hg)
    rw [Subgroup.map_sup,map_commutator,hz,hu,hv]
  have hne : W ≠ D.V₁ := by
    intro he
    apply hn
    intro v hv
    rw [←h.kernel_UH_eq_QH]
    apply (h.mem_kernel_iff h.UH_le_H).mpr
    refine ⟨h.V_le_H hv,?_⟩
    intro u hu
    exact (le_sup_right.trans he.le) (commutator_mem_commutator hu hv)
  exact ((h.irreducible W le_sup_left hW hlocalW).resolve_left hne).symm

/-- F.9.5(2) on the literal quotient U_H/V₁ and its original quotient map. -/
theorem commutator_image_eq_seed
    (hi : D.Vplus.relIndex D.V = 2) (hn : ¬ D.V ≤ D.QH)
    [(D.V₁.subgroupOf D.UH).Normal] :
    ((⁅D.UH,D.V⁆).subgroupOf D.UH).map (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)) =
      (D.Vplus.subgroupOf D.UH).map (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)) := by
  have hZU : D.V₁ ≤ D.UH := h.point_lt.le.trans (le_conjugateSpanBy _ _)
  have hCU : ⁅D.UH,D.V⁆ ≤ D.UH := le_normalizer_iff_commutator_le_left.mp
    (h.V_le_H.trans (le_normalizer_conjugateSpanBy D.Vplus D.H))
  let q := QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
  have hz : (D.V₁.subgroupOf D.UH).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  have he := congrArg (fun A : Subgroup G => (A.subgroupOf D.UH).map q)
    (h.seed_eq_point_sup_commutator hi hn)
  rw [subgroupOf_sup hZU hCU,Subgroup.map_sup,hz,bot_sup_eq] at he
  exact he.symm

end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
