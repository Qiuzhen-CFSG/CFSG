module
public import CFSG.Quasithin.ChapterF.Section08.TrackSetup
public import Theory.GroupTheory.IrreducibleSectionCore

/-!
# Odd critical distance in F.8

The edge two-core centralizes V/V₁ by irreducibility. At an even critical
vertex, F.7.9 places V in the conjugate edge core, whereas F.7.11 gives a
nontrivial commutator inside V. Hence V meets the conjugate point nontrivially;
F.8.1(a) kills that commutator. Together with b>1 this proves F.8.5.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.8.5,
printed pp.316–317.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section08.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
namespace Hypothesis
variable (h : D.Hypothesis)
include h
open Theory.GroupTheory

/-- Irreducibility in F.8.1(b) makes the edge two-core act trivially on V/V₁. -/
theorem edgeCore_commutator_le_point : ⁅D.V, (D.L₁ ⊔ D.T).pCoreIn 2⁆ ≤ D.V₁ := by
  let A := D.L₁ ⊔ D.T
  have hVA : D.V ≤ A := h.V_le_T.trans le_sup_right
  have hNA : D.V₁ ≤ A := h.point_le.trans hVA
  have hAV : A ≤ normalizer (D.V : Set G) :=
    h.normalizer_point_LT_eq.symm.le.trans (inf_le_left.trans h.LT_normalizes_V)
  let : (D.V.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hAV
  let : (D.V₁.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer
    (h.local_le.trans h.H_le)
  have hirr (E : Subgroup A) (hNE : D.V₁.subgroupOf A ≤ E)
      (hEV : E ≤ D.V.subgroupOf A) (hn : E.Normal) :
      E = D.V₁.subgroupOf A ∨ E = D.V.subgroupOf A := by
    have hNm : D.V₁ ≤ E.map A.subtype := by
      rw [← map_subgroupOf_eq_of_le hNA]
      exact map_mono hNE
    have hVm : E.map A.subtype ≤ D.V := by
      simpa only [map_subgroupOf_eq_of_le hVA] using map_mono (f := A.subtype) hEV
    have hnorm : A ≤ normalizer (E.map A.subtype : Set G) := by
      apply le_normalizer_iff.mpr
      rintro a ha _ ⟨x, hx, rfl⟩
      exact ⟨⟨a, ha⟩ * x * ⟨a, ha⟩⁻¹, hn.conj_mem x hx ⟨a, ha⟩, rfl⟩
    rcases h.irreducible (E.map A.subtype) hNm hVm hnorm with he | he
    · left
      apply map_injective A.subtype_injective
      simpa only [map_subgroupOf_eq_of_le hNA] using he
    · right
      apply map_injective A.subtype_injective
      simpa only [map_subgroupOf_eq_of_le hVA] using he
  let := h.elementary
  have hc := commutator_pCore_le_of_irreducible_section
    (D.V₁.subgroupOf A) (D.V.subgroupOf A) (comap_mono h.point_le)
    (IsElementaryAbelian.isPGroup 2 D.V).comap_subtype hirr
  have hm := map_mono (f := A.subtype) hc
  rwa [map_commutator, map_subgroupOf_eq_of_le hVA, map_subgroupOf_eq_of_le hNA] at hm

/-- Clause (a) in the conjugate orientation needed at a critical edge. -/
theorem conjugate_point_intersection_commute (g : G)
    (hne : D.V ⊓ D.V₁.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅D.V, D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hn : D.V₁ ⊓ ChapterG.Section02.Setup.conjugate D.V g ≠ ⊥ := by
    intro hz
    have hh := congrArg (map (MulAut.conj g).toMonoidHom) hz
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, Subgroup.map_bot] at hh
    have hi : (ChapterG.Section02.Setup.conjugate D.V g).map
        (MulAut.conj g).toMonoidHom = D.V := by
      rw [ChapterG.Section02.Setup.conjugate, map_map]
      have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
          MonoidHom.id G := by ext x; simp [MulAut.conj_apply, mul_assoc]
      rw [he, map_id]
    rw [hi, inf_comm] at hh
    exact hne hh
  have hh := congrArg (map (MulAut.conj g).toMonoidHom) (h.conjugates_commute g hn)
  rw [map_commutator, Subgroup.map_bot, ChapterG.Section02.Setup.conjugate,
    map_map] at hh
  have hi : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by ext x; simp [MulAut.conj_apply, mul_assoc]
  rw [hi, map_id, commutator_comm] at hh
  exact hh
end Hypothesis
end CFSG.Quasithin.ChapterF.Section08.Setup

namespace CFSG.Quasithin.ChapterF.Section08.Setup
open Section07 Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (stabilizer_base)
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
namespace Hypothesis
variable (h : D.Hypothesis)
include h

omit h [Finite G] in
private theorem map_conj_generated (A : Subgroup (D.LT ⊔ D.H : Subgroup G))
    (g : (D.LT ⊔ D.H : Subgroup G)) :
    (A.map (MulAut.conj g).toMonoidHom).map (D.LT ⊔ D.H).subtype =
      (A.map (D.LT ⊔ D.H).subtype).map (MulAut.conj (g : G)).toMonoidHom := by
  rw [map_map, map_map]
  rfl

/-- F.8.5(1): an even critical pair contradicts the original intersection clause. -/
theorem odd_b : Odd h.b := by
  apply (Nat.even_or_odd h.b).resolve_left
  intro heven
  let F := family (D := D)
  let S := h.f7Setup
  obtain ⟨v, hd, hcrit⟩ := (S.critical_witness h.f7V_ne_bot).1
  have hv : v.type = false := CriticalPairs.even_endpoint_type F S h.f7V_ne_bot hd heven
  have hne : base F false ≠ v := by
    intro he
    rw [← he, SimpleGraph.dist_self] at hd
    have := h.one_lt_b
    change 1 < S.track h.f7V_ne_bot at this
    omega
  obtain ⟨w, hAdj, hpre⟩ := exists_predecessor F S.generates (base F false) v hne
  have hw : w.type = true := by
    have ht := hAdj.1
    rw [hv] at ht
    cases hh : w.type <;> simp_all
  obtain ⟨g, hgv, hgw⟩ := incident_common_translate F hAdj.2
  rw [hv] at hgv
  rw [hw] at hgw
  change (graph F).dist (base F false) v = S.track h.f7V_ne_bot at hd
  have hEdge := (S.below_track h.f7V_ne_bot (v := w) (by change (graph F).dist (base F false) w < S.track h.f7V_ne_bot; omega) hAdj.symm).2
  have hEdgeMap :
      (stabilizer F w ⊓ stabilizer F v).map (D.LT ⊔ D.H).subtype =
        (D.L₁ ⊔ D.T).map (MulAut.conj (g : G)).toMonoidHom := by
    rw [← hgw, ← hgv, stabilizer_translate, stabilizer_translate,
      show stabilizer F (base F true) = F true from stabilizer_base F true,
      show stabilizer F (base F false) = F false from stabilizer_base F false,
      ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      map_conj_generated, Subgroup.map_inf _ _ _ (D.LT ⊔ D.H).subtype_injective]
    rw [show (F true).map (D.LT ⊔ D.H).subtype = D.H from
      map_subgroupOf_eq_of_le le_sup_right,
      show (F false).map (D.LT ⊔ D.H).subtype = D.LT from
      map_subgroupOf_eq_of_le le_sup_left,
      inf_comm, h.LT_inf_H_eq]
  have hVc : D.V ≤ ((D.L₁ ⊔ D.T).pCoreIn 2).map
      (MulAut.conj (g : G)).toMonoidHom := by
    have hh := map_mono (f := (D.LT ⊔ D.H).subtype) hEdge
    rw [h.f7Seed_map,
      ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _
        (D.LT ⊔ D.H).subtype_injective,
      hEdgeMap, Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _
        (MulAut.conj (g : G)).injective] at hh
    exact hh
  have hVm : (CriticalPairs.vertexModule F S.seed v).map (D.LT ⊔ D.H).subtype =
      D.V.map (MulAut.conj (g : G)).toMonoidHom := by
    rw [← hgv, CriticalPairs.vertexModule_translate_base F S.seed S.seed_normalized,
      map_conj_generated, h.f7Seed_map]
  have hc : ⁅D.V, D.V.map (MulAut.conj (g : G)).toMonoidHom⁆ ≤
      D.V₁.map (MulAut.conj (g : G)).toMonoidHom := by
    apply (commutator_mono hVc le_rfl).trans
    rw [← map_commutator, commutator_comm]
    exact map_mono h.edgeCore_commutator_le_point
  have hnon : ⁅D.V, D.V.map (MulAut.conj (g : G)).toMonoidHom⁆ ≠ ⊥ := by
    have hh := CriticalPairs.even_pair_commutator_ne_bot F S h.f7V_ne_bot hd heven hcrit
    intro hz
    apply hh
    apply (map_eq_bot_iff_of_injective _ (D.LT ⊔ D.H).subtype_injective).mp
    rwa [map_commutator, h.f7Seed_map, hVm]
  have hleft : ⁅D.V, D.V.map (MulAut.conj (g : G)).toMonoidHom⁆ ≤ D.V := by
    have hh := map_mono (f := (D.LT ⊔ D.H).subtype)
      ((CriticalPairs.even_pair_containments F S h.f7V_ne_bot hd heven).2.trans inf_le_left)
    rwa [map_commutator, h.f7Seed_map, hVm] at hh
  have hn : D.V ⊓ D.V₁.map (MulAut.conj (g : G)).toMonoidHom ≠ ⊥ := by
    intro hz
    exact hnon (eq_bot_iff.mpr ((le_inf hleft hc).trans hz.le))
  exact hnon (h.conjugate_point_intersection_commute (g : G) hn)

/-- Both assertions of source F.8.5 on the constructed original track. -/
theorem lemma_F_8_5 : 3 ≤ h.b ∧ Odd h.b ∧ IsElementaryAbelian 2 D.U := by
  have ho := h.odd_b
  have hb := h.one_lt_b
  refine ⟨?_, ho, lemma_F_8_5_two h⟩
  obtain ⟨k, hk⟩ := ho
  omega

end Hypothesis
end CFSG.Quasithin.ChapterF.Section08.Setup

