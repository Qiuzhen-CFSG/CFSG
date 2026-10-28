module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements

/-!
# Transport of the exact M₂₄ table shapes

A group isomorphism transports embedded dihedral factors, their intersections,
commutation and generation, then the normal kernel and its quotient. Exact
sequences are transported by composing their inclusion and projection maps.
No splitting or centralizer structure is inferred from cardinalities.

Source convention: Aschbacher–Smith E.2.16, p.228, and 16.1.5(7), p.1171.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
open Subgroup

/-- Transport the two embedded dihedral factors. -/
theorem IsDihedralSquareProduct.map {C D : Type*} [Group C] [Group D]
    (h : IsDihedralSquareProduct C) (e : C ≃* D) : IsDihedralSquareProduct D := by
  obtain ⟨B, A, hB, hA, hi, hc, hs⟩ := h
  refine ⟨B.map e.toMonoidHom, A.map e.toMonoidHom,
    hB.map (fun f => (e.subgroupMap B).symm.trans f),
    hA.map (fun f => (e.subgroupMap A).symm.trans f), ?_, ?_, ?_⟩
  · rw [← map_inf _ _ _ e.injective, card_map_of_injective e.injective]
    exact hi
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨a, ha, rfl⟩
    exact (e.map_mul b a).symm.trans ((congrArg e (hc b hb a ha)).trans (e.map_mul a b))
  · rw [← Subgroup.map_sup, hs, Subgroup.map_top_of_surjective _ e.surjective]

/-- Transport the central product of three dihedral eights. -/
theorem IsDihedralCubeProduct.map {C D : Type*} [Group C] [Group D]
    (h : IsDihedralCubeProduct C) (e : C ≃* D) : IsDihedralCubeProduct D := by
  obtain ⟨B, A, hB, hA, hi, hc, hs⟩ := h
  refine ⟨B.map e.toMonoidHom, A.map e.toMonoidHom,
    hB.map (e.subgroupMap B), hA.map (fun f => (e.subgroupMap A).symm.trans f), ?_, ?_, ?_⟩
  · rw [← map_inf _ _ _ e.injective, card_map_of_injective e.injective]
    exact hi
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨a, ha, rfl⟩
    exact (e.map_mul b a).symm.trans ((congrArg e (hc b hb a ha)).trans (e.map_mul a b))
  · rw [← Subgroup.map_sup, hs, Subgroup.map_top_of_surjective _ e.surjective]

/-- Transport the actual normal kernel and the L₃(2) quotient. -/
theorem IsM24DihedralExtension.map {C D : Type*} [Group C] [Group D]
    (h : IsM24DihedralExtension C) (e : C ≃* D) : IsM24DihedralExtension D := by
  obtain ⟨Q, hn, hQ, ⟨f⟩⟩ := h
  let := hn
  let hN := hn.map e.toMonoidHom e.surjective
  exact ⟨Q.map e.toMonoidHom, hN, hQ.map (e.subgroupMap Q),
    ⟨(QuotientGroup.congr Q (Q.map e.toMonoidHom) e rfl).symm.trans f⟩⟩

/-- Transport the middle group of an exact extension. -/
def extensionTransport {N C D Q : Type*} [Group N] [Group C] [Group D] [Group Q]
    (s : GroupExtension N C Q) (e : C ≃* D) : GroupExtension N D Q where
  inl := e.toMonoidHom.comp s.inl
  rightHom := s.rightHom.comp e.symm.toMonoidHom
  inl_injective := e.injective.comp s.inl_injective
  rightHom_surjective := s.rightHom_surjective.comp e.symm.surjective
  range_inl_eq_ker_rightHom := by
    ext d
    constructor
    · rintro ⟨n, rfl⟩
      change s.rightHom (e.symm (e (s.inl n))) = 1
      rw [e.symm_apply_apply]
      exact show s.inl n ∈ s.rightHom.ker from
        s.range_inl_eq_ker_rightHom ▸ ⟨n, rfl⟩
    · intro hd
      have hm : e.symm d ∈ s.inl.range := by
        rw [s.range_inl_eq_ker_rightHom]
        exact hd
      obtain ⟨n, hn⟩ := hm
      exact ⟨n, (congrArg e hn).trans (e.apply_symm_apply d)⟩

end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
