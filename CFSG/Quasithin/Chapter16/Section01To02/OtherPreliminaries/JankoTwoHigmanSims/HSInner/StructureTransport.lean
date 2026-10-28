module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements

/-!
# Transport of the exact HS core extension

Transport both embedded quaternion factors, the cyclic factor, and the normal
quotient along group isomorphisms. This preserves the common intersections,
commutation and generation in (Q₈ * Q₈) * C₄ without asserting a splitting.
The factor orders also give order 64 for the kernel and 7680 for the extension.

This is the change-of-representative step for Aschbacher–Smith 16.1.5(10),
printed p.1172. It does not construct the representative extension.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open Subgroup

/-- Carry the two embedded quaternion factors along a group isomorphism. -/
noncomputable def quaternionTransport {C D : Type*} [Group C] [Group D]
    (e : C ≃* D) (d : QuaternionCentralProductData C) : QuaternionCentralProductData D where
  left := d.left.map e.toMonoidHom
  right := d.right.map e.toMonoidHom
  left_model := d.left_model.map (fun f => (e.subgroupMap d.left).symm.trans f)
  right_model := d.right_model.map (fun f => (e.subgroupMap d.right).symm.trans f)
  intersection_card := by
    rw [← Subgroup.map_inf _ _ _ e.injective, Subgroup.card_map_of_injective e.injective]
    exact d.intersection_card
  commute := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (e.map_mul a b).symm.trans
      ((congrArg e (d.commute a ha b hb)).trans (e.map_mul b a))
  span := by rw [← Subgroup.map_sup, d.span, Subgroup.map_top_of_surjective _ e.surjective]

/-- Carry the embedded quaternion and cyclic factors along a group isomorphism. -/
theorem shape_transport {C D : Type*} [Group C] [Group D]
    (e : C ≃* D) (h : IsQuaternionSquareCyclicFourProduct C) :
    IsQuaternionSquareCyclicFourProduct D := by
  obtain ⟨B, Z, ⟨hB⟩, hZ, hBZ, hc, hs⟩ := h
  refine ⟨B.map e.toMonoidHom, Z.map e.toMonoidHom,
    ⟨quaternionTransport (e.subgroupMap B) hB⟩,
    hZ.map (fun f => (e.subgroupMap Z).symm.trans f), ?_, ?_, ?_⟩
  · rw [← Subgroup.map_inf _ _ _ e.injective, Subgroup.card_map_of_injective e.injective]
    exact hBZ
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨z, hz, rfl⟩
    exact (e.map_mul b z).symm.trans
      ((congrArg e (hc b hb z hz)).trans (e.map_mul z b))
  · rw [← Subgroup.map_sup, hs, Subgroup.map_top_of_surjective _ e.surjective]

/-- Isomorphisms preserve the exact embedded central product and normal quotient. -/
theorem coreExtension_transport {C D : Type*} [Group C] [Group D]
    (e : C ≃* D) (h : IsHSCoreExtension C) : IsHSCoreExtension D := by
  obtain ⟨Q, hQ, hshape, ⟨hq⟩⟩ := h
  let := hQ
  let Q' := Q.map e.toMonoidHom
  let : Q'.Normal := hQ.map e.toMonoidHom e.surjective
  exact ⟨Q', inferInstance, shape_transport (e.subgroupMap Q) hshape,
    ⟨(QuotientGroup.congr Q Q' e rfl).symm.trans hq⟩⟩

/-- The embedded source kernel has order 64. -/
theorem shape_card {C : Type*} [Group C] [Finite C]
    (h : IsQuaternionSquareCyclicFourProduct C) : Nat.card C = 64 := by
  obtain ⟨B, D, ⟨hB⟩, ⟨eD⟩, hBD, hc, hs⟩ := h
  have hBcard : Nat.card B = 32 := hB.card
  have hDcard : Nat.card D = 4 := by
    rw [Nat.card_congr eD.toEquiv]
    simp [C4]
  have hn : D ≤ normalizer (B : Set C) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro d hd b hb
    exact hc b hb d hd
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes B D hn
  rw [hBcard, hDcard, hBD, hs,
    Nat.card_congr (topEquiv : (⊤ : Subgroup C) ≃* C).toEquiv] at hh
  omega

/-- The exact source extension has order 7680, for use in exhaustive class coverage. -/
theorem coreExtension_card {C : Type*} [Group C] [Finite C] (h : IsHSCoreExtension C) :
    Nat.card C = 7680 := by
  obtain ⟨Q, hN, hs, ⟨e⟩⟩ := h
  let := hN
  have hq : Nat.card (C ⧸ Q) = 120 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [S5, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hh := Q.card_mul_index
  rw [shape_card hs, index_eq_card, hq] at hh
  exact hh.symm
end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
