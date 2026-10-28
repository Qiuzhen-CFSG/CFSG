module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.Triangles
public import Theory.SpecificGroups.SL2.CubicGeometry

/-!
# The opposite cubic selected in the original SL₂(3) factor

The first quaternion support and its actual cubic axis generate SL₂(3).
The second factor centralizes it, and the marked rotation acts as an
involution on its three other cubic subgroups. An involution on three
objects fixes one. Consequently one other cubic is normalized by the
entire original order-48 complement. This is the source selection of
the opposite point in the proof of Asc94 45.10, p.248.
-/

public section
private theorem fixed_of_involutive_card_three {α : Type*} [Finite α]
    (hc : Nat.card α = 3) (f : α → α) (hf : Function.Involutive f) :
    ∃ a, f a = a := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let e : α ≃ Fin 3 := Fintype.equivFinOfCardEq (by rwa [← Nat.card_eq_fintype_card])
  let F : α ≃ α := ⟨f, f, hf, hf⟩
  let q : Equiv.Perm (Fin 3) := e.symm.trans (F.trans e)
  have hq : q ^ 2 = 1 := by
    apply Equiv.ext
    intro i
    change e (f (e.symm (e (f (e.symm i))))) = i
    rw [e.symm_apply_apply, hf, e.apply_symm_apply]
  have hh : ∀ q : Equiv.Perm (Fin 3), q ^ 2 = 1 → ∃ i, q i = i := by decide
  obtain ⟨i, hi⟩ := hh q hq
  refine ⟨e.symm i, e.injective ?_⟩
  exact hi.trans (e.apply_symm_apply i).symm

open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

@[expose] noncomputable def oppositeFactor : Subgroup G :=
  h.toCentralizerHypothesis.factorData.leftCore ⊔ c.W

theorem oppositeFactor_model :
    Nonempty (c.oppositeFactor ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  let d := h.toCentralizerHypothesis.factorData
  have hB : Nonempty (d.leftCore ≃* QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  exact (quaternion_cubic_extension_recognition d.leftCore hB (c.actors.x : G)
    c.actors.x_order (c.actors.actionB c.actors.x) (c.actors.actionB_apply c.actors.x)
    c.actors.x_actionB_ne_one).1

omit [Finite G] in
theorem oppositeFactor_card : Nat.card c.oppositeFactor = 24 := by
  let d := h.toCentralizerHypothesis.factorData
  have hB : Nat.card d.leftCore = 8 := by
    change Nat.card (pCoreIn 2 d.left) = 8
    rw [Nat.card_congr (Factors.factorCoreEquiv d.left d.left_model.some).toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  change Nat.card (d.leftCore ⊔ c.W : Subgroup G) = 24
  rw [card_sup_eq_mul_of_normalizes_of_disjoint d.leftCore c.W
    (zpowers_le.mpr (c.actors.normalizes_left c.actors.x.property))
    (disjoint_of_coprime_natCard (by rw [hB, c.line_card]; decide)), hB, c.line_card]

omit [Finite G] in
theorem involution_mem_oppositeFactor : z ∈ c.oppositeFactor := by
  apply mem_sup_left
  exact (h.toCentralizerHypothesis.factorData.core_intersection h.involution ▸ mem_zpowers z).1

omit [Finite G] in
theorem oppositeFactor_le_fixed : c.oppositeFactor ≤ centralizer z := by
  let d := h.toCentralizerHypothesis.factorData
  exact sup_le ((pCoreIn_le 2 d.left).trans (d.left_le.trans (map_subtype_le _))) c.line_le_fixed

omit [Finite G] in
theorem special_centralizes_oppositeFactor : c.J ≤ Subgroup.centralizer (c.oppositeFactor : Set G) := by
  let d := h.toCentralizerHypothesis.factorData
  have hc : ∀ b ∈ d.leftCore, ∀ a ∈ d.rightCore, b * a = a * b := fun b hb a ha =>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) a (pCoreIn_le 2 d.right ha)
  have hJB : c.J ≤ Subgroup.centralizer (d.leftCore : Set G) := sup_le
    (fun a ha b hb => hc b hb a ha) (zpowers_le.mpr c.actors.y_centralizes)
  have hJW : c.J ≤ Subgroup.centralizer (c.W : Set G) := by
    apply sup_le
    · exact le_centralizer_iff.mp (zpowers_le.mpr c.actors.x_centralizes)
    · rw [le_centralizer_iff, zpowers_le]
      intro y hy
      exact mem_centralizer_singleton_iff.mp
        ((zpowers_le.mpr (mem_centralizer_singleton_iff.mpr c.actors.commute.symm.eq)) hy)
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp hJB) (le_centralizer_iff.mp hJW)

theorem rotation_normalizes_oppositeFactor :
    c.marking.s * c.marking.t ∈ normalizer (c.oppositeFactor : Set G) := by
  let d := h.toCentralizerHypothesis.factorData
  let r := c.marking.s * c.marking.t
  have hB : Nonempty (d.leftCore ≃* QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.left d.left_model.some⟩
  have hC : Nonempty (d.rightCore ≃* QuaternionGroup 2) :=
    ⟨Factors.factorCoreEquiv d.right d.right_model.some⟩
  have hi : Nat.card (d.leftCore ⊓ d.rightCore : Subgroup G) = 2 := by
    rw [d.core_intersection h.involution, Nat.card_zpowers, h.involution]
  have hc : ∀ b ∈ d.leftCore, ∀ a ∈ d.rightCore, b * a = a * b := fun b hb a ha =>
    d.factors_commute h.involution b (pCoreIn_le 2 d.left hb) a (pCoreIn_le 2 d.right ha)
  have hr : r ∈ normalizer ((d.leftCore ⊔ d.rightCore : Subgroup G) : Set G) := by
    rw [d.core_span h.involution]
    exact CentralizerHypothesis.centralizer_normalizes_core c.marking.rotation_centralizes
  have hinv : ∀ x ∈ c.actors.A, r * x * r⁻¹ = x⁻¹ := by
    rw [c.actors_eq]
    exact c.marking.rotation_inverts
  have hrB := (c.actors.normalizes_factors_of_inversion hB hC hi hc r hr hinv).1
  have hrW : r ∈ normalizer (c.W : Set G) :=
    (c.complement_le (mem_sup_right (mem_zpowers r))).2
  exact normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hrB, hrW⟩

/-- The original complement preserves a second cubic in the actual SL₂(3). -/
theorem exists_complement_fixed_opposite_cubic :
    ∃ Y : Subgroup G, Y ≤ c.oppositeFactor ∧ Nat.card Y = 3 ∧ Y ≠ c.W ∧
      c.W ⊔ Y = c.oppositeFactor ∧ c.K ≤ normalizer (Y : Set G) := by
  classical
  let L := c.oppositeFactor
  let r := c.marking.s * c.marking.t
  let S := {Y : Subgroup G // Y ≤ L ∧ Nat.card Y = 3 ∧ Y ≠ c.W}
  have hgeom := SL23CubicGeometry.geometry_of_equiv L c.W c.oppositeFactor_model.some
    le_sup_right c.line_card
  have hrL : L.conjBy r = L := mem_normalizer_iff_map_conj_eq.mp c.rotation_normalizes_oppositeFactor
  have hrW : c.W.conjBy r = c.W := mem_normalizer_iff_map_conj_eq.mp
    ((c.complement_le (mem_sup_right (mem_zpowers r))).2)
  let f : S → S := fun Y => ⟨Y.val.conjBy r,
    (map_mono Y.property.1).trans_eq hrL,
    (card_map_of_injective (MulAut.conj r).injective).trans Y.property.2.1,
    fun he => Y.property.2.2 (map_injective (MulAut.conj r).injective (he.trans hrW.symm))⟩
  have hf : Function.Involutive f := by
    intro Y
    apply Subtype.ext
    change (Y.val.conjBy r).conjBy r = Y.val
    rw [conjBy_conjBy, ← pow_two, c.marking.rotation_square]
    apply mem_normalizer_iff_map_conj_eq.mp
    apply centralizer_le_normalizer _
    intro y hy
    exact mem_centralizer_singleton_iff.mp (c.oppositeFactor_le_fixed (Y.property.1 hy))
  obtain ⟨Y, hY⟩ := fixed_of_involutive_card_three hgeom.1 f hf
  have hrY : r ∈ normalizer (Y.val : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (congrArg Subtype.val hY)
  refine ⟨Y.val, Y.property.1, Y.property.2.1, Y.property.2.2, hgeom.2.1 Y, ?_⟩
  exact sup_le ((c.special_centralizes_oppositeFactor.trans (centralizer_le Y.property.1)).trans
    (centralizer_le_normalizer _)) (zpowers_le.mpr hrY)

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
