module

public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding.Words
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer.TitsEmbedding.Relations
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.Rudvalis.Model.Primitive
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Mathlib.GroupTheory.Index

/-!
# A presentation route to the Tits subgroup of the Rudvalis stabilizer

The explicit words in `TitsEmbedding.Words` fix 0 and include a nonidentity
element. `TitsEmbedding.Relations` certifies Parrott's 37 relations, so the
resulting homomorphism from the simple presented Tits group is injective. Composing
with the proved equivalence from its Atlas degree-1600 carrier gives an
actual multiplicative equivalence onto the image subgroup. The stabilizer
order 35942400 then gives relative index two by Lagrange's theorem.

The full stabilizer order follows from the Rudvalis order certificate and
transitivity of the degree-4060 action. The final theorem discharges both
inputs of the conditional embedding and requires no additional hypotheses.

Source: GLS3, Table 5.3r, printed p.279, in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. The full stabilizer is ²F₄(2), and its
simple Tits subgroup has index two; it is not the full stabilizer. The
presentation source and concrete word conventions are documented in `Words`.
-/

namespace Rudvalis
open OuterStabilizer.TitsEmbedding

/-- Transitivity converts the model order into the full point-stabilizer order. -/
public theorem OuterStabilizer.TitsEmbedding.stabilizer_card_of_model_card
    (hcard : Nat.card Model = 145926144000) :
    Nat.card (MulAction.stabilizer Model (0 : Fin 4060)) = 35942400 := by
  let := model_isPretransitive
  have hi : (MulAction.stabilizer Model (0 : Fin 4060)).index = 4060 := by
    simpa using MulAction.index_stabilizer_of_transitive Model (0 : Fin 4060)
  have h := (MulAction.stabilizer Model (0 : Fin 4060)).card_mul_index
  rw [hi, hcard] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 4060) h

/-- The explicit relator certificate and full stabilizer order suffice for the
actual index-two Tits embedding. Both premises must be discharged in assembly. -/
public theorem outer_stabilizer_tits_subgroup_of_relations
    (hrel : Tits.SatisfiesParrottRelations assignment)
    (hcard : Nat.card (MulAction.stabilizer Model (0 : Fin 4060)) = 35942400) :
    ∃ K : Subgroup Model, K ≤ MulAction.stabilizer Model (0 : Fin 4060) ∧
      K.relIndex (MulAction.stabilizer Model (0 : Fin 4060)) = 2 ∧
      Nonempty (Tits.Atlas1600Group ≃* K) := by
  let φ := Tits.parrottLift assignment hrel
  have hinj : Function.Injective φ := by
    apply φ.ker_eq_bot_iff.mp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker inferInstance with h | h
    · exact h
    · have hm : Tits.parrottGenerator .r1 ∈ φ.ker := h ▸ Subgroup.mem_top _
      have he : assignment .r1 = 1 := by
        simpa only [MonoidHom.mem_ker, φ, Tits.parrottLift_generator] using hm
      exact (assignment_r1_ne_one he).elim
  let e : Tits.Atlas1600Group ≃* φ.range :=
    Tits.parrottFiniteImageEquiv.symm.trans (MonoidHom.ofInjective hinj)
  have hle : φ.range ≤ MulAction.stabilizer Model (0 : Fin 4060) := by
    rw [Tits.parrottLift_range]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact assignment_mem_stabilizer i
  refine ⟨φ.range, hle, ?_, ⟨e⟩⟩
  have hk : Nat.card φ.range = 17971200 :=
    (Nat.card_congr e.toEquiv).symm.trans Tits.atlas1600Group_card
  have hsub : Nat.card (φ.range.subgroupOf (MulAction.stabilizer Model (0 : Fin 4060))) =
      Nat.card φ.range := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hm := (φ.range.subgroupOf (MulAction.stabilizer Model (0 : Fin 4060))).card_mul_index
  rw [hsub, hk, hcard] at hm
  change 17971200 * φ.range.relIndex (MulAction.stabilizer Model (0 : Fin 4060)) = 35942400 at hm
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 17971200) hm

/-- The stabilizer of 0 in the concrete Rudvalis model contains an index-two
subgroup isomorphic to the concrete degree-1600 Tits group. -/
public theorem outer_stabilizer_tits_subgroup :
    ∃ K : Subgroup Model, K ≤ MulAction.stabilizer Model (0 : Fin 4060) ∧
      K.relIndex (MulAction.stabilizer Model (0 : Fin 4060)) = 2 ∧
      Nonempty (Tits.Atlas1600Group ≃* K) :=
  outer_stabilizer_tits_subgroup_of_relations assignment_relations
    (stabilizer_card_of_model_card model_card)

end Rudvalis
