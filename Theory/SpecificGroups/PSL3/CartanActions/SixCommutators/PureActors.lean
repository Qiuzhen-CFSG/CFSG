module

public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.Parameters
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.Actors
public import Theory.GroupAction.OddCommutatorImage

/-!
# Pure field, graph and mixed commutators in SL₃ and PSL₃ over 64 elements

Apply each literal coefficient or graph-field automorphism to the diagonal
matrix with parameters (u,1). Its displacement is exactly the parameter
witness from `Parameters`. The resulting subgroup has odd order and is
contained in the cyclic action commutator, so it injects modulo the two-core.
This proves the required lower bound for all pure nontrivial field actors and
all pure graph-field actors, including graph alone.

No assumption on the order of the actor or on fixation of the residual torus
is used. General inner and diagonal twists require the separate Borel quotient
action calculation; these pure-actor results do not assert that reduction.
Source: Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions.BorelQuotient
open Theory.GroupAction.OddCommutatorImage
namespace Matrix.PSL3.CartanActions.SixCommutators
variable (F : Type*) [Field F]

noncomputable def projectiveTorusInclusion :
    ((Fˣ × Fˣ) ⧸ cubicScalars F) →* PSL(3,F) :=
  (torus F).subtype.comp (torusEquiv F).toMonoidHom

theorem projectiveTorusInclusion_injective : Function.Injective (projectiveTorusInclusion F) :=
  Subtype.val_injective.comp (torusEquiv F).injective

@[simp] theorem projectiveTorusInclusion_mk (d : Fˣ × Fˣ) :
    projectiveTorusInclusion F (QuotientGroup.mk d) = torusMap F d := rfl

private theorem card_range_comp {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : Y →* Z) (hg : Function.Injective g) :
    Nat.card (g.comp f).range = Nat.card f.range := by
  rw [MonoidHom.range_comp]
  exact Nat.card_congr (equivMapOfInjective f.range g hg).toEquiv.symm

private theorem bound_of_witness {D : Type*} [Group D] [Finite D]
    (hF : Nat.card F = 2 ^ 6) (C : Subgroup D) (w : Fˣ →* D)
    (hw : ∀ u, w u ∈ C) (hcard : 3 < Nat.card w.range) :
    3 < Nat.card (C ⧸ pCore 2 C) := by
  have hodd : Odd (Nat.card Fˣ) := by rw [Nat.card_units,hF]; decide
  exact hcard.trans_le (odd_subgroup_card_le_quotient_twoCore w.range C
    (by rintro _ ⟨u,rfl⟩; exact hw u) (hodd.of_dvd_nat (card_range_dvd w)))

theorem special_field_witness (σ : F ≃+* F) (u : Fˣ) :
    torusSL F (fieldWitness F σ u) =
      (torusSL F (u,1))⁻¹ * Atlas.fieldEquivSL 3 σ (torusSL F (u,1)) := by
  rw [field_torusSL, ← map_inv, ← map_mul]
  congr 1
  ext <;> simp [fieldWitness,firstCoordinate,FiniteField.BinaryTorusInvolution.displacement,
    mul_comm]

theorem projective_field_witness (σ : F ≃+* F) (u : Fˣ) :
    projectiveTorusInclusion F (projectiveFieldWitness F σ u) =
      (torusMap F (u,1))⁻¹ * fieldAction F σ (torusMap F (u,1)) := by
  change torusMap F (fieldWitness F σ u) = _
  rw [field_torusMap, ← map_inv, ← map_mul]
  congr 1
  ext <;> simp [fieldWitness,firstCoordinate,FiniteField.BinaryTorusInvolution.displacement,
    mul_comm]

theorem special_graph_witness (σ : F ≃+* F) (u : Fˣ) :
    torusSL F (graphWitness F σ u) =
      (torusSL F (u,1))⁻¹ *
        (Atlas.fieldEquivSL 3 σ * oppositionGraphSL F) (torusSL F (u,1)) := by
  rw [MulAut.mul_apply, oppositionGraphSL_torusSL, field_torusSL, ← map_inv, ← map_mul]
  congr 1
  ext <;> simp [graphWitness]

theorem projective_graph_witness (σ : F ≃+* F) (u : Fˣ) :
    projectiveTorusInclusion F (projectiveGraphWitness F σ u) =
      (torusMap F (u,1))⁻¹ *
        (fieldAction F σ * oppositionGraph F) (torusMap F (u,1)) := by
  change torusMap F (graphWitness F σ u) = _
  rw [MulAut.mul_apply, oppositionGraph_torusMap, field_torusMap, ← map_inv, ← map_mul]
  congr 1
  ext <;> simp [graphWitness]

variable [Finite F] [CharP F 2]

theorem special_pure_field_bound (σ : F ≃+* F) (hF : Nat.card F = 2 ^ 6)
    (hσ : σ ≠ 1) :
    let C := commutatorSubgroup (zpowers (Atlas.fieldEquivSL 3 σ)) SL(3,F) (borelSL F)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  let w := (torusSL F).comp (fieldWitness F σ)
  apply bound_of_witness F hF _ w
  · intro u
    change torusSL F (fieldWitness F σ u) ∈ _
    rw [special_field_witness]
    exact generator_displacement_mem (borelSL F) _
      ⟨torusSL F (u,1),torusSL_mem_borel F (u,1)⟩
  · rw [card_range_comp _ _ (torusSL_injective F)]
    exact lt_of_lt_of_le (by decide : 3 < 9) (card_fieldWitness_ge F σ hF hσ)

theorem projective_pure_field_bound (σ : F ≃+* F) (hF : Nat.card F = 2 ^ 6)
    (hσ : σ ≠ 1) :
    let C := commutatorSubgroup (zpowers (fieldAction F σ)) PSL(3,F) (borel F)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  let w := (projectiveTorusInclusion F).comp (projectiveFieldWitness F σ)
  apply bound_of_witness F hF _ w
  · intro u
    change projectiveTorusInclusion F (projectiveFieldWitness F σ u) ∈ _
    rw [projective_field_witness]
    exact generator_displacement_mem (borel F) _
      ⟨torusMap F (u,1),torus_le_borel F ⟨(u,1),rfl⟩⟩
  · rw [card_range_comp _ _ (projectiveTorusInclusion_injective F)]
    exact lt_of_lt_of_le (by decide : 3 < 9) (card_projectiveFieldWitness_ge F σ hF hσ)

omit [CharP F 2] in
theorem special_pure_graph_bound (σ : F ≃+* F) (hF : Nat.card F = 2 ^ 6) :
    let α := Atlas.fieldEquivSL 3 σ * oppositionGraphSL F
    let C := commutatorSubgroup (zpowers α) SL(3,F) (borelSL F)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  let w := (torusSL F).comp (graphWitness F σ)
  apply bound_of_witness F hF _ w
  · intro u
    change torusSL F (graphWitness F σ u) ∈ _
    rw [special_graph_witness]
    exact generator_displacement_mem (borelSL F) _
      ⟨torusSL F (u,1),torusSL_mem_borel F (u,1)⟩
  · rw [card_range_comp _ _ (torusSL_injective F),card_graphWitness F σ hF]
    decide

omit [CharP F 2] in
theorem projective_pure_graph_bound (σ : F ≃+* F) (hF : Nat.card F = 2 ^ 6) :
    let α := fieldAction F σ * oppositionGraph F
    let C := commutatorSubgroup (zpowers α) PSL(3,F) (borel F)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  let w := (projectiveTorusInclusion F).comp (projectiveGraphWitness F σ)
  apply bound_of_witness F hF _ w
  · intro u
    change projectiveTorusInclusion F (projectiveGraphWitness F σ u) ∈ _
    rw [projective_graph_witness]
    exact generator_displacement_mem (borel F) _
      ⟨torusMap F (u,1),torus_le_borel F ⟨(u,1),rfl⟩⟩
  · rw [card_range_comp _ _ (projectiveTorusInclusion_injective F)]
    exact lt_of_lt_of_le (by decide : 3 < 21) (card_projectiveGraphWitness_ge F σ hF)
end Matrix.PSL3.CartanActions.SixCommutators
