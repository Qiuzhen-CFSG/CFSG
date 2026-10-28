module

public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.QuotientActions
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.Reduction
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.Parameters
public import Theory.GroupAction.OddCommutatorImage

/-!
# Borel commutators with arbitrary linear twists of field and graph actors

The actual Borel quotient maps remove the triangular GL₃ conjugation factor.
Evaluating the displacement of diag(u,u⁻¹,1) therefore gives the same explicit
field or graph-field witness as for a pure actor. Their odd images have orders
at least nine or twenty-one in the projective case. Every map to these odd
quotients kills the two-core of the cyclic action commutator, giving the
strict lower bound three. The actor need not be an involution.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954; GLS3 §2.7.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
open Theory.GroupAction.OddCommutatorImage
namespace Matrix.PSL3.CartanActions.SixCommutators
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

theorem special_twisted_field_bound (hF : Nat.card F = 2 ^ 6)
    (m : GL (Fin 3) F) (σ : F ≃+* F) (hσ : σ ≠ 1)
    (hm : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F)
    (hB : (borelSL F).map (specialActor F m σ false).toMonoidHom = borelSL F) :
    let C := commutatorSubgroup (zpowers (specialActor F m σ false)) SL(3,F) (borelSL F)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  apply (lt_of_lt_of_le (by decide : 3 < 9) (card_fieldWitness_ge F σ hF hσ)).trans_le
  apply card_le_cyclic_commutator_quotient _ _ hB (specialQuotientMap F hF)
    (by rw [Nat.card_prod]; exact (units_odd F hF).mul (units_odd F hF))
  intro u
  let b : borelSL F := ⟨torusSL F (u,1),torusSL_mem_borel F (u,1)⟩
  have ha : specialActor F m σ false b ∈ borelSL F := hB.le (mem_map_of_mem _ b.property)
  refine ⟨b,?_⟩
  have he : (⟨(b : SL(3,F))⁻¹ * specialActor F m σ false b,
      cyclic_commutator_le _ _ hB (generator_displacement_mem _ _ b)⟩ : borelSL F) =
      b⁻¹ * ⟨specialActor F m σ false b,ha⟩ := rfl
  rw [he,map_mul,map_inv]
  have heval : specialQuotientMap F hF ⟨specialActor F m σ false b,ha⟩ =
      (Units.map σ.toMonoidHom u,1) := by
    have hx : specialActor F m σ false b =
        linearConjSL F m (torusSL F (Units.map σ.toMonoidHom u,1)) := by
      simp only [specialActor,Bool.false_eq_true,↓reduceIte,mul_one,MulAut.mul_apply,b,
        field_torusSL,map_one]
    simp_rw [hx]
    exact specialQuotientMap_linear_torus F hF m hm _ _
  rw [heval]
  change fieldWitness F σ u = (specialQuotientMap F hF b)⁻¹ * _
  rw [show specialQuotientMap F hF b = (u,1) from specialQuotientMap_torus F hF _]
  ext <;> simp [fieldWitness,firstCoordinate,FiniteField.BinaryTorusInvolution.displacement,mul_comm]

theorem special_twisted_graph_bound (hF : Nat.card F = 2 ^ 6)
    (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hm : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F)
    (hB : (borelSL F).map (specialActor F m σ true).toMonoidHom = borelSL F) :
    let C := commutatorSubgroup (zpowers (specialActor F m σ true)) SL(3,F) (borelSL F)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  have hc : 3 < Nat.card (graphWitness F σ).range := by rw [card_graphWitness F σ hF]; decide
  apply hc.trans_le
  apply card_le_cyclic_commutator_quotient _ _ hB (specialQuotientMap F hF)
    (by rw [Nat.card_prod]; exact (units_odd F hF).mul (units_odd F hF))
  intro u
  let b : borelSL F := ⟨torusSL F (u,1),torusSL_mem_borel F (u,1)⟩
  have ha : specialActor F m σ true b ∈ borelSL F := hB.le (mem_map_of_mem _ b.property)
  refine ⟨b,?_⟩
  have he : (⟨(b : SL(3,F))⁻¹ * specialActor F m σ true b,
      cyclic_commutator_le _ _ hB (generator_displacement_mem _ _ b)⟩ : borelSL F) =
      b⁻¹ * ⟨specialActor F m σ true b,ha⟩ := rfl
  rw [he,map_mul,map_inv]
  have heval : specialQuotientMap F hF ⟨specialActor F m σ true b,ha⟩ =
      (1,(Units.map σ.toMonoidHom u)⁻¹) := by
    have hx : specialActor F m σ true b =
        linearConjSL F m (torusSL F (1,(Units.map σ.toMonoidHom u)⁻¹)) := by
      simp only [specialActor,↓reduceIte,MulAut.mul_apply,b,
        oppositionGraphSL_torusSL,field_torusSL,inv_one,map_one,map_inv]
    simp_rw [hx]
    exact specialQuotientMap_linear_torus F hF m hm _ _
  rw [heval]
  change graphWitness F σ u = (specialQuotientMap F hF b)⁻¹ * _
  rw [show specialQuotientMap F hF b = (u,1) from specialQuotientMap_torus F hF _]
  ext <;> simp [graphWitness]

omit [CharP F 2] in
private theorem projective_parameters_odd (hF : Nat.card F = 2 ^ 6) :
    Odd (Nat.card ((Fˣ × Fˣ) ⧸ cubicScalars F)) := by
  apply Odd.of_dvd_nat _ (cubicScalars F).index_dvd_card
  rw [Nat.card_prod]
  exact (units_odd F hF).mul (units_odd F hF)

theorem projective_twisted_field_bound (hF : Nat.card F = 2 ^ 6)
    (m : GL (Fin 3) F) (σ : F ≃+* F) (hσ : σ ≠ 1)
    (hm : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F)
    (hB : (borel F).map (projectiveActor F m σ false).toMonoidHom = borel F) :
    let C := commutatorSubgroup (zpowers (projectiveActor F m σ false)) PSL(3,F) (borel F)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  apply (lt_of_lt_of_le (by decide : 3 < 9) (card_projectiveFieldWitness_ge F σ hF hσ)).trans_le
  apply card_le_cyclic_commutator_quotient _ _ hB (projectiveQuotientMap F hF)
    (projective_parameters_odd F hF)
  intro u
  let b : borel F := ⟨torusMap F (u,1),torus_le_borel F ⟨(u,1),rfl⟩⟩
  have ha : projectiveActor F m σ false b ∈ borel F := hB.le (mem_map_of_mem _ b.property)
  refine ⟨b,?_⟩
  have he : (⟨(b : PSL(3,F))⁻¹ * projectiveActor F m σ false b,
      cyclic_commutator_le _ _ hB (generator_displacement_mem _ _ b)⟩ : borel F) =
      b⁻¹ * ⟨projectiveActor F m σ false b,ha⟩ := rfl
  rw [he,map_mul,map_inv]
  have heval : projectiveQuotientMap F hF ⟨projectiveActor F m σ false b,ha⟩ =
      QuotientGroup.mk (Units.map σ.toMonoidHom u,1) := by
    have hx : projectiveActor F m σ false b =
        linearConj F m (torusMap F (Units.map σ.toMonoidHom u,1)) := by
      simp only [projectiveActor,Bool.false_eq_true,↓reduceIte,mul_one,MulAut.mul_apply,b,
        field_torusMap,map_one]
    simp_rw [hx]
    exact projectiveQuotientMap_linear_torus F hF m hm _ _
  rw [heval]
  change projectiveFieldWitness F σ u = (projectiveQuotientMap F hF b)⁻¹ * _
  rw [show projectiveQuotientMap F hF b = QuotientGroup.mk (u,1) from projectiveQuotientMap_torus F hF _]
  change (QuotientGroup.mk' (cubicScalars F)) (fieldWitness F σ u) =
    ((QuotientGroup.mk' (cubicScalars F)) (u,1))⁻¹ *
      (QuotientGroup.mk' (cubicScalars F)) (Units.map σ.toMonoidHom u,1)
  rw [← map_inv,← map_mul]
  congr 1
  ext <;> simp [fieldWitness,firstCoordinate,FiniteField.BinaryTorusInvolution.displacement,mul_comm]

theorem projective_twisted_graph_bound (hF : Nat.card F = 2 ^ 6)
    (m : GL (Fin 3) F) (σ : F ≃+* F)
    (hm : (unipotent F).map (linearConj F m).toMonoidHom = unipotent F)
    (hB : (borel F).map (projectiveActor F m σ true).toMonoidHom = borel F) :
    let C := commutatorSubgroup (zpowers (projectiveActor F m σ true)) PSL(3,F) (borel F)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  have hc : 3 < Nat.card (projectiveGraphWitness F σ).range :=
    lt_of_lt_of_le (by decide : 3 < 21) (card_projectiveGraphWitness_ge F σ hF)
  apply hc.trans_le
  apply card_le_cyclic_commutator_quotient _ _ hB (projectiveQuotientMap F hF)
    (projective_parameters_odd F hF)
  intro u
  let b : borel F := ⟨torusMap F (u,1),torus_le_borel F ⟨(u,1),rfl⟩⟩
  have ha : projectiveActor F m σ true b ∈ borel F := hB.le (mem_map_of_mem _ b.property)
  refine ⟨b,?_⟩
  have he : (⟨(b : PSL(3,F))⁻¹ * projectiveActor F m σ true b,
      cyclic_commutator_le _ _ hB (generator_displacement_mem _ _ b)⟩ : borel F) =
      b⁻¹ * ⟨projectiveActor F m σ true b,ha⟩ := rfl
  rw [he,map_mul,map_inv]
  have heval : projectiveQuotientMap F hF ⟨projectiveActor F m σ true b,ha⟩ =
      QuotientGroup.mk (1,(Units.map σ.toMonoidHom u)⁻¹) := by
    have hx : projectiveActor F m σ true b =
        linearConj F m (torusMap F (1,(Units.map σ.toMonoidHom u)⁻¹)) := by
      simp only [projectiveActor,↓reduceIte,MulAut.mul_apply,b,
        oppositionGraph_torusMap,field_torusMap,inv_one,map_one,map_inv]
    simp_rw [hx]
    exact projectiveQuotientMap_linear_torus F hF m hm _ _
  rw [heval]
  change projectiveGraphWitness F σ u = (projectiveQuotientMap F hF b)⁻¹ * _
  rw [show projectiveQuotientMap F hF b = QuotientGroup.mk (u,1) from projectiveQuotientMap_torus F hF _]
  change (QuotientGroup.mk' (cubicScalars F)) (graphWitness F σ u) =
    ((QuotientGroup.mk' (cubicScalars F)) (u,1))⁻¹ *
      (QuotientGroup.mk' (cubicScalars F)) (1,(Units.map σ.toMonoidHom u)⁻¹)
  rw [← map_inv,← map_mul]
  congr 1
  ext <;> simp [graphWitness]
end Matrix.PSL3.CartanActions.SixCommutators
