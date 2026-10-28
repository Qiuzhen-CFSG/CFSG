module

public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.Actors
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Isolating the linear factor of a Sylow-preserving standard actor

The special linear actor descends through the actual center quotient to the
specified projective actor. Field and opposition graph automorphisms preserve
the upper unipotent subgroup, so a Sylow-preserving standard actor has a
Sylow-preserving GL₃ factor. No torus-fixation or involution assumption is used.
Source: GLS3 §2.7; Aschbacher–Smith 13.8.20, printed p.954.
-/

public section

open scoped MatrixGroups Pointwise
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage Matrix.PSL3.CartanActions
namespace Matrix.PSL3.CartanActions.SixCommutators
variable (F : Type*) [Field F]

theorem centerAction_specialActor (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool) :
    centerAction F (specialActor F m σ ε) = projectiveActor F m σ ε := by
  have hf : centerAction F (Atlas.fieldEquivSL 3 σ) = fieldAction F σ := by
    ext x
    obtain ⟨y,rfl⟩ := projection_surjective F x
    change QuotientGroup.mk (Atlas.fieldEquivSL 3 σ y) =
      fieldAction F σ (QuotientGroup.mk y)
    rw [fieldAction_mk]
    rfl
  have hg : centerAction F (oppositionGraphSL F) = oppositionGraph F := by
    rw [oppositionGraphSL,map_mul]
    rfl
  cases ε <;> simp [specialActor,projectiveActor,map_mul,hf,hg,linearConj]

theorem centerAction_unipotent (α : MulAut SL(3,F))
    (h : (unipotentSL F).map α.toMonoidHom = unipotentSL F) :
    (unipotent F).map (centerAction F α).toMonoidHom = unipotent F := by
  change ((unipotentSL F).map (projection F)).map _ = _
  have hc : (centerAction F α).toMonoidHom.comp (projection F) =
      (projection F).comp α.toMonoidHom := rfl
  rw [Subgroup.map_map,hc,← Subgroup.map_map,h]
  rfl

variable [CharP F 2]

theorem linear_part_unipotent (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool)
    (h : (unipotent F).map (projectiveActor F m σ ε).toMonoidHom = unipotent F) :
    (unipotent F).map (linearConj F m).toMonoidHom = unipotent F := by
  let H := MulAction.stabilizer (MulAut PSL(3,F)) (unipotent F)
  have ha : projectiveActor F m σ ε ∈ H := h
  have hf : fieldAction F σ ∈ H := fieldAction_unipotent F σ
  have hg : (if ε then oppositionGraph F else 1) ∈ H := by
    cases ε
    · exact H.one_mem
    · exact oppositionGraph_unipotent F
  have hh := H.mul_mem (H.mul_mem ha (H.inv_mem hg)) (H.inv_mem hf)
  have hmem : linearConj F m ∈ H := by
    simpa only [projectiveActor,mul_inv_cancel_right] using hh
  exact hmem

end Matrix.PSL3.CartanActions.SixCommutators
