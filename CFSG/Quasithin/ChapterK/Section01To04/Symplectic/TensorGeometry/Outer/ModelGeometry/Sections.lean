module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.ModelGeometry.Coordinates
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Native actions on the Hermitian field sections

The actual fixed subgroup of the coefficient-field automorphism preserves the
fixed and displacement subspaces of transposition. In characteristic two the
displacement lies inside the fixed space. The middle quotient uses the literal
comap under inclusion and has dimension four. All action formulas retain the
published Hermitian representation. The common fixed space is identified with
the invariants of the fixed-space action, connecting these sections to the
source estimate. Faithfulness and the natural-module identification are separate
mathematical obligations.

Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457, and H.4.4(6), p.381.
-/

@[expose] public section

open Matrix Representation
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
noncomputable section
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ)

open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms

local instance : AddCommGroup (Space σ hσ) := inferInstance
local instance : AddCommGroup (fieldFixed σ hσ) := inferInstance

/-- The fixed subgroup of the literal coefficient-field automorphism. -/
abbrev centralizer : Subgroup (Sp F) := (fieldAutomorphism σ.toRingEquiv).fixedSubgroup

/-- The inherited action of the native fixed subgroup. -/
def centralizerAction : Representation k (centralizer σ) (Space σ hσ) :=
  (action σ hσ).comp (centralizer σ).subtype

lemma centralizerAction_commutes (g : centralizer σ) (X : Space σ hσ) :
    centralizerAction σ hσ g (fieldSwap σ hσ X) =
      fieldSwap σ hσ (centralizerAction σ hσ g X) := by
  change action σ hσ g.val (fieldSwap σ hσ X) = fieldSwap σ hσ (action σ hσ g.val X)
  rw [fieldSwap_action, (MulAut.mem_fixedSubgroup _ _).mp g.property]

lemma fieldMoved_le_fieldFixed [CharP F 2] : fieldMoved σ hσ ≤ fieldFixed σ hσ := by
  rintro X ⟨Y, rfl⟩
  rw [mem_fieldFixed]
  ext i j
  change Y.val i j - Y.val j i = Y.val j i - Y.val i j
  simp only [CharTwo.sub_eq_add, add_comm]

/-- The actual fixed matrices, with the restricted native action. -/
def fixedSubrepresentation : Subrepresentation (centralizerAction σ hσ) where
  toSubmodule := fieldFixed σ hσ
  apply_mem_toSubmodule g X hX := by
    have hfix : fieldSwap σ hσ X = X := by
      apply Subtype.ext
      exact (mem_fieldFixed σ hσ X).mp hX
    change fieldSwap σ hσ (centralizerAction σ hσ g X) - centralizerAction σ hσ g X = 0
    rw [← centralizerAction_commutes, hfix, sub_self]

/-- The actual displacement matrices, with the restricted native action. -/
def movedSubrepresentation : Subrepresentation (centralizerAction σ hσ) where
  toSubmodule := fieldMoved σ hσ
  apply_mem_toSubmodule g X hX := by
    obtain ⟨Y, rfl⟩ := hX
    refine ⟨centralizerAction σ hσ g Y, ?_⟩
    change fieldSwap σ hσ (centralizerAction σ hσ g Y) - centralizerAction σ hσ g Y =
      centralizerAction σ hσ g (fieldSwap σ hσ Y - Y)
    rw [map_sub, centralizerAction_commutes]

def movedAction : Representation k (centralizer σ) (fieldMoved σ hσ) :=
  (movedSubrepresentation σ hσ).toRepresentation

def fixedAction : Representation k (centralizer σ) (fieldFixed σ hσ) :=
  (fixedSubrepresentation σ hσ).toRepresentation

/-- The displacement subspace inside the fixed space is the literal comap under inclusion. -/
def movedInFixed : Submodule k (fieldFixed σ hσ) :=
  (fieldMoved σ hσ).comap (fieldFixed σ hσ).subtype

lemma movedInFixed_invariant (g : centralizer σ) :
    movedInFixed σ hσ ≤ (movedInFixed σ hσ).comap (fixedAction σ hσ g) := by
  intro X hX
  exact (movedSubrepresentation σ hσ).apply_mem_toSubmodule g hX

/-- The literal fixed/displacement quotient carrier. -/
abbrev Middle := (fieldFixed σ hσ) ⧸ movedInFixed σ hσ

/-- The literal fixed/displacement quotient representation. -/
def middleAction : Representation k (centralizer σ)
    (Middle σ hσ) :=
  (fixedAction σ hσ).quotient (movedInFixed σ hσ) (movedInFixed_invariant σ hσ)

lemma movedAction_apply (g : centralizer σ) (X : fieldMoved σ hσ) :
    (movedAction σ hσ g X).val = action σ hσ g.val X.val := rfl

lemma fixedAction_apply (g : centralizer σ) (X : fieldFixed σ hσ) :
    (fixedAction σ hσ g X).val = action σ hσ g.val X.val := rfl

lemma middleAction_mk (g : centralizer σ) (X : fieldFixed σ hσ) :
    middleAction σ hσ g ((movedInFixed σ hσ).mkQ X) =
      (movedInFixed σ hσ).mkQ (fixedAction σ hσ g X) := rfl

lemma finrank_middle [FiniteDimensional k F] [CharP F 2]
    (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl) :
    Module.finrank k (Middle σ hσ) = 4 := by
  change Module.finrank k ((fieldFixed σ hσ) ⧸ movedInFixed σ hσ) = 4
  have hd := (movedInFixed σ hσ).finrank_quotient_add_finrank
  have he := (Submodule.comapSubtypeEquivOfLe (fieldMoved_le_fieldFixed σ hσ)).finrank_eq
  change Module.finrank k (movedInFixed σ hσ) = Module.finrank k (fieldMoved σ hσ) at he
  rw [he, finrank_fieldMoved σ hσ hdeg hne, finrank_fieldFixed σ hσ hdeg hne] at hd
  omega

/-- Displacements have zero diagonal, in the original matrix coordinates. -/
lemma moved_diagonal_zero (X : fieldMoved σ hσ) (i : Index) : X.val.val i i = 0 := by
  obtain ⟨Y, hY⟩ := X.property
  have h := congrArg (fun Z : Space σ hσ => Z.val i i) hY
  change Y.val i i - Y.val i i = X.val.val i i at h
  simpa only [sub_self] using h.symm

/-- The source's intersection of fixed spaces is exactly the native invariant
space inside the field-fixed representation. -/
def commonFixedEquiv (B : Subgroup (Sp F)) (hB : B ≤ centralizer σ) :
    commonFixed σ hσ B ≃ₗ[k]
      Representation.invariants ((fixedAction σ hσ).comp (Subgroup.inclusion hB)) where
  toFun X := ⟨⟨X.val, X.property.1⟩, by
    intro b
    apply Subtype.ext
    exact X.property.2 b⟩
  invFun X := ⟨X.val.val, X.val.property, by
    intro b
    exact congrArg Subtype.val (X.property b)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma finrank_commonFixed_eq (B : Subgroup (Sp F)) (hB : B ≤ centralizer σ) :
    Module.finrank k (commonFixed σ hσ B) =
      Module.finrank k (Representation.invariants
        ((fixedAction σ hσ).comp (Subgroup.inclusion hB))) :=
  (commonFixedEquiv σ hσ B hB).finrank_eq

end
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
