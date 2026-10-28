module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Source

/-!
# The matrix calculation needed for the fixed value spaces

These definitions retain the arbitrary automorphism marking of the natural
three-space and the common flag of the two parabolics. `ModelGeometry` is an
explicit intermediate obligation about subgroups of the literal eight-element
module. Its construction from a nonzero parabolic fixed vector is separate
from transport to an extension and is not asserted in this module.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(i), printed p.847.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open Subgroup

abbrev VectorGroup := Multiplicative (Fin 3 → ZMod 2)

/-- The natural action, in multiplicative notation for its additive group. -/
noncomputable def vectorAction (a : SL) : VectorGroup ≃* VectorGroup :=
  AddEquiv.toMultiplicative (Matrix.SpecialLinearGroup.toLin' a).toAddEquiv

@[simp] theorem vectorAction_apply (a : SL) (v : VectorGroup) :
    (vectorAction a v).toAdd = a.val.mulVec v.toAdd := rfl

/-- Pointwise fixed vectors for an actual matrix subgroup. -/
def fixedSpace (P : Subgroup SL) : Subgroup VectorGroup where
  carrier := {v | ∀ a ∈ P, vectorAction a v = v}
  one_mem' := by intro a _; exact map_one _
  mul_mem' := by
    intro v w hv hw a ha
    rw [map_mul, hv a ha, hw a ha]
  inv_mem' := by
    intro v hv a ha
    rw [map_inv, hv a ha]

@[simp] theorem mem_fixedSpace (P : Subgroup SL) (v : VectorGroup) :
    v ∈ fixedSpace P ↔ ∀ a ∈ P, vectorAction a v = v := Iff.rfl

/-- Both parabolics use the same marking, which need not be inner. -/
def markedParabolic (σ : MulAut SL) (g : SL) (j : Bool) : Subgroup SL :=
  (modelParabolic g j).map σ.toMonoidHom

/-- Fixed vectors of the full parabolic's intrinsic two-core. -/
def modelValues (σ : MulAut SL) (g : SL) (j : Bool) : Subgroup VectorGroup :=
  fixedSpace (((pCore 2 (modelParabolic g j)).map (modelParabolic g j).subtype).map
    σ.toMonoidHom)

/-- The finite natural-module calculation. All groups and actors here are
literal matrices or vectors; no ambient extension or source commutator occurs.
A constructor must derive this from `fixedSpace (markedParabolic σ g i) ≠ ⊥`. -/
structure ModelGeometry (σ : MulAut SL) (g : SL) (i : Bool) : Prop where
  small_invariant : ∀ A : Subgroup VectorGroup, Nat.card A ≤ 4 →
    (∀ a ∈ markedParabolic σ g i, A.map (vectorAction a).toMonoidHom = A) →
    A ≤ modelValues σ g i
  seed_fixed : modelValues σ g i ≤ fixedSpace (markedParabolic σ g i)
  seed_card : Nat.card (modelValues σ g i) ≤ 2
  incident : modelValues σ g i ≤ modelValues σ g (!i)
  other_proper : modelValues σ g (!i) ≠ ⊤
  neighbors : ∃ a b : SL, a ∈ markedParabolic σ g (!i) ∧
    b ∈ markedParabolic σ g (!i) ∧
    modelValues σ g i ⊓ (modelValues σ g i).map (vectorAction a).toMonoidHom = ⊥ ∧
    modelValues σ g i ⊓ (modelValues σ g i).map (vectorAction b).toMonoidHom = ⊥ ∧
    (modelValues σ g i).map (vectorAction a).toMonoidHom ⊓
      (modelValues σ g i).map (vectorAction b).toMonoidHom = ⊥

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
