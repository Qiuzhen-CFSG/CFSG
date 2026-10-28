module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.Reduction

/-!
# Remaining permutation geometry for the primitive branch of B.1.13

The large-degree argument must bound the degree of a proper primitive
alternating Sylow overgroup containing a double transposition. In degree
seven the required identification is an isomorphism of the whole overgroup
with the actual matrix quotient PSL₃(2). In degree eight it suffices to
construct a nontrivial abelian normal subgroup of the overgroup itself:
primitivity and faithfulness will make it transitive and self-centralizing.

These are independent, unproved inputs to the component assembly. They do
not assert a classification, assume component models, or replace a group
by an isomorphic quotient. The degree-six case is discharged separately
by the checked solvable-parabolic classification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.13,
printed p.74 (PDF p.85), final paragraph. No SQTK or FF premise is added.
-/

public section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- The missing large-degree exclusion. The Sylow and permutation hypotheses
are all available at the literal source consumer. -/
@[expose] def AlternatingPrimitiveDegreeBound : Prop :=
  ∀ (m : ℕ), 6 ≤ m →
    ∀ (S : Sylow 2 (alternatingGroup (Fin m)))
      (X : Subgroup (alternatingGroup (Fin m))), (S : Subgroup _) ≤ X → X ≠ ⊤ →
      IsPreprimitive X (Fin m) →
      (∀ x : X, ¬ x.val.val.IsThreeCycle) →
      (∃ t : X, t ^ 2 = 1 ∧ t.val.val.support.card = 4) → m ≤ 8

/-- The seven-point identification must construct an actual multiplicative
equivalence, not merely the order 168 or a family label. -/
@[expose] def AlternatingPrimitiveSevenModel : Prop :=
  ∀ (S : Sylow 2 (alternatingGroup (Fin 7)))
    (X : Subgroup (alternatingGroup (Fin 7))), (S : Subgroup _) ≤ X → X ≠ ⊤ →
    IsPreprimitive X (Fin 7) →
    (∀ x : X, ¬ x.val.val.IsThreeCycle) →
    (∃ t : X, t ^ 2 = 1 ∧ t.val.val.support.card = 4) →
    Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))

/-- Only the abelian normal translation subgroup is needed in degree eight;
no identification of the quotient, group order, or complement is assumed. -/
@[expose] def AlternatingPrimitiveEightAbelianNormal : Prop :=
  ∀ (S : Sylow 2 (alternatingGroup (Fin 8)))
    (X : Subgroup (alternatingGroup (Fin 8))), (S : Subgroup _) ≤ X → X ≠ ⊤ →
    IsPreprimitive X (Fin 8) →
    (∀ x : X, ¬ x.val.val.IsThreeCycle) →
    (∃ t : X, t ^ 2 = 1 ∧ t.val.val.support.card = 4) →
    ∃ A : Subgroup X, A.Normal ∧ IsMulCommutative A ∧ A ≠ ⊥

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
