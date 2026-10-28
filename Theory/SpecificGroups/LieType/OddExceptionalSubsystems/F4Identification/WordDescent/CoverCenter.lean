module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Operators

/-!
# Center reduction for the actual odd-characteristic F4 matrix cover

A central matrix commutes with every value of the explicitly signed adjoint
candidate. If that candidate is injective and intertwines the actual root
curves with conjugation, it follows that the central matrix fixes every vector.
This proves the matrix is the identity, not just that its central quotient is
centerless. Generator equivariance extends to the whole literal cover by
subgroup closure induction.

The two operator hypotheses remain explicit. Their independent proofs must
be supplied before asserting the unconditional cover-center theorem used by
`WordDescent`. Source: the adjoint Chevalley construction in GLS3 §§2.2–2.6,
realized by this repository's integral Geck operators.
-/

public section
noncomputable section

open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open Theory.AlgebraicGroup
open ReeF4.WordRelations.Faithfulness

namespace TwistedE6.FoldedSubsystem.F4Identification.CoverCenter

variable (F : Type*) [Field F]

/-- Equivariance of the literal all-root curves propagates to their matrix cover. -/
theorem equivariant_cover_of_rootCurves
    (heq : ∀ r t, Equivariant (adjointMap F) (F4Chevalley.rootCurve r t))
    (g : Cover F) : Equivariant (adjointMap F) g.val := by
  apply equivariant_closure (adjointMap F)
    (Set.range fun rt : typeF4Roots × F => F4Chevalley.rootCurve rt.1 rt.2)
  · rintro _ ⟨⟨r, t⟩, rfl⟩
    exact heq r t
  · exact g.property

/-- The explicit faithful adjoint map detects every central displacement. -/
theorem central_eq_one_of_adjointMap (htwo : (2 : F) ≠ 0)
    (hinj : Function.Injective (adjointMap F))
    (heq : ∀ r t, Equivariant (adjointMap F) (F4Chevalley.rootCurve r t))
    (g : Cover F) (hg : g ∈ Subgroup.center (Cover F)) : g = 1 := by
  have he := equivariant_cover_of_rootCurves F heq g
  have hfix (v : Coordinate → F) : g.val.val *ᵥ v = v := by
    apply hinj
    apply (Units.mul_left_inj g.val).mp
    exact (he v).trans (central_commutes_adjointMap F htwo g hg v).eq
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h := congrFun (hfix (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply,
    OneMemClass.coe_one, Units.val_one, Matrix.one_apply] using h

/-- Conditional assembly, retaining the two unproved operator obligations. -/
theorem center_eq_bot_of_adjointMap (htwo : (2 : F) ≠ 0)
    (hinj : Function.Injective (adjointMap F))
    (heq : ∀ r t, Equivariant (adjointMap F) (F4Chevalley.rootCurve r t)) :
    Subgroup.center (Cover F) = ⊥ := by
  apply bot_unique
  intro g hg
  exact Subgroup.mem_bot.mpr (central_eq_one_of_adjointMap F htwo hinj heq g hg)

end TwistedE6.FoldedSubsystem.F4Identification.CoverCenter
