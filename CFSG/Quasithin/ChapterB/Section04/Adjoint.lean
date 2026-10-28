module

public import Theory.Representation.SL3.AdjointCubicCentralizer.Projective

/-!
# The adjoint calculation and the extension issue in B.4.14

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma B.4.14, printed p.98.

For the ordinary adjoint action, the fixed space of diag(ω,1,1) is the
four-dimensional space diag(-tr(D),D). The lower SL₂ acts on D by
conjugation, as recorded by `fixedRepresentationEquiv`.

There is a distinct projective extension of the same SL₃ action: multiply
conjugation by the determinant character. Scalar matrices have determinant
one over F₄, so this is an actual PGL₃ representation. The same cubic now
fixes just the two-dimensional lower-left column. The theorem below combines
these facts for a nonidentity cubic in the actual projective quotient, and
rules out even an intertwining bijection between the two projective actions.
In particular a binary module isomorphism cannot identify these extensions.

This is an obstruction to the printed proof's step from an adjoint SL₃
constituent to the claimed PGL₃ action. It is not a proof of B.4.14, nor a
formal verification of all hypotheses for a counterexample. The binary
irreducibility, faithful-action and parabolic chief-factor checks are not
asserted here. The source recognition statement and uniserial conclusion
remain unproved. No additional premise selecting an extension has been
silently added to that statement.
-/

public section
namespace CFSG.Quasithin.ChapterB.Section04.Adjoint
open Representation.SL3.AdjointCubicCentralizer

/-- Over the four-element field, identical restrictions through SL₃ do not
determine either the projective module or its cubic fixed-space dimension.
All actions use the literal quotient map `Matrix.SpecialLinearGroup.toPGL`. -/
theorem determinant_twist_obstruction (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 4) :
    ∃ ω : Fˣ,
      orderOf (Matrix.ProjGenLinGroup.mk (diagonalUnit F ω)) = 3 ∧
      Module.finrank F (fixedSpace F ω) = 4 ∧
      Module.finrank F (twistedFixedSpace F ω) = 2 ∧
      (projectiveTwistedAdjoint F (units_cube_of_card_four F hF)).comp
          Matrix.SpecialLinearGroup.toPGL =
        (projectiveAdjoint F).comp Matrix.SpecialLinearGroup.toPGL ∧
      ¬ ∃ e : TraceZero F ≃ TraceZero F, ∀ g X,
        e (projectiveAdjoint F g X) =
          projectiveTwistedAdjoint F (units_cube_of_card_four F hF) g (e X) := by
  let := Fintype.ofFinite Fˣ
  have : Nontrivial Fˣ := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hF]
    decide)
  obtain ⟨ω,hω⟩ := exists_ne (1 : Fˣ)
  have hω' : (ω : F) ≠ 1 := fun h => hω (Units.ext h)
  have hω2 := square_ne_one_of_cube F ω hω'
    (congrArg Units.val (units_cube_of_card_four F hF ω))
  exact ⟨ω, projective_diagonal_order F hF ω hω', finrank_fixedSpace F ω hω',
    finrank_twistedFixedSpace F ω hω' hω2, projective_restrictions_equal F _,
    no_projective_intertwining_bijection F hF ω hω'⟩

end CFSG.Quasithin.ChapterB.Section04.Adjoint
