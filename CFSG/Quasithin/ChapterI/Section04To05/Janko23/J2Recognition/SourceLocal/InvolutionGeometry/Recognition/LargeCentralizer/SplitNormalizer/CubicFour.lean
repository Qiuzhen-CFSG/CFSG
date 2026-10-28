module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SplitNormalizer.Inputs
public import Theory.SpecificGroups.Alternating.FourTransitiveCubic

/-!
# The marked cubic-four subgroup of the large-centralizer frame

The frame's subgroup U has order four, and X₃ has order three and acts
transitively on its nonidentity elements. The faithful four-coset action
therefore gives an actual isomorphism UX₃ ≃ A₄. The normal Sylow
identification of U transports through this same isomorphism, giving
exactly the ambient two-core marking required by `CubicFourModel`.

This supplies the cubic-four input to
`LiftedFive.unalignedGeometry_of_cubicFourModel`. It requires neither
a central quotient recognition nor a lifted normal A₅.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), printed p.260.
-/

public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer

variable {G : Type*} [Group G] [Finite G] {D : Seed G} {t : G}

/-- The transitive cubic action supplies the actual marked A₄ model. -/
theorem LocalFrame.nonempty_cubicFourModel (F : LocalFrame D t) :
    Nonempty (CubicFourModel F) := by
  obtain ⟨e, he⟩ := AlternatingFourTransitiveCubic.exists_marked_equiv
    F.U F.X3 F.U_card F.X3_card F.X3_normalizes F.X3_transitive
  exact ⟨⟨e, he⟩⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
