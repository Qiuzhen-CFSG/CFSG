module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SevenRatio
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.Source
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Extension

/-!+# Source assembly of the perfect A₆ centralizer cover and its normalizer

The inputs are exactly the order and marked involution geometry of 47.1,
and the full five-local conclusion of 47.2 at that same selected involution.
Their producers are `qt-i47-j2-source-involutions` and
`qt-i47-j2-five-local-calculation`, respectively. No local Sylow calculation,
perfectness, quotient identification, or normalizer actor remains an input.

`CoreRecognition.Source` computes the Sylow factors of the literal C_G(X),
excludes the seven factor using `seven_normalizer_ratio`, and obtains the
index-six A₅ subgroup of C_G(X)/X. Its faithful coset action gives A₆, and
the nonabelian Sylow three forces perfectness. The independent actor
construction uses the earlier A₅ embedding and the extraspecial core norm
to produce an inverting involution and an element of order eight in N_G(X).

The first theorem supplies every field of `CentralizerCalculation`. The
second applies `Extension` to identify the quotient by the actual relative
copy of X with PGL₂ over the nine-element field. This entry point is kept
below the assembly roots and separate from `Recognition`, whose index
lemma is already used by the actor producer.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1–47.2 and the proof of
47.3(1), printed pp.259–262, especially p.262. The printed semidihedral
assertion and 47.4 are not premises of this construction. The remaining
Sylow and fusion clauses of 47.3 belong to the three-local assembly owner.
-/

public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {D : Seed G}

/-- The centralizer cover and both actual normalizer actors, from exactly the
earlier source order, selected geometry and marked five-local conclusion. -/
theorem centralizerCalculation_of_source (hG : Nat.card G = 604800)
    (geometry : InvolutionGeometry.SelectedGeometry D)
    (five : FiveLocal.SourceConclusion D geometry.t) :
    Nonempty (CentralizerCalculation D) :=
  (show EarlierConclusions D from ⟨hG, geometry, five⟩).centralizerCalculation

/-- Application to the extension consumer: the perfect-cover and actor premises
are discharged, retaining the literal quotient N_G(X)/(X subgroupOf N_G(X)). -/
theorem normalizerQuotient_of_source (hG : Nat.card G = 604800)
    (geometry : InvolutionGeometry.SelectedGeometry D)
    (five : FiveLocal.SourceConclusion D geometry.t) :
    Nonempty ((M D ⧸ XM D) ≃*
      GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) := by
  obtain ⟨H⟩ := centralizerCalculation_of_source hG geometry five
  exact ⟨H.normalizerQuotientEquiv⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
