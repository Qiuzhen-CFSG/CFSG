module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SectionAlternatives
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SectionAlternatives.Source.GroupComparison


/-!
# Surviving source sections on the actual offender action

Intersect every action row of B.4.2 and B.5.1(1) with the proved small
actor catalogue. The actual quotient N/F*(N) is a two-group, so the
rank-one rows fail the odd-part comparison. The unipotent two-parts
exclude larger-field Sp₄ and G₂, and the order bounds exclude binary
SL₄, SL₅ and the degree-eight permutation rows.

The surviving ordinary actions are transported using their original group
and linear equivalences. In the marked rows, `restrictMarked` uses the
commuting subgroup square. The doubled-natural alternative remains on
[V,F*(N)] itself; the other ordinary alternatives remain on its central
quotient. No splitting of either extension is required. All six B.5.1
clauses remain stored in the original source conclusion; clause (1) and
its Sylow supplement suffice for this extraction.

The two exceptional outputs retain the faithful section action and the
full marked binary G₂ or corrected projective-line triple-six geometry.
The literal quotient-action application combines the extraction with the
proved ordinary fixed-space exclusions. Its exceptional calculations and
the final quotient identification remain with their respective owners.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.2, p.86; B.5.1(1)–(6), p.99; K.1.3, p.453; 15.4.18, p.1163.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open ClassificationComparison ClassificationComparison.FFAlternatives
open ClassificationComparison.QuasisimpleComparison NativeSections
universe u v
variable {A : Type u} [Group A] [Finite A]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) A V}

namespace ClassificationComparison.QuasisimpleComparison

/-- Extract every surviving section from the full corrected B.5.1 conclusion
and the actual small actor. Nonsplit and trivial extensions are retained. -/
theorem BoundedBranch.sectionAlternatives
    (b : BoundedBranch ρ) (ha : SmallActorModel A) :
    SectionAlternatives b.source.sectionData := by
  have hq := b.actorQuotient_twoGroup
  cases b.source.clause_one with
  | irreducible _ faithful _ source _ =>
    cases source with
    | linearTwo F _ e _ _ =>
      exact (SourceSections.no_linearTwo ha _ hq F e.groupEquiv).elim
    | linearThree F _ e _ =>
      exact Or.inl (.linearThree F e)
    | symplectic F large _ e _ =>
      have h := symplectic_degree_eq_one (SourceSections.small_sylow ha) F
        ((generalizedFitting A).subtype.comp e.groupEquiv.symm.toMonoidHom)
        (Subtype.val_injective.comp e.groupEquiv.symm.injective)
      omega
    | symplecticTwo e _ =>
      exact Or.inl (.symplecticDerived (restrictMarked e))
    | g2 F large _ e _ _ =>
      have h := g2_degree_eq_one (SourceSections.small_sylow ha) F
        ((generalizedFitting A).subtype.comp e.groupEquiv.symm.toMonoidHom)
        (Subtype.val_injective.comp e.groupEquiv.symm.injective)
      omega
    | g2Two e _ _ =>
      exact Or.inr (Or.inr (.binaryG2 faithful e))
    | symmetric n hn e _ _ =>
      rcases hn with rfl | rfl
      · exact (SourceSections.no_linearTwo ha _ hq BinaryField.four
          (e.subgroupEquiv.trans alternatingFiveLinearEquiv)).elim
      · exact Or.inl (.alternating 7 (Or.inr rfl) (restrictMarked e))
    | alternatingSix _ e _ _ =>
      exact Or.inl (.alternating 6 (Or.inl rfl) e)
    | alternatingSeven _ _ e dimension _ _ =>
      exact Or.inl (.alternatingFour e (faithful.comp Subtype.val_injective) dimension)
    | tripleSix _ action _ =>
      exact Or.inr (Or.inr (.tripleSix faithful action))
    | binaryLinear d hd _ e _ =>
      exact (SourceSections.no_linearFourFive ha _ d hd e.groupEquiv).elim
    | orthogonalSix _ _ e _ _ =>
      exact (SourceSections.no_linearFourFive ha _ 4 (Or.inl rfl)
        (e.groupEquiv.trans alternatingEightLinearEquiv)).elim
    | symmetricEight _ e _ =>
      exact (SourceSections.no_linearFourFive ha _ 4 (Or.inl rfl)
        (e.subgroupEquiv.trans alternatingEightLinearEquiv)).elim
    | exteriorFive _ _ e _ _ _ =>
      exact (SourceSections.no_linearFourFive ha _ 5 (Or.inr rfl) e).elim
  | doubleThree F _ e _ _ =>
    exact Or.inr (Or.inl (.repeatedThree F 2 e))
  | naturalDual d hd _ h =>
    obtain ⟨e⟩ := h
    exact (SourceSections.no_linearFourFive ha _ d hd e.groupEquiv).elim
  | repeatedNatural d _ hd _ _ _ h =>
    obtain ⟨e⟩ := h
    exact (SourceSections.no_linearFourFive ha _ d hd e.groupEquiv).elim

/-- The proved module disjunction on the literal offender actor and its
actual generalized Fitting subgroup, with no additional classifier premise. -/
theorem ComparedBranch.sectionAlternatives
    (b : ComparedBranch ρ) : SectionAlternatives b.source.sectionData :=
  b.toBoundedBranch.sectionAlternatives b.smallActor

end ClassificationComparison.QuasisimpleComparison

variable {H : Type u} [Group H] [Finite H]
  (P : Sylow 2 H) (Z : Subgroup H) [IsElementaryAbelian 2 (moduleClosure Z)]
  (hC : centralizer (Z : Set H) = (P : Subgroup H))

/-- On the literal H/O₂(H) action, discharge the module-disjunction premise
of the existing seed-centralizer exclusion. Only the exceptional sections remain. -/
theorem comparedBranch_exceptionalSection
    (b : ComparedBranch (quotientAction P Z hC)) :
    ExceptionalSection b.source.sectionData :=
  comparedBranch_exceptionalSection_of_models P Z hC b b.sectionAlternatives

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
