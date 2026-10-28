module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryQuotient
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCoreApplications

/-!
# Applying the secondary quotient theorem to the original source construction

The original torus-centralizer argument now proves quasisimplicity for the
component selected in the root normalizer. The corrected source constructor
therefore needs only the remaining 4.3.14 radical-normalizer/core geometry,
in addition to the earlier MS witness and simultaneous parabolic markings.
The completed sieve and quintic exclusion reduce this same constructed
witness to the full PSL₃(4) quotient and retain the original outer torus.

The remaining geometry, actual MS construction, earlier A₅ consumer and
linear-four representation contradiction belong to
qt-d-1222-rankone-uniqueness-nonblock. These applications do not discharge
those premises or construct the refuted whole-radical torus-movement field.
Source: Aschbacher--Smith, original 4.3.12--16 and the conclusion of 4.3.2,
printed pp.617--619.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- Construct the source data with the selected component's quotient now proved
quasisimple. Only the original radical-normalizer/core geometry remains. -/
theorem MSData.exists_secondarySourceData_of_radical_geometry
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (henlarged : ((d.sourceComponent hn D h hL hSL).map (rootNormalizer c).subtype ⊔
      (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hnorm : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (henlarges : secondary c < ((d.sourceComponent hn D h hL hSL).map
      (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) :
    ∃ s : SecondarySourceData c n,
      s.component = d.sourceComponent hn D h hL hSL ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      ((Q c).subgroupOf (rootNormalizer c)).map s.action ⊔
        ⁅((R₂ c).subgroupOf (rootNormalizer c)).map s.action,
          ((secondary c).subgroupOf (rootNormalizer c)).map s.action⁆ =
        ((R₂ c).subgroupOf (rootNormalizer c)).map s.action :=
  d.exists_secondarySourceData_of_sourceComponent hn D h hL hSL
    (d.sourceComponent_quasisimple hn D h hL hSL) henlarged hnorm henlarges

/-- Apply the corrected sieve and actual unitary exclusion to the selected
component, with no remaining component-selection or quasisimplicity premise. -/
theorem MSData.linearFour_of_radical_geometry
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (henlarged : ((d.sourceComponent hn D h hL hSL).map (rootNormalizer c).subtype ⊔
      (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hnorm : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (henlarges : secondary c < ((d.sourceComponent hn D h hL hSL).map
      (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) :
    ∃ s : SecondarySourceData c n,
      s.component = d.sourceComponent hn D h hL hSL ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      (n = 2 ∧ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4) ∧
      (s.torus.subgroupOf (rootNormalizer c)).map s.action ⊓
        MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ := by
  obtain ⟨hB,hBn,hsec,_⟩ := d.sourceComponent_spec hn D h hL hSL
  exact d.linearFour_of_secondary_geometry hn D h hL hSL
    (d.sourceComponent hn D h hL hSL) hB hBn
    (d.sourceComponent_quasisimple hn D h hL hSL) hsec.le henlarged hnorm henlarges

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
