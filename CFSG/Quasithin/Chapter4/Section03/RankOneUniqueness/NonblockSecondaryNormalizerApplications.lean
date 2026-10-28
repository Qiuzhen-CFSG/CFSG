module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryNormalizer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryRadicalApplications

/-!
# Applying full normalizer control to the original secondary construction

The characteristic second center of R₂ proves N_G(R₂)≤H. Together with
the previous radical-saturation argument this supplies secondary
normalization and O₂(K_Z T)≤R₂ on the selected original component.
The corrected source constructor and the completed sieve/quintic exclusion
therefore retain only strict core enlargement among their 4.3.14 premises.

The earlier MS witness and simultaneous parabolic/Sylow markings, strict
core enlargement, the original A₅ application and terminal PSL₃(4)
representation contradiction remain with the same nonblock assembly owner.
Source: Aschbacher--Smith, original 4.3.14--16, pp.617--619.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- Construct the original source data after deriving the full radical-normalizer
containment from its intrinsic second center. Strict core enlargement and
the earlier MS/parabolic markings remain explicit source obligations. -/
theorem MSData.exists_secondarySourceData_of_core_enlargement
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (henlarges : secondary c < ((d.sourceComponent hn D h hL hSL).map
      (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) :
    ∃ s : SecondarySourceData c n,
      s.component = d.sourceComponent hn D h hL hSL ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      ((Q c).subgroupOf (rootNormalizer c)).map s.action ⊔
        ⁅((R₂ c).subgroupOf (rootNormalizer c)).map s.action,
          ((secondary c).subgroupOf (rootNormalizer c)).map s.action⁆ =
        ((R₂ c).subgroupOf (rootNormalizer c)).map s.action := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  exact d.exists_secondarySourceData_of_normalizer_containment hn D h hL hSL
    (m.radical_normalizer_le_original hn D) henlarges

/-- The corrected sieve and actual unitary-five exclusion leave the full
PSL₃(4) quotient. The normalizer and enlarged-core bound are discharged;
strict core enlargement and the earlier MS/marking inputs remain explicit. -/
theorem MSData.linearFour_of_core_enlargement
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (henlarges : secondary c < ((d.sourceComponent hn D h hL hSL).map
      (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) :
    ∃ s : SecondarySourceData c n,
      s.component = d.sourceComponent hn D h hL hSL ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      (n = 2 ∧ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4) ∧
      (s.torus.subgroupOf (rootNormalizer c)).map s.action ⊓
        MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  exact d.linearFour_of_normalizer_containment hn D h hL hSL
    (m.radical_normalizer_le_original hn D) henlarges

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
