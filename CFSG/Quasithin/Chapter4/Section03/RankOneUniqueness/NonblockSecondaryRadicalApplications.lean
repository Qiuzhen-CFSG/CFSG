module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryRadicalBounds
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryQuotientApplications

/-!
# Applying the original secondary radical bounds

The center calculation Z(R₂)=Z_S derives secondary normalization from
N_G(R₂)≤H. The same containment and the original Sylow witness derive
O₂(K_Z T)≤R₂. Both conclusions are applied to the selected component
and the literal normal quotient action in the corrected source constructor.
The completed sieve and quintic exclusion then leave the full PSL₃(4)
quotient and original outer torus.

The normalizer containment, strict core enlargement, actual MS construction,
simultaneous markings and terminal linear-four contradiction remain explicit
obligations of qt-d-1222-rankone-uniqueness-nonblock. This is a reduction of
those source obligations, not the completed nonblock exclusion.
Source: Aschbacher--Smith, original 4.3.14--16, pp.617--619.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- Construct the original source data with 4.3.14's enlarged-core bound and
secondary normalization proved from the remaining normalizer containment.
The strict core enlargement remains a separate source obligation. -/
theorem MSData.exists_secondarySourceData_of_normalizer_containment
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (hN : normalizer (R₂ c : Set G) ≤ c.H)
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
  obtain ⟨_,_,hsec,_⟩ := d.sourceComponent_spec hn D h hL hSL
  exact d.exists_secondarySourceData_of_radical_geometry hn D h hL hSL
    (enlarged_core_le_radical_of_normalizer_le hN _
      (sup_le (hsec.le.trans le_sup_left) (inf_le_left.trans le_sup_right)))
    (m.radical_normalizer_control hn D hN) henlarges

/-- The corrected sieve and actual unitary-five exclusion now leave the full
PSL₃(4) quotient under only the still explicit normalizer containment and
strict core enlargement, in addition to the earlier MS and marking inputs. -/
theorem MSData.linearFour_of_normalizer_containment
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (hN : normalizer (R₂ c : Set G) ≤ c.H)
    (henlarges : secondary c < ((d.sourceComponent hn D h hL hSL).map
      (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) :
    ∃ s : SecondarySourceData c n,
      s.component = d.sourceComponent hn D h hL hSL ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      (n = 2 ∧ ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4) ∧
      (s.torus.subgroupOf (rootNormalizer c)).map s.action ⊓
        MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  obtain ⟨_,_,hsec,_⟩ := d.sourceComponent_spec hn D h hL hSL
  exact d.linearFour_of_radical_geometry hn D h hL hSL
    (enlarged_core_le_radical_of_normalizer_le hN _
      (sup_le (hsec.le.trans le_sup_left) (inf_le_left.trans le_sup_right)))
    (m.radical_normalizer_control hn D hN) henlarges

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
