module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSpecialCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameCoreOrder
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryNormalizerApplications

/-!
# The nonblock terminal contradiction from the original source data

The completed quotient sieve leaves PSL₃(4) and PSU₃(5), with source degree
two. The existing unitary proof uses the actual marked extraspecial five-group
and its central fixed-index bound. The new linear proof excludes the special
component core by putting it inside K₂, contrary to strict enlargement.
Both branches are now discharged for the same original MS and secondary data.

The source-component application constructs those secondary data from the
selected original component and explicit strict enlargement. It discharges
normalizer control, the enlarged-core bound, model inspection and both terminal
representation exclusions. The earlier MS witness, its simultaneous parabolic
and Sylow markings, and strict enlargement remain genuine source obligations
of qt-d-1222-rankone-uniqueness-nonblock. The independently owned nonbinary
classification is still required at its exact contract. No unconditional
4.3.2 or Chapter 12 uniqueness theorem is asserted here.

Source: Aschbacher--Smith, original 4.3.8--16 and conclusion of 4.3.2,
printed pp.616--619.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- Field transport preserves the actual full component quotient marking. -/
theorem MSData.linearFour_false_of_source_model (d : MSData c 2)
    (m : RootCoordinates d) (s : SecondarySourceData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmodel : ClassicalGroup.IsPSL (s.component ⧸ pCore 2 s.component) 3 4) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let i : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  exact d.linearFour_false_of_source m s D h (e.trans (Atlas.fieldEquivPSL 3 i))

/-- Both terminal models are impossible under the same original source data. -/
theorem MSData.false_of_secondarySourceData (d : MSData c n)
    (m : RootCoordinates d) (s : SecondarySourceData c n) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) : False := by
  obtain ⟨⟨hn2,hmodels⟩,_⟩ := EndgameSieve.SecondarySourceData.exceptional_of_coordinates
    s d m hn D h
  subst n
  rcases hmodels with hlinear | hunitary
  · exact d.linearFour_false_of_source_model m s D h hlinear
  · exact SourceEndgame.unitaryFive_false_of_source_data d s m D h hunitary

/-- Apply the terminal contradiction to the constructed original component.
Strict enlargement, the MS witness and its literal markings remain explicit. -/
theorem MSData.false_of_sourceComponent_core_enlargement
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (henlarges : secondary c < ((d.sourceComponent hn D h hL hSL).map
      (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) : False := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  obtain ⟨s,_⟩ := d.exists_secondarySourceData_of_core_enlargement hn D h hL hSL henlarges
  exact d.false_of_secondarySourceData m s hn D h

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
