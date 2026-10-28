module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.LocalFacts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Five
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Overgroup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Obligations
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three

/-!
# Assembly of corank-two block lifting

For an A₅ block the genuine local family and earlier 1.2.4 construct a
containing C-component. Trivial odd core then gives either an ordinary
component or characteristic two of its overgroup generated with Q.
This module assembles the two block types using that actual overgroup.

For an A₃ block, the separate layer-placement argument either constructs
an ordinary component containing it or places it in the layer centralizer.
In the latter case an E.6.7 factor in the characteristic-two envelope gives
the required block, with its actual module and relative subnormality.
The final theorem supplies both branches and the characteristic-two
C-component classification. Only the permitted earlier-source inputs remain;
an A₃ block is never inserted into the perfect local family.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265); 1.2.3–4, printed p.505.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
open ComponentBalance

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- Relative C-components have the ordinary-component/characteristic-two
dichotomy in the actual centralizer. -/
theorem centralizer_cComponent_dichotomy (h21 : OddCoreFree V)
    {A X : Subgroup G} (hA : A ∈ obstructionFamily M V)
    (hX : X ∈ Chapter1.cComponentsIn (centralizer (A : Set G))) :
    CentralizerComponent A X ∨ generalizedFitting X = pCore 2 X := by
  rcases hX.2.component_or_generalizedFitting_eq_pCore (h21 A hA.1 hA.2.1) with hc | hf
  · exact Or.inl ⟨hX.1, hc⟩
  · right
    let e := subgroupOfEquivOfLe hX.1
    have hm := congrArg (Subgroup.map e.toMonoidHom) hf
    rwa [map_generalizedFitting_equiv, pCore_map_iso] at hm

/-- The nonsolvable branch, conditional only on the remaining block
classification and the permitted earlier 1.2.4 input. -/
theorem five_lifting
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (earlier : LocalContainmentInput G) (h21 : OddCoreFree V)
    (blocks : CharacteristicTwoComponentBlocks (sylowCentralizer (T : Subgroup G) V) M V)
    {U A L : Subgroup G} (hU : U ∈ obstructionFamily M V)
    (hA : A ∈ obstructionFamily M V) (hAU : A ≤ U) (hc : subgroupCorank V A = 2)
    (hL : SmallBlock U L) (h5 : ChapterC.IsAlternatingBlock L 5) (he : ¬ L ≤ M) :
    ∃ X : Subgroup G, L ≤ X ∧
      ((CentralizerBlock A X ∧ ChapterC.IsChiZeroBlock X) ∨ CentralizerComponent A X) := by
  obtain ⟨X, ⟨hX, hLX⟩, _⟩ :=
    exists_unique_cComponent_overgroup_of_five h earlier hU hA hAU hL h5
  refine ⟨X, hLX, ?_⟩
  rcases centralizer_cComponent_overgroup_dichotomy h h21 hA hX with hcomp | hfit
  · exact Or.inr hcomp
  · exact Or.inl (blocks A hA hc X hX (fun hx => he (hLX.trans hx)) hfit)

/-- Assembly from the two branch contracts. The final theorem below
discharges both using their proved constructions. -/
theorem corankTwoLifting_of_three_and_componentBlocks
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (earlier : LocalContainmentInput G) (h21 : OddCoreFree V)
    (three : ThreeBlockLifting M V)
    (blocks : CharacteristicTwoComponentBlocks (sylowCentralizer (T : Subgroup G) V) M V) :
    CorankTwoLifting M V := by
  intro U hU hUh L hL he A hA hAU hc
  rcases hL.2.2 with h3 | h5
  · exact three U hU hUh L hL h3 he A hA hAU hc
  · exact five_lifting h earlier h21 blocks hU hA hAU hc hL h5 he

/-- The corank-two overgroup construction in E.6.23, including the solvable
A₃ branch. The explicit source inputs are hyperplane characteristic two,
1.2.4 containment, E.6.7–8, E.6.18 and E.6.21, C.1.9, the component-orbit
clause of 1.2.1(3), and the Sylow-orbit clause of A.3.8(3). No new lifting,
placement, block-identification or persistence premise remains. -/
theorem corankTwoLifting [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V)
    (hchar : ∀ W : Subgroup G, IsHyperplane V W →
      generalizedFitting (centralizer (W : Set G)) = pCore 2 (centralizer (W : Set G)))
    (earlier : LocalContainmentInput G)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (h8 : OddObstruction.EarlierComponentAlternatives M V
      (sylowCentralizer (T : Subgroup G) V))
    (h18 : SevenExcluded M V) (h21 : OddCoreFree V)
    (h19 : BlockCommutationInput G)
    (horbit : Three.Placement.EarlierComponentOrbits (G := G))
    (h38 : CharacteristicTwoBlocks.SylowOrbitSource K) :
    CorankTwoLifting M V :=
  corankTwoLifting_of_three_and_componentBlocks h earlier h21
    (threeBlockLifting h hchar h67 h8 h18 h21 h19 horbit)
    (characteristicTwoComponentBlocks h h15 h67 h38 h19)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting
