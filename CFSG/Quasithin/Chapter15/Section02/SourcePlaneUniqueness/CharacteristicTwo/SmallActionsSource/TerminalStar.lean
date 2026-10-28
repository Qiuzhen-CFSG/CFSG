module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.StarReduction
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.RepeatedNatural.Source
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.Transport

/-!
# The surviving star residual for the original binary component

The terminal owner's obstruction constructs the corrected seed inside the
original X and identifies the literal Kc/O₂(Kc) with L₄(2). The earlier
component-orbit alternative supplies Kc's centralization, and the actual
NI action supplies the faithful S₃ map. StarReduction then eliminates
the elementary and cyclic cases for this exact seed and quotient marking.

The remaining star residual is the actual extraspecial group of order 27.
Its exclusion, rather than this reduction alone, is needed to complete
the binary terminal branch and source 15.2.21(3).
Earlier component and action premises retain their existing producers;
final source discharge remains with qt-e-152-plane-uniqueness.

Source: Aschbacher--Smith 15.2.21(3), 15.2.23(a), printed pp.1114,1117;
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding.OmegaAction TerminalLinear
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The actual binary component reaches only the extraspecial source star
case, using its original-X seed and literal Kc/O₂(Kc) marking. -/
theorem binaryBranch_star_extraspecial
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    {n : ℕ} (b : BinaryBranch M I X n)
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hirr : IsSmallActionIrreducible (T : Subgroup G) (smallActionK H))
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    let P := (Y.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 9 ∧
      Nat.card P = 27 ∧ IsExtraspecial 3 P ∧ Nonempty (P ≃* HeisenbergPrime 3) := by
  have hnot := reducible_of_symmetricThreePair d hpair
  have hc := orbit_centralizes_of_reducible d horbit hI hnot
  obtain ⟨f,hf,hker⟩ := exists_symmetricThree_action_of_image_equiv eNI
  obtain ⟨⟨eK⟩,_,P,_,_,_,_,s,hs⟩ := binaryBranch_smallAction_obstruction
    d hI hfit hn hout b hX hKX hpair hirr hc hNI f hf hker
  exact linearFour_star_extraspecial d hquotient horbit hI s hs eNI hnot eK
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
