module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ExtraspecialExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.TerminalStar

/-!
# Excluding the actual binary terminal component

The terminal component model constructs its two-perfect outside seed
inside the original X and identifies the literal Kc/O₂(Kc) with L₄(2).
The earlier component-orbit alternative gives Kc's centralization; the
original wreath quotient supplies T-irreducibility. Corrected15.2.21(3)
then contradicts S-reducibility from the original S₃-square quotient.

This completes the small-action contradiction consumed by the terminal
component owner. The preceding component, NI-action, Omega-row and
small-parabolic inputs retain their existing producers; final discharge
remains with qt-e-152-plane-uniqueness. No marked-factor comparison is
needed by this consumer.

Source: Aschbacher--Smith15.2.21(3) and15.2.23(a), printed pp.1114,1117,
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

/-- The binary terminal component contradicts the proved, arbitrary-seed
15.2.21(3). The original-X seed and literal Kc quotient come from the
terminal component model; T-irreducibility comes from the original wreath. -/
theorem binaryBranch_false_from_smallActions
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
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) → False := by
  let := hsource.prepared.elementary
  intro ho
  have hnot := reducible_of_symmetricThreePair d hpair
  have hc := orbit_centralizes_of_reducible d horbit hI hnot
  obtain ⟨f,hf,hker⟩ := exists_symmetricThree_action_of_image_equiv eNI
  obtain ⟨⟨eK⟩,_,P,_,_,_,_,s,hs⟩ := binaryBranch_smallAction_obstruction
    d hI hfit hn hout b hX hKX hpair (sylow_irreducible d) hc hNI f hf hker
  exact hnot (source_15_2_21_3_from_preceding d hquotient horbit hI s hs eNI eK ho)
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
