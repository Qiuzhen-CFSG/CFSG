module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.CyclicStar
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaChosenComplete

/-!
# The remaining original star case in the L₄(2) exclusion

Apply the complete original 15.2.3 classification to the chosen module.
Its elementary-nine case makes C_M(V) prime to three and contradicts the
middle-parabolic seed. The cyclic case is excluded by CyclicStar using
the arbitrary outside seed. Thus the original Y-star is extraspecial
of order 27, with its actual Heisenberg isomorphism and order-nine action
image. TerminalStar applies this to the original binary component.

The final extraspecial contradiction is still required for 15.2.21(3).
Source: Aschbacher--Smith 15.2.21(3), printed p.1114, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding.OmegaAction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I Y₁ : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Only the original extraspecial star residual can remain in the reducible
L₄(2) branch. Both other alternatives are excluded on the original maps. -/
theorem linearFour_star_extraspecial
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I)
    (s : Seed M I (smallActionS T ZS) Y₁) (hout : ¬ Y₁ ≤ Mc ⊓ I)
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (eK : (smallActionKc H Mc ⧸ pCore 2 (smallActionKc H Mc)) ≃*
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
    let Y := caseIIResidual T M (chosenStarredPreimage M V hsource.prepared.normalized) Mc
    let P := (Y.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))
    Nat.card ((Y.subgroupOf M).map (action hsource)) = 9 ∧
      Nat.card P = 27 ∧ IsExtraspecial 3 P ∧ Nonempty (P ≃* HeisenbergPrime 3) := by
  let := hsource.prepared.elementary
  dsimp only
  intro ho
  have hs := source_omega_chosen_residual_complete hsource.ambient T hsource.empty
    hsource.maximal hsource.centralizing hsource.partner hsource.many hsource.prepared ho
  rcases hs.alternatives with he | hx | hc
  · have hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)) := by
      apply bot_unique
      apply primeToResidual_le
      rw [index_bot]
      exact he.2.2.2.2.2.2
    exact (hnot (linearFour_irreducible_of_threePrime d hquotient horbit hI hC eK)).elim
  · refine ⟨?_,hx.2.1,hx.2.2.1,hx.2.2.2.1⟩
    change Nat.card (((caseIIResidual T M
      (chosenStarredPreimage M V hsource.prepared.normalized) Mc).subgroupOf M).map
        (actionHom M V hsource.prepared.normalized).rangeRestrict) = 9
    rw [hx.1]
    obtain ⟨e⟩ := SymmetricThreeProductResidual.residual_equiv_elementaryNine ho.2.2.2.1.some
    exact (Nat.card_congr e.toEquiv).trans (by simp)
  · exact (linearFour_not_cyclic_star d hquotient horbit hI s hout eNI hnot eK ho hc.1).elim
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
