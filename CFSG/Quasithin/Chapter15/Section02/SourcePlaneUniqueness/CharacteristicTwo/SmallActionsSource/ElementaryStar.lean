module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.MiddleParabolic
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaNineElementary

/-!
# Eliminating the elementary residual in the reducible L₄(2) branch

The original 15.2.3 elementary-nine branch makes C_M(V) a 3′-group.
The middle minimal parabolic constructed inside the literal Kc gives a
two-perfect seed in that centralizer with an S₃ quotient after adjoining
S. The two conclusions are incompatible. This connects the new middle-node
construction to the original residual and its action and star quotient maps.

The cyclic and extraspecial 15.2.3 branches and the arbitrary outside seed
remain part of the complete 15.2.21(3) argument.

Source: Aschbacher--Smith 15.2.21(3), printed p.1114; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- The elementary-nine branch of the original star residual cannot occur
when the literal L₄(2) component has a reducible S-action. -/
theorem linearFour_not_elementary_star
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (eK : (smallActionKc H Mc ⧸ pCore 2 (smallActionKc H Mc)) ≃*
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) →
      let Y := caseIIResidual T M
        (chosenStarredPreimage M V hsource.prepared.normalized) Mc
      Nat.card ((Y.subgroupOf M).map
        (actionHom M V hsource.prepared.normalized).rangeRestrict) = 9 →
      Nat.card ((Y.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) = 9 → False := by
  let := hsource.prepared.elementary
  dsimp only
  intro ho hbar hstar
  have hcop := (source_omega_nine_elementary_data hsource.ambient T
    hsource.maximal.1 hsource.partner hsource.prepared ho hbar hstar).2
  have hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)) := by
    apply bot_unique
    apply primeToResidual_le
    rwa [index_bot]
  exact hnot (linearFour_irreducible_of_threePrime d hquotient horbit hI hC eK)
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
