module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.AlternatingFive.Action
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.AlternatingSeven.Action

/-!+# The preliminary no-chi-block theorem and the NI ≤ MI branch

The actual rank-one and alternating actions exclude all four chi-block
families in the escaping-plane subgroup I. C.1.28 then supplies a chi-block
if NI = M ∩ I is contained in MI = Mc ∩ I, closing that branch of 15.2.23.

The only extra earlier-source premise is the Kc orbit alternative. Its
producers are qt-e-152-plane-geometry and qt-e-152-small-parabolic; final
discharge remains with qt-e-152-plane-characteristic-two. No model marking,
action, or block-exclusion premise remains in these statements.

Source: Aschbacher--Smith, preliminary 15.2.23 and its first branch,
printed pp.1115–1116, refs/quasithin.pdf. The separate C.1.34 reduction to
the surviving natural L₃(2) block is not asserted here.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Every chi-block alternative is excluded using its actual block action. -/
theorem no_chi_block
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (X : Subgroup I) : ¬ ChapterC.IsChiBlockIn X := by
  intro hX
  exact d.a5_block_false horbit hI hfit hX.1
    (d.chi_block_alternating_five horbit hI hfit hX)

/-- The NI ≤ MI branch of 15.2.23, with the no-chi premise discharged. -/
theorem characteristicTwo_false_of_intersection_le_of_orbit
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hNI : M ⊓ I ≤ Mc ⊓ I) : False :=
  d.characteristicTwo_false_of_intersection_le hI hfit hNI
    (d.no_chi_block horbit hI hfit)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
