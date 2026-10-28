module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeOvercomponent
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionRee

/-!
# Excluding Ree overcomponents of the Chapter12 Ree pair

The original compatible Ree comparison fixes the right residual. Its
literal image in a larger local component's two-core quotient, and then
in that quotient's central quotient, cannot have a Ree containing carrier.
Parabolic placement and the Suzuki quotient force the image to have the
same order as the original residual; the resulting injectivity contradicts
the nontrivial containing two-core and its original containment in H.

The full containing-carrier selection now proves right maximality and
the literal normalizer conditions of5.3. Both compatible orientations and
every positive Ree parameter are retained. Exhaustive amalgam comparison,
original uniqueness and ambient completion recognition remain required
for GlobalExit.

Source: Aschbacher–Smith 5.2.8, printed p.652, and the Chapter12 application
on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H J : Subgroup G} (D : ChosenModule T L V)
include D

/-- In the actual Chapter12 Ree branch, a proper containing local component
has neither a Ree two-core quotient nor a central quotient of Ree type. -/
theorem rankOne_global_ree_overcomponent_exclusions
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : residual H < J)
    {k : ℕ} (hk : 0 < k) :
    ¬ Nonempty ((J ⧸ pCore 2 J) ≃* ReeF4.Model k) ∧
      ¬ Nonempty (((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) ≃* ReeF4.Model k) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.not_ree_overcomponent hi hH hp m he hJ hKJ hk,
    d.not_ree_central_overcomponent hi hH hp m he hJ hKJ hk⟩

/-- The actual Ree right residual is maximal and its normalizer pair satisfies
5.3, with the full containing-carrier selection discharged. -/
theorem rankOne_global_ree_normalizer_local_conditions
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse)) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.ree_right_maximal hi hH hp m he,
    d.ree_normalizer_local_conditions hi hH hp m he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
