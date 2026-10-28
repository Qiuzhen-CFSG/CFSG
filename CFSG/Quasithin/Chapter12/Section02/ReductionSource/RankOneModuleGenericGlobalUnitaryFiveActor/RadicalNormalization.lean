module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveActor.RadicalNormalization
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five


/-!
# The original chosen U₅ actor's radical normalization

Apply the literal Chapter6 normalization to the same chosen marking and lift.
The remaining quotient-trivial actor has the proved vector and center scalars
and retains the original involution cocycle. Full unitary representation
requires the remaining radical and opposite-endpoint compatibility.

Source: Aschbacher–Smith F.4.29(2) and 12.2.22, printed pp.289,795 of
refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.UnitaryFiveFlagAutomorphisms
open Theory.SpecificGroups.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The chosen original actor admits normalization by a native flag element. -/
theorem rankOne_unitaryFive_marked_actor_radical_normalize (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
      U.amalgam.reverse)
    (ell : UnitaryNativeLift.Five.LiftReverse U a)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
      r.extension.amalgam.reverse)
    (hF : ∀ z, (F.middle z).val = (ell.action z).val)
    (t : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
    (htT : t.val ∈ (T : Subgroup G)) (ht : orderOf t = 2)
    (htS : t.val ∉ sourceS L H) :
    ∃ (b : U.overlap) (γ : flagAutomorphisms U) (k : U.F),
      b.val ∈ U.rightLocalImage ∧ k ≠ 0 ∧
      ell.action t = innerFlag U b * γ * graphFlag U ∧
      (F.middle t).val = MulAut.conj b.val * γ.val * GraphFixed.projectiveAut U.form U.matrix ∧
      rightLinearAction U γ = 1 ∧
      (∀ u : PlaneCore.Parameters U.form, (rightRadicalAction U γ u).x = k • u.x) ∧
      (∀ u : PlaneCore.Parameters U.form, u.x = 0 →
        (rightRadicalAction U γ u).z = (k * U.form.conj k) • u.z) ∧
      (γ * graphFlag U) * innerFlag U b * (γ * graphFlag U) = (innerFlag U b)⁻¹ := by
  exact d.unitaryFive_marked_actor_radical_normalize
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc r a ell F hF t htT ht htS

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
