module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveActor.QuotientNormalization
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Flag-compatible quotient normalization for the chosen original actor

Apply the native plane-Levi normalization to the same original marking,
reversed lift and full middle. The remaining actor has Hermitian quotient
coefficient and satisfies the actual cocycle constraint inherited from the
original involution. This is a quotient normalization, not yet the required
unitary-twist representation on the entire carrier.

Source: Aschbacher–Smith F.4.29(2) and 12.2.22, pp.289,795 of refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.UnitaryFiveFlagAutomorphisms
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The chosen original actor admits normalization by a native flag element. -/
theorem rankOne_unitaryFive_marked_actor_quotient_normalize (D : ChosenModule T L V)
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
    ∃ (b : U.overlap) (β : flagAutomorphisms U),
      b.val ∈ U.rightLocalImage ∧
      ell.action t = innerFlag U b * β ∧
      (F.middle t).val = MulAut.conj b.val * β.val ∧
      rightLinearAction U β = Theory.PSL2.fieldAut U.form.conj ∧
      β * innerFlag U b * β = (innerFlag U b)⁻¹ := by
  exact d.unitaryFive_marked_actor_quotient_normalize
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc r a ell F hF t htT ht htS

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
