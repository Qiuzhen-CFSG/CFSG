module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.EndpointFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Full endpoint class predicates in the original U₅(4) row

The same original full-normalizer maps preserve ambient conjugacy to each
plane-core central involution throughout both endpoints. The result uses
the proved S=T and compatible fixed-path transport, and retains the exact
marking, whole residual and extension used by the chosen module.

Source: 12.2.22 and F.4.35,42–43, printed pp.795,292,295–296.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Literal whole-endpoint fusion for each marked plane-center involution. -/
theorem rankOne_unitaryFive_marked_endpoint_classes
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse)) :
    let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
    ∀ (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse)
      (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse),
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) →
      ∀ (z : normalizer (L : Set G)),
        z.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype → orderOf z.val=2 →
      (∀ x : normalizer (L : Set G), IsConj z.val x.val ↔
        IsConj (UnitaryFiveFusion.markedLeftHom r F z) (UnitaryFiveFusion.markedLeftHom r F x)) ∧
      (∀ x : normalizer (residual H : Set G), IsConj z.val x.val ↔
        IsConj (UnitaryFiveFusion.markedLeftHom r F z) (UnitaryFiveFusion.markedRightHom r F x)) := by
  intro r a F h0 z hz hz2
  exact ⟨UnitaryFiveFusion.marked_left_class d
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc r a F h0 z hz hz2,
    UnitaryFiveFusion.marked_right_class d
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc r a F h0 z hz hz2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
