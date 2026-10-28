module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.AmbientClasses
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# The two ambient U₅(4) involution classes in the chosen-module row

Construct Input on the whole reduced module and use the published marking of
that same prepared row. Cyclic transfer and fixed-path fusion now make the
marked long and short representatives exhaustive among all involutions of
G. They remain nonconjugate, and all endpoint, whole-middle, carrier/range,
native-coverage and center-fusion conclusions use this identical extension.

The original KnownSimple, proper-K, many-overgroups and quotient hypotheses
are retained. The original ambient Sylow equality, full short-centralizer
argument and same-extension order comparison remain separate obligations.
Source: Aschbacher–Smith F.4.30,35,38, applied at 12.2.22, pp.290–294,795.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Exactly two ambient involution classes on the marking constructed from
the original chosen-module row, with all original marking equations retained. -/
theorem rankOne_unitaryFive_marked_ambient_classes (D : ChosenModule T L V)
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
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
    ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
    ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      r.extension.carrier = inner U.Carrier ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.left = U.leftParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.right = U.rightParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.middle =
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0
      let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
      let z : P := a.comparison.left.symm U.longInvolution
      let t : P := a.comparison.left.symm U.shortInvolution
      z.val ∈ Z ∧ t.val ∈ Z ∧ orderOf z.val = 2 ∧ orderOf t.val = 2 ∧
      ¬ IsConj z.val t.val ∧
      (∀ x : P, x.val ∈ Z → x ≠ 1 → IsConj z x ∨ IsConj t x) ∧
      (∀ x y : P, x.val ∈ Z → y.val ∈ Z →
        (IsConj x.val y.val ↔ IsConj (a.comparison.left x).val (a.comparison.left y).val) ∧
        (IsConj x.val y.val ↔ IsConj
          (inclusion r.extension.right_le (F.left (inclusion r.left_le x)))
          (inclusion r.extension.right_le (F.left (inclusion r.left_le y)))) ∧
        (IsConj x.val y.val ↔ IsConj x y)) ∧
      (∀ u : U.Carrier, orderOf u = 2 →
        IsConj (inclusion r.extension.right_le (F.left (inclusion r.left_le z))) (r.extension.baseHom u) ∨
        IsConj (inclusion r.extension.right_le (F.left (inclusion r.left_le t))) (r.extension.baseHom u)) ∧
      (∀ x : G, orderOf x = 2 → IsConj z.val x ∨ IsConj t.val x) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_marked_ambient_classes hi hH hp U hc
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
