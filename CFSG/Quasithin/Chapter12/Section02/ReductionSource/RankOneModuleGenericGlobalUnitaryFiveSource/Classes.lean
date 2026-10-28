module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Classes
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Two inner involution types on the chosen-module marking

Construct the original Input with W equal to the whole reduced module, then
apply the proved two-class center theorem on the marking of that same row.
The two original representatives do not fuse in G, and they exhaust the
nonidentity plane-core center. Fusion there agrees in G, the native carrier,
the full extension and the original reduced endpoint. Every native involution
belongs to one of the two corresponding extension classes.

The exact endpoint equations, whole-common-normalizer equation and all range
identities are retained. Ambient outer involutions, transfer and F.4.42 remain
additional source steps; this theorem asserts no ambient order comparison.
Source: Aschbacher–Smith F.4.35, printed p.292, applied at 12.2.22.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Two native types and exact center fusion on the marking constructed from
the original chosen-module row. -/
theorem rankOne_unitaryFive_marked_center_classes (D : ChosenModule T L V)
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
        IsConj (inclusion r.extension.right_le (F.left (inclusion r.left_le t))) (r.extension.baseHom u)) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_marked_center_classes hi hH hp U hc
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
