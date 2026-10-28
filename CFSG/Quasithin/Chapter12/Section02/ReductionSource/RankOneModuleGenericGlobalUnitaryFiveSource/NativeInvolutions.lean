module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.NativeInvolutions
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Native involutions on the original chosen-module marking

Construct the original Input on the whole reduced module from Hypothesis1221
and the many-overgroups assumption. The published marking of that exact row
then supplies native involution coverage in the marked plane-core center and
a selected short involution with full-extension centralizer containment and
its exact original local centralizer order. Every endpoint equation, the
whole-D action and all range equalities stay on this same extension.

Ambient involution coverage, outer transfer, the full ambient F.4.42 equality
and the final same-extension order bound remain separate obligations.
Source: Aschbacher–Smith F.4.35 and F.4.42, pp.292,295, applied at 12.2.22.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Native coverage and the short-root full-extension centralizer on the exact marking
constructed from the original chosen-module row. -/
theorem rankOne_unitaryFive_marked_native_involutions (D : ChosenModule T L V)
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
      (∀ u : U.Carrier, orderOf u = 2 →
        ∃ z : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0,
          z.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
          orderOf z.val = 2 ∧
          IsConj (r.extension.baseHom u)
            (inclusion r.extension.right_le (F.left (inclusion r.left_le z)))) ∧
      (∃ z : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0,
        z.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
        orderOf z.val = 2 ∧ a.comparison.left z = U.shortInvolution ∧
        centralizer ({inclusion r.extension.right_le (F.left (inclusion r.left_le z))} :
          Set r.extension.carrier) ≤ r.extension.right.subgroupOf r.extension.carrier ∧
        Nat.card (centralizer ({inclusion r.left_le z} : Set (normalizer (L : Set G)))) =
          Nat.card (centralizer ({inclusion r.extension.right_le (F.left (inclusion r.left_le z))} :
            Set r.extension.carrier))) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_marked_native_involutions hi hH hp U hc
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
