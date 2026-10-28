module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FullLongCentralizers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Centralizer comparisons on the original chosen unitary-five row

Construct the original Input on the whole reduced module from the many-overgroups
hypothesis. The published marking of this very row then transports full long-root
centralizers, plane-center fusion and centralizer two-parts to its same extension.
Every local premise in these comparisons is discharged by the Chapter6 proofs.

Outer transfer, involution coverage and the full short-root centralizer argument
remain necessary for the ambient order theorem. Source: Aschbacher–Smith
F.4.35–43, printed pp.292–296, as applied in 12.2.22, printed p.795.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.UnitaryNonbinary
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Plane-center fusion and centralizer two-parts on the exact chosen marking. -/
theorem rankOne_unitaryFive_marked_plane_centralizers (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam.reverse)) :
    let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
    (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam,
      ∃ f : UnitaryNativeLift.Five.Lift U a,
      ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H)) r.extension.amalgam,
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
        (∀ x : normalizer (L : Set G),
          x.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype →
          (Nat.card (centralizer ({x.val} : Set G))).factorization 2 =
            (Nat.card (centralizer ({F.left x} : Set r.extension.left))).factorization 2) ∧
        (∀ x y : normalizer (L : Set G),
          x.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype →
          y.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype →
          (IsConj x.val y.val ↔ IsConj (F.left x) (F.left y)))) ∨
    (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
      ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
      ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H)) r.extension.amalgam.reverse,
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
        (∀ x : normalizer (L : Set G),
          x.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype →
          (Nat.card (centralizer ({x.val} : Set G))).factorization 2 =
            (Nat.card (centralizer ({F.left x} : Set r.extension.right))).factorization 2) ∧
        (∀ x y : normalizer (L : Set G),
          x.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype →
          y.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype →
          (IsConj x.val y.val ↔ IsConj (F.left x) (F.left y)))) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_marked_plane_centralizers hi hH hp U hc
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc)

/-- Full long-root centralizer placement and order on the exact chosen marking. -/
theorem rankOne_unitaryFive_marked_full_long_centralizers (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam.reverse)) :
    let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
    (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
      ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
      ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H)) r.extension.amalgam.reverse,
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
        (∀ z : normalizer (residual H : Set G),
          z.val ∈ (center (residual H)).map (residual H).subtype → orderOf z.val = 2 →
          centralizer ({inclusion r.extension.left_le (F.right z)} : Set r.extension.carrier) ≤
            r.extension.left.subgroupOf r.extension.carrier ∧
          Nat.card (centralizer ({z.val} : Set G)) =
            Nat.card (centralizer
              ({inclusion r.extension.left_le (F.right z)} : Set r.extension.carrier)))) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  exact d.unitaryFive_marked_full_long_centralizers hi hH hp U hc
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
