module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.OuterSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Outer centralizer saturation in the original chosen U₅(4) row

Construct the original whole-reduced Input and its full-normalizer marking.
The selected original outer involution has saturated full and inner native
centralizers on precisely that extension. The endpoint, whole-overlap and
range equations remain those of the constructed marking.

Source: F.4.37, printed p.293, applied to 5.3.3 and 12.2.22. This is native
saturation; graph type and Sylow placement in the ambient completion are
still required before concluding S=T.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The original chosen row supplies an outer involution saturated inside
its same extension and inner subgroup, retaining all marking equations. -/
theorem rankOne_unitaryFive_marked_outer_saturated
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam.reverse))
    (hST : sourceS L H < (T : Subgroup G)) :
    let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
    ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
    ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      r.extension.carrier = ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.left = U.leftParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.right = U.rightParabolic.map MulAut.conj ⊔
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      r.extension.middle =
        ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).subtype.comp f.action).range ∧
      let D := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
      ∃ P : Sylow 2 r.extension.middle,
        (P : Subgroup r.extension.middle) =
          ((T : Subgroup G).subgroupOf D).map F.middle.toMonoidHom ∧
        (P : Subgroup r.extension.middle) ⊓ (ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier).comap r.extension.middle.subtype =
          ((sourceS L H).subgroupOf D).map F.middle.toMonoidHom ∧
        ∃ t : D, t.val ∈ (T : Subgroup G) ∧ orderOf t=2 ∧
          t.val ∉ sourceS L H ∧ F.middle t ∈ (P : Subgroup r.extension.middle) ∧
          (F.middle t).val ∉ ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier ∧
          let j := inclusion (inf_le_left.trans r.extension.left_le :
            r.extension.middle ≤ r.extension.carrier)
          (∃ Q : Sylow 2 (centralizer ({j (F.middle t)} : Set r.extension.carrier)),
            (Q : Subgroup _).map (centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
              ((P : Subgroup r.extension.middle).map j) ⊓
                centralizer ({j (F.middle t)} : Set r.extension.carrier)) ∧
          (∃ R : Sylow 2 (r.extension.baseHom.range ⊓
              centralizer ({j (F.middle t)} : Set r.extension.carrier) : Subgroup r.extension.carrier),
            (R : Subgroup _).map (r.extension.baseHom.range ⊓
              centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
              ((P : Subgroup r.extension.middle).map j) ⊓
                (r.extension.baseHom.range ⊓ centralizer ({j (F.middle t)} : Set r.extension.carrier))) := by
  exact d.unitaryFive_marked_outer_saturated
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc) hST

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
