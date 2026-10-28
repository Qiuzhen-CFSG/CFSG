module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.TorusSplitting
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# The actual Sylow complement in the chosen U₅(4) row

The original whole-reduced input and the supplied full-normalizer marking
construct a cyclic complement to S in T. A strict enlargement gives an
actual outer involution. These are applications of the Hall/Frattini proof
of F.4.29(2); graph type, fixed-centralizer Sylow placement, and S=T remain
further obligations.

Source: Aschbacher–Smith F.4.29(2), printed p.289, applied to 5.3.3 and
Chapter12 with the same marked extension and whole residual.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- The same marked row supplies a cyclic complement of its original S. -/
theorem rankOne_global_unitaryFive_sylow_complement
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
    (r : Global.UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) :
    ∃ B : Subgroup G, B ≤ (T : Subgroup G) ∧ Disjoint (Global.sourceS L H) B ∧
      (T : Set G) = (Global.sourceS L H : Set G) * (B : Set G) ∧
      IsCyclic B ∧ Nat.card B = (Global.sourceS L H).relIndex (T : Subgroup G) := by
  exact d.unitaryFive_sylow_complement
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc r

/-- A strict enlargement yields an involution in the original T outside S. -/
theorem rankOne_global_unitaryFive_exists_outer_involution
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
    (r : Global.UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (hST : Global.sourceS L H < (T : Subgroup G)) :
    ∃ t : T, orderOf t=2 ∧ t.val ∉ Global.sourceS L H := by
  exact d.unitaryFive_exists_outer_involution
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc r hST

/-- The constructed marking transports the full original Sylow and its
exact inner intersection, and supplies an outer involution when S<T. -/
theorem rankOne_unitaryFive_marked_sylow_split
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
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) U.amalgam.reverse)) :
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
        (sourceS L H < (T : Subgroup G) →
          ∃ t : D, t.val ∈ (T : Subgroup G) ∧ orderOf t=2 ∧
            F.middle t ∈ (P : Subgroup r.extension.middle) ∧
            (F.middle t).val ∉ ChapterF.SourceCompletion.UnitaryNonbinary.inner U.Carrier) := by
  exact d.unitaryFive_marked_sylow_split
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
