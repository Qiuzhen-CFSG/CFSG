module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.GraphFlagNormalization
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# The original fixed native flag in the chosen U₅(4) row

Construct the whole-reduced Input and its published full-normalizer marking.
For a middle involution represented by a unitary graph twist, construct a
flag-preserving graph conjugator. Its fixed-group equivalence retains both
original native endpoints and the whole middle on the same extension and
literal base map. No additional flag-conjugacy witness is required.

Source: F.4.29(2), F.4.37(2) and 12.2.22, printed pp.289,293,795 of
refs/quasithin.pdf. Representation of the selected abstract outer actor and
full fixed-Sylow root geometry remain unproved source inputs.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
open Theory.SpecificGroups.UnitaryFive
open GraphFixed Descent
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Apply the constructed flag conjugator to the original chosen-module marking. -/
theorem rankOne_unitaryFive_unitary_twist_fixed_native_flag (D : ChosenModule T L V)
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
    ∀ (f : r.extension.middle), f^2=1 →
      ∀ u : U.form.unitarySubgroup,
      f.val=unitaryConj U.form u*projectiveAut U.form U.matrix →
    ∃ b : Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U,
      let j := inclusion (inf_le_left.trans r.extension.left_le : r.extension.middle ≤ r.extension.carrier)
      f.val=b.val*projectiveAut U.form U.matrix*b.val⁻¹ ∧
      ∃ e : (projectiveAut U.form U.matrix).fixedSubgroup ≃*
          (r.extension.baseHom.range ⊓ centralizer ({j f} : Set r.extension.carrier) : Subgroup r.extension.carrier),
        (∀ x, (e x).val=r.extension.baseHom (b.val x.val)) ∧
        (∀ x, (e x).val∈r.extension.family false ↔ x.val∈U.leftParabolic) ∧
        (∀ x, (e x).val∈r.extension.family true ↔ x.val∈U.rightParabolic) ∧
        (∀ x, (e x).val∈r.extension.middle.subgroupOf r.extension.carrier ↔ x.val∈U.overlap) := by
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n :=
    D.rankOne_generic_input_of_many h hmany hn hpsl
  let r := d.unitaryFiveNormalizerMarking hi hH hp U hc
  exact fun f hf2 u hf => unitary_twist_fixed_native_flag U r.extension f hf2 u hf

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
