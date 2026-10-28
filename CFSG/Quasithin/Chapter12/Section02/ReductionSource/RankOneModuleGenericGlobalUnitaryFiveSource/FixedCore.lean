module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FixedCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Normalizer control for the original chosen U₅(4) fixed Sylow

Apply the represented-actor calculation to the same marking constructed
from the whole-reduced chosen-module input. The full C_T(t), including
outer actors, has its ambient normalizer in the original right-residual
normalizer. The original long root and Hermitian fusion are used literally.

Source: F.4.37(4), printed p.293, in the 12.2.22 application on p.795 of
refs/quasithin.pdf. Ambient Sylow placement and completion are later steps.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive.Descent Theory.SpecificGroups.UnitaryFive.GraphFixed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}
variable (D : ChosenModule T L V)
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
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
include D h hmany hn hpsl hH d hp hc

/-- Full normalizer control on the actual chosen-module marking. -/
theorem rankOne_unitaryFive_represented_fixed_normalizer :
    let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
    ∀ (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse) (P : Sylow 2 r.extension.middle),
      (P : Subgroup r.extension.middle) ⊓ (inner U.Carrier).comap r.extension.middle.subtype =
        ((sourceS L H).subgroupOf (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))).map
          F.middle.toMonoidHom →
      ∀ (t : ↥(normalizer (L : Set G) ⊓ normalizer (residual H : Set G))),
        t.val ∈ (T : Subgroup G) → orderOf t=2 → ∀ u : U.form.unitarySubgroup,
        (F.middle t).val=unitaryConj U.form u*projectiveAut U.form U.matrix →
        (let j := inclusion (inf_le_left.trans r.extension.left_le :
            r.extension.middle ≤ r.extension.carrier)
          ∃ R : Sylow 2 (r.extension.baseHom.range ⊓
              centralizer ({j (F.middle t)} : Set r.extension.carrier) : Subgroup r.extension.carrier),
            (R : Subgroup _).map (r.extension.baseHom.range ⊓
              centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
              ((P : Subgroup r.extension.middle).map j) ⊓
                (r.extension.baseHom.range ⊓ centralizer ({j (F.middle t)} : Set r.extension.carrier))) →
        normalizer (((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) : Set G) ≤
          normalizer (residual H : Set G) := by
  intro r F P hinner t htT ht u hf hsat
  exact d.unitaryFive_represented_fixed_normalizer_le_right
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc
    r F P hinner t htT ht u hf hsat

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
