module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FixedSylowOrders
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Full fixed-Sylow order comparison in the chosen U₅(4) row

The original whole-reduced input and its constructed marking give the
ambient lower bound 65536 for every involution-centralizer Sylow. For the
same middle map and the inner saturation clause supplied by outer selection,
a represented graph twist has inner fixed Sylow order 256. The actual
source index bounds the full fixed Sylow by 1024, including all outer actors.
Consequently that full intersection cannot be an ambient centralizer Sylow.

This supplies the numerical contradiction following F.4.37 on printed
pp.293--294, in the original 12.2.22 application on p.795. The invariant
long-root geometry needed to prove ambient Sylow placement remains open;
no equality S=T or completion is asserted by this conditional comparison.
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

/-- Fusion into the original plane-core center forces the same lower bound
for every Sylow subgroup of every ambient involution centralizer. -/
theorem rankOne_unitaryFive_involution_centralizer_sylow_lower
    (x : G) (hx : orderOf x=2) (P : Sylow 2 (centralizer ({x} : Set G))) :
    65536 ≤ Nat.card P := by
  exact d.unitaryFive_involution_centralizer_sylow_lower
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc
    (D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc) x hx P

/-- On the same selected maps, inner saturation and a concrete actor formula
give the full fixed-Sylow bound and its incompatibility with ambient placement.
The representation and ambient root argument remain distinct source duties. -/
theorem rankOne_unitaryFive_represented_fixed_sylow_orders :
    let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
    ∀ (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse) (P : Sylow 2 r.extension.middle),
      (P : Subgroup r.extension.middle) ⊓ (inner U.Carrier).comap r.extension.middle.subtype =
        ((sourceS L H).subgroupOf (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))).map
          F.middle.toMonoidHom →
      ∀ (t : ↥(normalizer (L : Set G) ⊓ normalizer (residual H : Set G))),
        orderOf t=2 → ∀ u : U.form.unitarySubgroup,
        (F.middle t).val=unitaryConj U.form u*projectiveAut U.form U.matrix →
        (let j := inclusion (inf_le_left.trans r.extension.left_le :
            r.extension.middle ≤ r.extension.carrier)
          ∃ R : Sylow 2 (r.extension.baseHom.range ⊓
              centralizer ({j (F.middle t)} : Set r.extension.carrier) : Subgroup r.extension.carrier),
            (R : Subgroup _).map (r.extension.baseHom.range ⊓
              centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
              ((P : Subgroup r.extension.middle).map j) ⊓
                (r.extension.baseHom.range ⊓ centralizer ({j (F.middle t)} : Set r.extension.carrier))) →
        Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G)=256 ∧
          Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ 1024 ∧
          ¬ ∃ Q : Sylow 2 (centralizer ({t.val} : Set G)),
            (Q : Subgroup _).map (centralizer ({t.val} : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer ({t.val} : Set G) := by
  intro r F P hinner t ht u hf hsat
  exact d.unitaryFive_represented_fixed_sylow_orders
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc r F P hinner t ht u hf hsat

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
