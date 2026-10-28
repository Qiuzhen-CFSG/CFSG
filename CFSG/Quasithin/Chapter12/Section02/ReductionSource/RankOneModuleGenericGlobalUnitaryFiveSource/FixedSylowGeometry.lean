module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FixedSylowGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# The long-root intersection for the chosen U₅(4) fixed Sylow

Apply the original-source calculation to the whole-reduced chosen-module
input and its same marking. The center–derived subgroup of the FULL C_T(t)
is elementary, nontrivial, of order at most sixteen, and lies in the
sixteen-element center of C_S(t). It meets the original long-root group
nontrivially. The actual representation and inner saturation remain explicit.

Source: F.4.37(4), printed p.293, applied in 12.2.22 on p.795 of
refs/quasithin.pdf. Invariance and ambient Sylow placement remain to be proved.
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

/-- The actual selected maps give the characteristic subgroup and its
nontrivial intersection with the original long root. -/
theorem rankOne_unitaryFive_represented_fixed_geometry :
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
        let I := sourceS L H ⊓ centralizer ({t.val} : Set G)
        let Q := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
        let Z := (center Q ⊓ _root_.commutator Q).map Q.subtype
        (_root_.commutator I = center I ∧ Nat.card (center I)=16 ∧
          IsElementaryAbelian 2 (center I) ∧
          Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧ Nat.card Z ≤ 16 ∧
          Z ≤ (center I).map I.subtype ∧
          normalizer (Q : Set G) ≤ normalizer (Z : Set G)) ∧
        Z ⊓ (center (residual H)).map (residual H).subtype ≠ ⊥ := by
  intro r F P hinner t htT ht u hf hsat
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.unitaryFive_represented_fixed_derived_center hi hH hp U hc
      r F P hinner t ht u hf hsat,
    d.unitaryFive_represented_fixed_derived_meets_root hi hH hp U hc
      r F P hinner t htT ht u hf hsat⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
