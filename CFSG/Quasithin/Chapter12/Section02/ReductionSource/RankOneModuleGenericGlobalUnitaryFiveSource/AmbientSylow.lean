module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.AmbientSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five

/-!
# Ambient fixed-Sylow placement and conditional S=T in the chosen U₅(4) row

Both saturation clauses come from the same original marked extension.
The represented actor supplies invariant long-root geometry; transporting
full saturation through its literal endpoint map proves that the whole
C_T(t) is Sylow in C_G(t). The proved 1024-versus-65536 order comparison
then excludes such a selected outer actor.

The chosen-module equality S=T has only the concrete actor representation
as a remaining earlier premise. It is not unconditional source recognition.
Source: F.4.37--38, pp.293--294, applied in 12.2.22, p.795 of refs/quasithin.pdf.
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

/-- Ambient placement of the FULL original fixed Sylow on the same maps. -/
theorem rankOne_unitaryFive_represented_fixed_ambient_sylow :
    let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
    ∀
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
      r.extension.amalgam.reverse)
    (P : Sylow 2 r.extension.middle)
    (_hP : (P : Subgroup r.extension.middle) =
      ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))).map
        F.middle.toMonoidHom)
    (_hinner : (P : Subgroup r.extension.middle) ⊓
      (inner U.Carrier).comap r.extension.middle.subtype =
      ((sourceS L H).subgroupOf (normalizer (L : Set G) ⊓ normalizer (residual H : Set G))).map
        F.middle.toMonoidHom)
    (t : ↥(normalizer (L : Set G) ⊓ normalizer (residual H : Set G)))
    (_htT : t.val ∈ (T : Subgroup G))
    (_ht : orderOf t=2) (u : U.form.unitarySubgroup)
    (_hf : (F.middle t).val=unitaryConj U.form u*projectiveAut U.form U.matrix)
    (_hfull : let j := inclusion (inf_le_left.trans r.extension.left_le :
        r.extension.middle ≤ r.extension.carrier)
      ∃ R : Sylow 2 (centralizer ({j (F.middle t)} : Set r.extension.carrier)),
        (R : Subgroup _).map (centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
          ((P : Subgroup r.extension.middle).map j) ⊓
            centralizer ({j (F.middle t)} : Set r.extension.carrier))
    (_hsat : let j := inclusion (inf_le_left.trans r.extension.left_le :
        r.extension.middle ≤ r.extension.carrier)
      ∃ R : Sylow 2 (r.extension.baseHom.range ⊓
          centralizer ({j (F.middle t)} : Set r.extension.carrier) : Subgroup r.extension.carrier),
        (R : Subgroup _).map (r.extension.baseHom.range ⊓
          centralizer ({j (F.middle t)} : Set r.extension.carrier)).subtype =
          ((P : Subgroup r.extension.middle).map j) ⊓
            (r.extension.baseHom.range ⊓ centralizer ({j (F.middle t)} : Set r.extension.carrier))),
    ∃ Q : Sylow 2 (centralizer ({t.val} : Set G)),
      (Q : Subgroup _).map (centralizer ({t.val} : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer ({t.val} : Set G) := by
  intro r F P _hP _hinner t _htT _ht u _hf _hfull _hsat
  exact d.unitaryFive_represented_fixed_ambient_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc
    r F P _hP _hinner t _htT _ht u _hf _hfull _hsat

/-- The selected-actor representation is the sole remaining earlier premise. -/
theorem rankOne_unitaryFive_sourceS_eq_sylow_of_actor_representation :
    let r := D.rankOne_unitaryFiveNormalizerMarking h hmany hn hpsl hH d hp U hc
    ∀
    (_hrep : ∀ (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse)
      (ell : UnitaryNativeLift.Five.LiftReverse U a)
      (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
        r.extension.amalgam.reverse),
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) →
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) →
      (∀ z, (F.middle z).val = (ell.action z).val) →
      ∀ t : ↥(normalizer (L : Set G) ⊓ normalizer (residual H : Set G)),
        t.val ∈ (T : Subgroup G) → orderOf t=2 → t.val ∉ sourceS L H →
        ∃ u : U.form.unitarySubgroup,
          (F.middle t).val=unitaryConj U.form u*projectiveAut U.form U.matrix),
    sourceS L H = (T : Subgroup G) := by
  intro r _hrep
  exact d.unitaryFive_sourceS_eq_sylow_of_actor_representation
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp U hc r _hrep

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
