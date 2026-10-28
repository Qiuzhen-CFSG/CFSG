module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityThompson
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityLongCentralizer

/-!
# The original triality exit from the designated short-root centralizer

The original chosen module and supplied reversed comparison determine the
published whole-normalizer extension. Native short-root extremality and the
full marked short-root centralizer are the only additional inputs here.
The Chapter 6 Thompson argument proves the full order equality for that
same carrier and the existing completion recognizer gives the actual
triality model at the original exponent greater than one.

These are conditional applications to the literal Chapter 12 setup. The
independent short-root source owner must supply both inputs; this module does
not assert their discharge or exhaustive selected-residual comparison.
Source: Aschbacher--Smith F.4.40--44 and 5.3.3--4, printed pp.294--296,659,
and 12.2.2, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.SourceCompletion.TrialityNonbinary
open Global.TrialityCompletionFusion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Thompson comparison identifies both mixed-pair counts and the full order
of the constructed carrier in the literal chosen-module row. -/
theorem rankOne_global_triality_thompson_of_short_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (nativeAmalgam m hm).reverse)
    (hmodel : ∃ R : Sylow 2 (centralizer
        ({(shortElement (binaryParameters m hm) rfl).val} : Set (BinaryCarrier m hm))),
      (R : Subgroup _) = (unipotent (binaryParameters m hm)).subgroupOf
        (centralizer ({(shortElement (binaryParameters m hm) rfl).val} : Set (BinaryCarrier m hm))))
    (hshort :
      let a := d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
        hH hp m hm e
      let t := (e.right.symm (shortElement (binaryParameters m hm) rfl)).val
      let t' := a.extension.baseHom (shortElement (binaryParameters m hm) rfl).val
      ∃ ht : centralizer ({t} : Set G) ≤ normalizer (L : Set G),
        ∃ kt : centralizer ({t} : Set G) ≃* centralizer ({t'} : Set a.extension.carrier),
          (∀ x, (kt x).val = inclusion a.extension.right_le
            (a.comparison.left (inclusion ht x))) ∧
          kt ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ =
            ⟨t',mem_centralizer_singleton_iff.mpr rfl⟩) :
    let a := d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH hp m hm e
    let P := binaryParameters m hm
    let z := (e.right.symm (longElement P rfl)).val
    let t := (e.right.symm (shortElement P rfl)).val
    let z' := a.extension.baseHom (longElement P rfl).val
    let t' := a.extension.baseHom (shortElement P rfl).val
    TwoInvolutionClassOrder.kappa z t z = TwoInvolutionClassOrder.kappa z' t' z' ∧
      TwoInvolutionClassOrder.kappa z t t = TwoInvolutionClassOrder.kappa z' t' t' ∧
      Nat.card G = Nat.card a.extension.carrier :=
  d.triality_thompson_counts_of_short_centralizer (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm e _ hmodel hshort

/-- The literal global exit follows once the designated short-root owner's
extremality and full marked centralizer are supplied for the same carrier. -/
theorem rankOne_globalExit_of_triality_prepared_short_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (nativeAmalgam m hm).reverse)
    (hmodel : ∃ R : Sylow 2 (centralizer
        ({(shortElement (binaryParameters m hm) rfl).val} : Set (BinaryCarrier m hm))),
      (R : Subgroup _) = (unipotent (binaryParameters m hm)).subgroupOf
        (centralizer ({(shortElement (binaryParameters m hm) rfl).val} : Set (BinaryCarrier m hm))))
    (hshort :
      let a := d.trialityNormalizerMarking (D.rankOne_generic_input_of_many h hmany hn hpsl)
        hH hp m hm e
      let t := (e.right.symm (shortElement (binaryParameters m hm) rfl)).val
      let t' := a.extension.baseHom (shortElement (binaryParameters m hm) rfl).val
      ∃ ht : centralizer ({t} : Set G) ≤ normalizer (L : Set G),
        ∃ kt : centralizer ({t} : Set G) ≃* centralizer ({t'} : Set a.extension.carrier),
          (∀ x, (kt x).val = inclusion a.extension.right_le
            (a.comparison.left (inclusion ht x))) ∧
          kt ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ =
            ⟨t',mem_centralizer_singleton_iff.mpr rfl⟩) :
    RankOneModule.GlobalExit G := by
  have hc := D.rankOne_global_triality_thompson_of_short_centralizer
    h hmany hn hpsl hH d hp m hm e hmodel hshort
  exact D.rankOne_globalExit_of_triality_prepared_extension_order
    h hmany hn hpsl hH d hp m hm e hc.2.2.le

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
