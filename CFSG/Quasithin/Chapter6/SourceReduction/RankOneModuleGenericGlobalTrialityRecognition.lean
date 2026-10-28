module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityThompson
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Marked

/-!
# Recognition of the original prepared triality row

The native short-root Sylow theorem and F.4.42 supply the two missing inputs
to Thompson's comparison. This proves the order equality for the extension
constructed from the supplied reversed amalgam isomorphism. Its existing
small-completion recognizer then identifies the ambient group with the actual
triality carrier, at the original exponent m = n > 1, including q = 4.

The catalogue-facing result handles both orientations: the faithful original
left factor excludes the arms-left comparison, and the surviving comparison
uses its own unchanged full-normalizer marking. No centralizer, extension,
order or recognition premise remains. Constructing the comparison for an
arbitrary selected perfect factor is still a separate source obligation.

Source: Aschbacher--Smith F.4.40--44, printed pp.294--296, and 5.3.3--4,
printed p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.TrialityNonbinary TrialityCompletionFusion
variable {G : Type*} [Group G] [Finite G]

/-- Thompson's equality on the very same constructed full-normalizer extension,
with both short-root source inputs discharged. -/
theorem Preparation.triality_ambient_order
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (nativeAmalgam m hm).reverse) :
    Nat.card G = Nat.card (d.trialityNormalizerMarking h hH hp m hm e).extension.carrier := by
  have hmodel := ShortRootCentralizer.centralizer_sylow m hm
    (d.triality_local_structure h hH.1.1.2 hp m hm e).2.1 1 one_ne_zero
  have hshort := d.triality_short_centralizer_full_marked h hH hp m hm e
    (d.trialityNormalizerMarking h hH hp m hm e)
  exact (d.triality_thompson_counts_of_short_centralizer h hH hp m hm e
    (d.trialityNormalizerMarking h hH hp m hm e) hmodel hshort).2.2

/-- The supplied reversed comparison recognizes the actual ambient group and
retains the full-normalizer generation and same-carrier order equality. -/
theorem Preparation.triality_prepared_recognition
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (nativeAmalgam m hm).reverse) :
    let E := (d.trialityNormalizerMarking h hH hp m hm e).extension
    m = n ∧ 1 < m ∧
      normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      Nat.card G = Nat.card E.carrier ∧
      Nonempty (G ≃* BinaryCarrier m hm) ∧ ClassificationModels.IsRankTwoModel G n :=
  d.triality_prepared_extension_recognition_of_order h hH hp m hm e
    (d.triality_ambient_order h hH hp m hm e).le

/-- Both catalogue orientations give the concrete triality model at the original
strictly nonbinary exponent; the arms-left orientation is impossible. -/
theorem Preparation.triality_ambient_recognition
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)) :
    m = n ∧ 1 < m ∧ Nonempty (G ≃* BinaryCarrier m hm) ∧
      ClassificationModels.IsRankTwoModel G n := by
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hH.1.1.2 hp
      (binaryParameters m hm) rfl he).elim
  · obtain ⟨e⟩ := he
    have hr := d.triality_prepared_recognition h hH hp m hm e
    exact ⟨hr.1,hr.2.1,hr.2.2.2.2⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
