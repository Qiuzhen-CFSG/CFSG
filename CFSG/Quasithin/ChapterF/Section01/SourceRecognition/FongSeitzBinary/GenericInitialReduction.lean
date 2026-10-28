module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MinimalConfiguration
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The initial Fong–Seitz reduction for the Chapter 12 pair

The actual preparation gives F.1.1 for ![L,R] and S = O₂(N_G(L) ∩ H).
MinimalConfiguration therefore constructs the canonical G₀/Z equivalence
and an isomorphism from the original inclusion amalgam, preserving both
endpoint maps and the whole Borel. Its subgroup equation includes N, U,
the Borel and both standard parabolics. The relative reduction kernel is
proved trivial; neither perfectness of R nor a recognized Lie row is assumed.

This discharges the initial-reduction premise of the Fong–Seitz invocation
for the literal Chapter 12 consumer. The independently constructed marked
split quotient and the remaining source profile and Lie comparisons still
require their source producers. Full KnownSimple and proper-K hypotheses
are retained in the actual Chapter 12 input.

Source: Fong–Seitz I, Theorem A and (1A)–(1D), pp.1–4, and §§2–3,
pp.7,12; DGS Theorem D, p.224; Aschbacher–Smith 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The exact Chapter 12 pair admits the canonical initial reduction with
both marked endpoint squares, the full Borel, and every subgroup image retained. -/
theorem rankOne_global_marked_initial_reduction
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) :
    ∃ η : split.InitialQuotient ≃* (X ⧸ Q.D),
      ∃ a : RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
        (MarkedLocal.sourceInitialAmalgam Q split),
        split.initialCore = ⊥ ∧
        (∀ M : Subgroup (X ⧸ Q.D), (split.initialSubgroup M).map η.toMonoidHom = M) ∧
        (∀ x : parabolic ![L,R] (Global.sourceS L H) 0,
          η (a.left x) = MarkedLocal.endpointMap Q e 0 x) ∧
        (∀ x : (parabolic ![L,R] (Global.sourceS L H) 0 ⊓
            parabolic ![L,R] (Global.sourceS L H) 1 : Subgroup G),
          η (a.middle x) = (e.middle x : X ⧸ Q.D)) ∧
        (∀ x : parabolic ![L,R] (Global.sourceS L H) 1,
          η (a.right x) = MarkedLocal.endpointMap Q e 1 x) := by
  have hh := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  have hm := MarkedLocal.source_minimal_configuration Q e hh split
  refine ⟨MarkedLocal.sourceInitialEquiv Q e hh split,
    MarkedLocal.sourceInitialMarkedIso Q e hh split,
    split.initialCore_eq_bot hm.1 hm.2.1, ?_, ?_, ?_, ?_⟩
  · exact split.initialEquiv_subgroup hm.1 hm.2.1
  · exact MarkedLocal.sourceInitialMarkedIso_left_apply Q e hh split
  · exact MarkedLocal.sourceInitialMarkedIso_middle_apply Q e hh split
  · exact MarkedLocal.sourceInitialMarkedIso_right_apply Q e hh split

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
