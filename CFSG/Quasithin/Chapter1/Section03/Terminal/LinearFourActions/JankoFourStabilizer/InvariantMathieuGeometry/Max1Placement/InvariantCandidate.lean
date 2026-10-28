module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.IntrinsicTransport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Placement

/-!
# Uniqueness and invariance of the local max1 candidate

Every candidate core centralizes
Z(O₂(A)). The ambient centralizer bound puts all these cores inside any one
candidate, where intrinsic uniqueness identifies them. The ambient normalizer
bound then identifies the candidates themselves. Since automorphisms preserving
A preserve the entire candidate family, every candidate is invariant.

The native M₂₄ octad-placement theorem discharges the premise of literal
intrinsic recovery, which transports through each candidate's actual
isomorphism. The ambient recovery theorem independently supplies the two
bounds in J₄. Thus `concreteCandidateFixedPointTheorem` has no remaining
geometric premise beyond candidate existence, as required by its contract.
The stronger invariance theorem needs no restriction on automorphism order.

Source: Aschbacher–Smith A.3.12(17), printed pp.47–48, and the proof of 1.3.9,
p.514; GLS3 Table 5.3i. The geometric contracts and the distinction between
intrinsic and ambient centralizers are documented in `CoreRecovery`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open Section02.LocalModels

/-- Intrinsic core uniqueness and ambient centralizer/normalizer control imply
uniqueness of the entire candidate, including its actual ambient embedding. -/
theorem candidate_eq_of_core_recovery
    (hintrinsic : IntrinsicCoreRecovery) (hambient : AmbientCoreRecovery)
    (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    {H K : Subgroup Janko4.Model} (hH : H ∈ candidates A) (hK : K ∈ candidates A) :
    H = K := by
  obtain ⟨_, hunique⟩ := hintrinsic A H hA hH
  obtain ⟨hcontain, hnormalizerH⟩ := hambient A S H hA hlocal hH
  have hE : K.pCoreIn 2 ∈ centralElementary A :=
    ⟨(hintrinsic A K hA hK).1, core_elementary_and_card_of_candidate hK⟩
  have hcore : K.pCoreIn 2 = H.pCoreIn 2 :=
    hunique _ hE (hE.1.trans hcontain)
  have hNH : normalizer (H.pCoreIn 2 : Set Janko4.Model) = H :=
    le_antisymm hnormalizerH (le_normalizer_core H)
  have hNK : normalizer (K.pCoreIn 2 : Set Janko4.Model) = K :=
    le_antisymm (hambient A S K hA hlocal hK).2 (le_normalizer_core K)
  rw [hcore, hNH] at hNK
  exact hNK

/-- Under core recovery, every automorphism preserving A fixes every candidate.
The two-power-order restriction is unnecessary for this conditional deduction. -/
theorem candidate_invariant_of_core_recovery
    (hintrinsic : IntrinsicCoreRecovery) (hambient : AmbientCoreRecovery)
    (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    {H : Subgroup Janko4.Model} (hH : H ∈ candidates A)
    (α : MulAut Janko4.Model) (hfix : A.map α.toMonoidHom = A) :
    H.map α.toMonoidHom = H :=
  candidate_eq_of_core_recovery hintrinsic hambient A S hA hlocal
    (map_mem_candidates_of_invariant hH α hfix) hH

/-- Conditional assembly of the requested fixed-point contract. Candidate
existence remains exactly the explicit premise of that contract. -/
theorem concreteCandidateFixedPointTheorem_of_core_recovery
    (hintrinsic : IntrinsicCoreRecovery) (hambient : AmbientCoreRecovery) :
    ConcreteCandidateFixedPointTheorem := by
  intro A S hA hlocal hnonempty α _ hfix
  obtain ⟨H, hH⟩ := hnonempty
  exact ⟨H, hH, candidate_invariant_of_core_recovery
    hintrinsic hambient A S hA hlocal hH α hfix⟩

/-- The local calculation may be supplied solely on the literal max1 carrier.
This deduction keeps both geometric inputs explicit for independent reuse. -/
theorem concreteCandidateFixedPointTheorem_of_literal_core_recovery
    (hliteral : LiteralIntrinsicCoreRecovery) (hambient : AmbientCoreRecovery) :
    ConcreteCandidateFixedPointTheorem :=
  concreteCandidateFixedPointTheorem_of_core_recovery
    (intrinsicCoreRecovery_of_literal hliteral) hambient

/-- Native octad placement and the literal binary geometry recover the intrinsic
two-core of every candidate through its supplied isomorphism. -/
theorem intrinsicCoreRecovery : IntrinsicCoreRecovery :=
  intrinsicCoreRecovery_of_literal
    (literalIntrinsicCoreRecovery MathieuLocalSections.octadPlacement)

/-- A source-local L₄(2) section lies in at most one max1 candidate, with
equality of the actual subgroups of J₄. -/
theorem candidate_eq
    (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    {H K : Subgroup Janko4.Model} (hH : H ∈ candidates A) (hK : K ∈ candidates A) :
    H = K :=
  candidate_eq_of_core_recovery intrinsicCoreRecovery ambientCoreRecovery
    A S hA hlocal hH hK

/-- Every automorphism preserving the section fixes each of its max1 candidates. -/
theorem candidate_invariant
    (A : Subgroup Janko4.Model) (S : Sylow 2 Janko4.Model)
    (hA : ClassicalGroup.IsPSL (XiQuotient A) 4 2)
    (hlocal : A ∈ ChapterA.Section03.localCComponents S)
    {H : Subgroup Janko4.Model} (hH : H ∈ candidates A)
    (α : MulAut Janko4.Model) (hfix : A.map α.toMonoidHom = A) :
    H.map α.toMonoidHom = H :=
  candidate_invariant_of_core_recovery intrinsicCoreRecovery ambientCoreRecovery
    A S hA hlocal hH α hfix

/-- A two-power-order automorphism preserving a source-local L₄(2) section
fixes a max1 candidate whenever the candidate family is nonempty. -/
theorem concreteCandidateFixedPointTheorem : ConcreteCandidateFixedPointTheorem :=
  concreteCandidateFixedPointTheorem_of_core_recovery
    intrinsicCoreRecovery ambientCoreRecovery

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
