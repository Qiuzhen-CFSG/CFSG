module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.CoreRecovery
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.CandidateConjugacy
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralNormalizer

/-!
# Ambient core recovery for J₄ max1 candidates

Every source-local max1 candidate is conjugate to the literal max1 subgroup.
Transporting the proved literal centralizer and core-normalizer bounds along
this conjugation gives both ambient bounds for the original candidate. The
transport preserves its intrinsic Sylow-local witness and the section's
ambient Sylow-local witness separately.

The three concrete geometry theorems discharge every premise of the transport
reduction. No intrinsic core recovery or ambient simplicity or perfectness
assumption is needed.

Source: Aschbacher–Smith A.3.12(17), printed pp.47–48, and the proof of
1.3.9, p.514; GLS3 Table 5.3i. See `AmbientGeometry.Reduction` for the exact
contracts and the distinction between intrinsic and ambient control.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement

/-- For every source-local L₄(2) section and max1 candidate H, both the ambient
centralizer of Z(O₂(A)) and the ambient normalizer of O₂(H) lie in H. -/
theorem ambientCoreRecovery : AmbientCoreRecovery :=
  AmbientGeometry.ambientCoreRecovery_of_literal_geometry
    AmbientGeometry.candidateConjugacy AmbientGeometry.literalCentralizerControl
    AmbientGeometry.literalCoreNormalizerControl

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
