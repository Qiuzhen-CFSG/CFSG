module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SixFour
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalSixFourSupport

/-!
# Original endpoint and quotient application of source (6.4)

The mixed commutator of the original Suzuki parameter and the indicated
conjugated linear parameter lies in the single shifted Suzuki Omega root.
The Frattini argument in SixFour removes the former extra linear factor.
Hypothesis F.1.1 supplies the self-centralizing endpoint two-core; the
common-field theorem supplies the order bound, retaining its odd-degree
premise. All parameters, including Sz(2), are included.

The final formula uses the literal generated-carrier quotient Q.q and any
lift of the specified normalizer representative. The complete marked
amalgam and both endpoint maps are unchanged. The Omega centralization
assertion is already supplied by OriginalSixFourSupport.

Source: Fong--Seitz I (1973), proof of (6H), printed p.52, (6.4).
Rank-one pairing, odd degree, the nonzero mixed-commutator equalities,
remaining (6H), Section 10 and the full marked comparison remain required.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits)
  (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (hcore : Q.tits.B.normalCore = ⊥)


private theorem original_opposite_linear_mem
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r =
      Q.simple 1*Q.simple 0*Q.simple 1)
    (c : Multiplicative (BinaryGaloisField n)) :
    (r : X ⧸ Q.D)⁻¹ * endpointMap Q e 0
      (originalRootLift Q e split 0 ((linearRootEquiv Q split 0 ν T hC).symm c)) * r ∈
      rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) := by
  rw [originalRootLift_image,rootAt_eq Q split 0 _ r hr]
  change (r : X ⧸ Q.D)*((r : X ⧸ Q.D)⁻¹*
    ((linearRootEquiv Q split 0 ν T hC).symm c : X ⧸ Q.D)*r)*(r : X ⧸ Q.D)⁻¹ ∈
      simpleRoot Q split 0
  simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using
    ((linearRootEquiv Q split 0 ν T hC).symm c).property

include h hm hn ν hC μ hB hcore in
/-- Source (6.4)'s first assertion on the actual original endpoint parameters. -/
theorem original_six_four_le_omega
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r =
      Q.simple 1*Q.simple 0*Q.simple 1)
    (a b : BinaryGaloisField (2*m+1)) (c : Multiplicative (BinaryGaloisField n)) :
    ⁅endpointMap Q e 1 (originalSuzukiParameter Q e split 1 m μ hB a b),
      (r : X ⧸ Q.D)⁻¹ * endpointMap Q e 0
        (originalRootLift Q e split 0 ((linearRootEquiv Q split 0 ν T hC).symm c)) * r⁆ ∈
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
  apply (source_six_four_of_odd_degree Q split
    (parabolic_core_selfCentralizing Q e h 1) hm n hn m ν T hC μ hB hcore).1
  apply commutator_mem_commutator
  · simpa only [originalSuzukiParameter,originalRootLift_image] using
      (suzukiParameter Q split 1 m μ hB a b).property
  · exact original_opposite_linear_mem Q e split n ν T hC r hr c

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (hcore : Q.tits.B.normalCore = ⊥)

include h hm hn ν hC μ hB hcore in
/-- The actual source (6.4) containment through the literal map Q.q. -/
theorem original_six_four_le_omega_quotient
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r =
      Q.simple 1*Q.simple 0*Q.simple 1)
    (z : generated L S) (hz : Q.q z = r)
    (a b : BinaryGaloisField (2*m+1)) (c : Multiplicative (BinaryGaloisField n)) :
    Q.q ⁅originalSuzukiGeneratedParameter Q split 1 m μ hB a b,
      z⁻¹ * originalLinearGeneratedParameter Q split n ν T hC c * z⁆ ∈
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
  have hh := original_six_four_le_omega Q (originalMarkedIso Q) split h hm n hn m ν T hC μ hB hcore
    r hr a b c
  simp only [originalRootLift_image,originalSuzukiParameter] at hh
  simpa only [map_commutatorElement,map_mul,map_inv,originalSuzukiGeneratedParameter_quotient,
    originalLinearGeneratedParameter_quotient,hz] using hh

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
