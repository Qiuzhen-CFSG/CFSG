module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SixFourSupport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalProductSupport

/-!
# Original endpoint application of the support and Omega assertions for (6.4)

Apply the source mixed-commutator product bound and Omega centralization
to the original Suzuki and linear parameters, transported through the
entire marked amalgam equivalence. Hypothesis F.1.1 supplies local
characteristic two at the same Suzuki endpoint. Common-field recognition
discharges the size bound, retaining its explicit odd-linear-degree premise.

The generated-carrier formulas use the literal original quotient map Q.q
and any original lift of the specified normalizer representative. The two
endpoint maps, right conjugation, all Suzuki parameters including zero,
and the potentially infinite original ambient group are retained.

Source: Fong--Seitz I (1973), proof of (6H), printed p.52, before and in
(6.4). These applications establish the two-factor support and the second
assertion of (6.4). Removing the remaining linear factor, the nonzero mixed
commutator equality, pairing and odd-degree discharge, remaining (6H),
Section 10, and the final full-model comparison remain source obligations.
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
/-- The actual original Suzuki and opposite linear parameters satisfy the
two-factor support bound; original local characteristic two supplies the
self-centralizing radical premise. -/
theorem original_six_four_product
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r =
      Q.simple 1*Q.simple 0*Q.simple 1)
    (a b : BinaryGaloisField (2*m+1)) (c : Multiplicative (BinaryGaloisField n)) :
    ⁅endpointMap Q e 1 (originalSuzukiParameter Q e split 1 m μ hB a b),
      (r : X ⧸ Q.D)⁻¹ * endpointMap Q e 0
        (originalRootLift Q e split 0 ((linearRootEquiv Q split 0 ν T hC).symm c)) * r⁆ ^ 2 = 1 ∧
    ⁅endpointMap Q e 1 (originalSuzukiParameter Q e split 1 m μ hB a b),
      (r : X ⧸ Q.D)⁻¹ * endpointMap Q e 0
        (originalRootLift Q e split 0 ((linearRootEquiv Q split 0 ν T hC).symm c)) * r⁆ ∈
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set (X ⧸ Q.D)) *
      (rootAt Q split 0 (Q.simple 1) : Set (X ⧸ Q.D)) := by
  apply (source_six_four_support_of_odd_degree Q split
    (parabolic_core_selfCentralizing Q e h 1) hm n hn m ν T hC μ hB hcore).1
  apply commutator_mem_commutator
  · simpa only [originalSuzukiParameter,originalRootLift_image] using
      (suzukiParameter Q split 1 m μ hB a b).property
  · exact original_opposite_linear_mem Q e split n ν T hC r hr c

include h hm hn ν hC μ hB hcore in
/-- The second assertion of source (6.4) on the original endpoint coordinates. -/
theorem original_six_four_omega_commute
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r =
      Q.simple 1*Q.simple 0*Q.simple 1)
    (b : BinaryGaloisField (2*m+1)) (c : Multiplicative (BinaryGaloisField n)) :
    Commute (endpointMap Q e 1 (originalSuzukiParameter Q e split 1 m μ hB 0 b))
      ((r : X ⧸ Q.D)⁻¹ * endpointMap Q e 0
        (originalRootLift Q e split 0 ((linearRootEquiv Q split 0 ν T hC).symm c)) * r) := by
  have hΩ : endpointMap Q e 1 (originalSuzukiParameter Q e split 1 m μ hB 0 b) ∈
      omegaOneAmbient (simpleRoot Q split 1) := by
    rw [←suzukiOmegaParameter_range Q split 1 m μ hB]
    exact ⟨Multiplicative.ofAdd b,by simp only [originalSuzukiParameter,originalRootLift_image]; rfl⟩
  exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (source_six_four_support_of_odd_degree Q split
      (parabolic_core_selfCentralizing Q e h 1) hm n hn m ν T hC μ hB hcore).2 hΩ) _
      (original_opposite_linear_mem Q e split n ν T hC r hr c)).symm

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

/-- The original linear parameter as an element of the original generated carrier. -/
def originalLinearGeneratedParameter (c : Multiplicative (BinaryGaloisField n)) : generated L S :=
  ⟨originalRootLift Q (originalMarkedIso Q) split 0 ((linearRootEquiv Q split 0 ν T hC).symm c),
    parabolic_le_generated 0 (originalRootLift Q (originalMarkedIso Q) split 0
      ((linearRootEquiv Q split 0 ν T hC).symm c)).property⟩

theorem originalLinearGeneratedParameter_quotient (c : Multiplicative (BinaryGaloisField n)) :
    Q.q (originalLinearGeneratedParameter Q split n ν T hC c) =
      ((linearRootEquiv Q split 0 ν T hC).symm c : (generated L S) ⧸ Q.D) :=
  originalRootLift_quotient Q split 0 ((linearRootEquiv Q split 0 ν T hC).symm c)

include h hm hn ν hC μ hB hcore in
/-- The two-factor bound retains the original quotient map and any original
lift of the specified normalizer element. -/
theorem original_six_four_product_quotient
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r =
      Q.simple 1*Q.simple 0*Q.simple 1)
    (z : generated L S) (hz : Q.q z = r)
    (a b : BinaryGaloisField (2*m+1)) (c : Multiplicative (BinaryGaloisField n)) :
    (Q.q ⁅originalSuzukiGeneratedParameter Q split 1 m μ hB a b,
      z⁻¹ * originalLinearGeneratedParameter Q split n ν T hC c * z⁆)^2 = 1 ∧
    Q.q ⁅originalSuzukiGeneratedParameter Q split 1 m μ hB a b,
      z⁻¹ * originalLinearGeneratedParameter Q split n ν T hC c * z⁆ ∈
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set ((generated L S) ⧸ Q.D)) *
      (rootAt Q split 0 (Q.simple 1) : Set ((generated L S) ⧸ Q.D)) := by
  have hh := original_six_four_product Q (originalMarkedIso Q) split h hm n hn m ν T hC μ hB hcore
    r hr a b c
  simp only [originalRootLift_image,originalSuzukiParameter] at hh
  simpa only [map_commutatorElement,map_mul,map_inv,originalSuzukiGeneratedParameter_quotient,
    originalLinearGeneratedParameter_quotient,hz] using hh

include h hm hn ν hC μ hB hcore in
/-- Literal original Q.q application of the Omega centralization in (6.4). -/
theorem original_six_four_omega_quotient
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r =
      Q.simple 1*Q.simple 0*Q.simple 1)
    (z : generated L S) (hz : Q.q z = r)
    (b : BinaryGaloisField (2*m+1)) (c : Multiplicative (BinaryGaloisField n)) :
    Q.q ⁅originalSuzukiGeneratedParameter Q split 1 m μ hB 0 b,
      z⁻¹ * originalLinearGeneratedParameter Q split n ν T hC c * z⁆ = 1 := by
  have hh := commutatorElement_eq_one_iff_commute.mpr
    (original_six_four_omega_commute Q (originalMarkedIso Q) split h hm n hn m ν T hC μ hB hcore
      r hr b c)
  simp only [originalRootLift_image,originalSuzukiParameter] at hh
  simpa only [map_commutatorElement,map_mul,map_inv,originalSuzukiGeneratedParameter_quotient,
    originalLinearGeneratedParameter_quotient,hz] using hh

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
