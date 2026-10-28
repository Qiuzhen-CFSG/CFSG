module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PerpendicularFrattini
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalPositivePerpendicular

/-!
# Original perpendicular support and the binary fixed image

The endpoint markings put the actual original Suzuki parameters into the
same source roots. The narrowed three-factor support and Omega bound apply
to their commutators, and the quotient specialization retains Q.q and an
actual lift of the normalizer word. The binary two-core equivalence supplies
the perpendicular image fixed by the actual quintic element on V/Φ(V),
together with the bound of four for that fixed subgroup.

Source: Fong--Seitz I (1973), (6H), printed p.54. These are intermediate
support and fixed-image assertions, not binary perpendicular commutation.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
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
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

private theorem perpendicular_parameter_mem
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r =
      Q.simple 0*Q.simple 1*Q.simple 0)
    (c d : BinaryGaloisField (2*m+1)) :
    (r : X ⧸ Q.D)⁻¹ * endpointMap Q e 1
      (originalSuzukiParameter Q e split 1 m μ hB c d) * r ∈
        rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0) := by
  rw [originalSuzukiParameter,originalRootLift_image,rootAt_eq Q split 1 _ r hr]
  change (r : X ⧸ Q.D)*((r : X ⧸ Q.D)⁻¹*
    (suzukiParameter Q split 1 m μ hB c d : X ⧸ Q.D)*r)*(r : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split 1
  simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using
    (suzukiParameter Q split 1 m μ hB c d).property

include ν hC μ hB hn in
/-- Narrow perpendicular product support on the actual original root parameters, including q=2. -/
theorem original_source_perpendicular_product_support
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8)
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r =
      Q.simple 0*Q.simple 1*Q.simple 0)
    (a b c d : BinaryGaloisField (2*m+1)) :
    ⁅endpointMap Q e 1 (originalSuzukiParameter Q e split 1 m μ hB a b),
      (r : X ⧸ Q.D)⁻¹ * endpointMap Q e 1
        (originalSuzukiParameter Q e split 1 m μ hB c d) * r⁆ ∈
      (rootAt Q split 0 (Q.simple 1) : Set (X ⧸ Q.D)) *
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set (X ⧸ Q.D)) *
      (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) := by
  apply source_perpendicular_product_support Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)
  apply commutator_mem_commutator
  · simpa only [originalSuzukiParameter,originalRootLift_image] using
      (suzukiParameter Q split 1 m μ hB a b).property
  · exact perpendicular_parameter_mem Q e split m μ hB r hr c d

include ν hC μ hB hn in
/-- The original Omega acts on the perpendicular root only into the shifted Omega. -/
theorem original_source_omega_perpendicular_le
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8)
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r =
      Q.simple 0*Q.simple 1*Q.simple 0)
    (b c d : BinaryGaloisField (2*m+1)) :
    ⁅endpointMap Q e 1 (originalSuzukiParameter Q e split 1 m μ hB 0 b),
      (r : X ⧸ Q.D)⁻¹ * endpointMap Q e 1
        (originalSuzukiParameter Q e split 1 m μ hB c d) * r⁆ ∈
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
  apply source_omega_perpendicular_le Q split n hn m ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)
  apply commutator_mem_commutator
  · rw [←suzukiOmegaParameter_range Q split 1 m μ hB]
    exact ⟨Multiplicative.ofAdd b,by simp only [originalSuzukiParameter,originalRootLift_image]; rfl⟩
  · exact perpendicular_parameter_mem Q e split m μ hB r hr c d

omit m μ hB in
include ν hC hn in
/-- The original binary core supplies the fixed perpendicular image and the fixed-space bound. -/
theorem original_binary_perpendicular_frattini_fixed
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup 0 : Set _))
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8)
    (v : pCore 2 (parabolic L S 1))
    (hv : endpointMap Q e 1 v ∈ rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) :
    let hV := marked_suzuki_remainder_le_kernel Q split 1 0 μ hB
    let v' := originalRadicalEquiv Q e split 1 hV v
    let a := quotientAut (frattini (simpleRemainder Q split 1))
      ((radicalSection Q split 1 hV).numeratorAction (frattiniMover Q split 1 0 μ hB))
    a (QuotientGroup.mk' (frattini (simpleRemainder Q split 1)) v') =
        QuotientGroup.mk' (frattini (simpleRemainder Q split 1)) v' ∧
      Nat.card a.fixedSubgroup ≤ 4 := by
  dsimp only
  exact ⟨source_binary_perpendicular_frattini_fixed Q split n hn ν T hC μ hB hm
    (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1) _ hv,
    source_binary_mover_frattini_fixed_card_le Q split n hn ν T hC μ hB hm
      (LinearThreePresentation.borel_core_eq_bot Q e h) (parabolic_core_selfCentralizing Q e h 1)⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

include ν hC μ hB hn in
/-- The narrowed product support through literal Q.q and an actual lift of the reflection word. -/
theorem original_source_perpendicular_product_support_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8)
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r =
      Q.simple 0*Q.simple 1*Q.simple 0)
    (z : generated L S) (hz : Q.q z = r)
    (a b c d : BinaryGaloisField (2*m+1)) :
    Q.q ⁅originalSuzukiGeneratedParameter Q split 1 m μ hB a b,
      z⁻¹ * originalSuzukiGeneratedParameter Q split 1 m μ hB c d * z⁆ ∈
      (rootAt Q split 0 (Q.simple 1) : Set ((generated L S) ⧸ Q.D)) *
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set ((generated L S) ⧸ Q.D)) *
      (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set ((generated L S) ⧸ Q.D)) := by
  have hh := original_source_perpendicular_product_support Q (originalMarkedIso Q) split n hn m ν T hC μ hB
    h hm r hr a b c d
  simp only [originalRootLift_image,originalSuzukiParameter] at hh
  simpa only [map_commutatorElement,map_mul,map_inv,originalSuzukiGeneratedParameter_quotient,hz] using hh

include ν hC μ hB hn in
/-- Literal Q.q application of the Omega-perpendicular bound, including q=2. -/
theorem original_source_omega_perpendicular_le_quotient
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8)
    (r : Q.tits.N)
    (hr : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) r =
      Q.simple 0*Q.simple 1*Q.simple 0)
    (z : generated L S) (hz : Q.q z = r)
    (b c d : BinaryGaloisField (2*m+1)) :
    Q.q ⁅originalSuzukiGeneratedParameter Q split 1 m μ hB 0 b,
      z⁻¹ * originalSuzukiGeneratedParameter Q split 1 m μ hB c d * z⁆ ∈
      omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) := by
  have hh := original_source_omega_perpendicular_le Q (originalMarkedIso Q) split n hn m ν T hC μ hB
    h hm r hr b c d
  simp only [originalRootLift_image,originalSuzukiParameter] at hh
  simpa only [map_commutatorElement,map_mul,map_inv,originalSuzukiGeneratedParameter_quotient,hz] using hh

omit m μ hB in
include ν hC hn in
/-- The binary fixed-image step uses the literal Q.q image of the original two-core. -/
theorem original_binary_perpendicular_frattini_fixed_quotient
    (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup 0)
    (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup 0 : Set _))
    (h : HypothesisF11 L S) (hm : rotationOrder Q = 8)
    (v : pCore 2 (parabolic L S 1))
    (hv : Q.q (inclusion (parabolic_le_generated 1) v.val) ∈
      rootAt Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) :
    let hV := marked_suzuki_remainder_le_kernel Q split 1 0 μ hB
    let v' := originalRadicalEquiv Q (originalMarkedIso Q) split 1 hV v
    let a := quotientAut (frattini (simpleRemainder Q split 1))
      ((radicalSection Q split 1 hV).numeratorAction (frattiniMover Q split 1 0 μ hB))
    a (QuotientGroup.mk' (frattini (simpleRemainder Q split 1)) v') =
        QuotientGroup.mk' (frattini (simpleRemainder Q split 1)) v' ∧
      Nat.card a.fixedSubgroup ≤ 4 := by
  apply original_binary_perpendicular_frattini_fixed Q (originalMarkedIso Q) split n hn ν T hC μ hB h hm v
  have he := originalRadicalEquiv_quotient Q split 1
    (marked_suzuki_remainder_le_kernel Q split 1 0 μ hB) v
  change MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 v.val = _ at he
  rw [he]
  exact hv

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
