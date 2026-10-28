module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.MixedBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearLocal

/-!
# Original marked applications of the first mixed Ree source bounds

The naturally marked linear and Suzuki radicals pull back to the actual
two-cores of the original full endpoints. The mixed bounds (6.2)--(6.3)
are applied to the original lifted root coordinates and the specified
normalizer element, with right conjugation and the literal endpoint maps.
The generated-carrier specialization expresses (6.3) through the original
Q.q, including any chosen original lift of that normalizer element.

The full original or geometric amalgam marking is retained, with either
endpoint orientation. The ambient group may be infinite; the Suzuki
parameter may be zero. No perfectness or common-field premise is added.
The preceding natural faithful-panel markings remain explicit inputs.

Source: Fong--Seitz I (1973), (2B), pp.7--9, and (6.2)--(6.3), p.52.
These proved mixed bounds feed the (6H)/Section 10 construction; they do
not supply the remaining equality, module recognition or final amalgam
comparison required by the original Chapter12 consumer.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (i j : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

include μ hB in
/-- The source radical is the actual original endpoint two-core, including
Sz(2), under its natural faithful-panel marking. -/
theorem original_marked_suzuki_remainder_comap :
    (simpleRemainder Q split i).comap (endpointMap Q e i) =
      pCore 2 (parabolic L S i) :=
  remainder_comap_of_containment Q e split i
    (marked_suzuki_remainder_le_kernel Q split i m μ hB)

include ν hC in
theorem original_marked_linear_remainder_comap :
    (simpleRemainder Q split j).comap (endpointMap Q e j) =
      pCore 2 (parabolic L S j) :=
  remainder_comap_of_containment Q e split j
    (marked_linear_remainder_le_kernel Q split j ν T hC)

private theorem conjugated_parameter_mem (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n =
      Q.simple j*Q.simple i) (c d : BinaryGaloisField (2*m+1)) :
    (n : X ⧸ Q.D)⁻¹ * endpointMap Q e i (originalSuzukiParameter Q e split i m μ hB c d) * n ∈
      rootAt Q split i (Q.simple j*Q.simple i) := by
  simp only [originalSuzukiParameter, originalRootLift_image]
  rw [rootAt_eq Q split i _ n hn]
  change (n : X ⧸ Q.D)*((n : X ⧸ Q.D)⁻¹ *
    (suzukiParameter Q split i m μ hB c d : X ⧸ Q.D)*n)*(n : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using
    (suzukiParameter Q split i m μ hB c d).property

include ν hC in
/-- The original marked endpoint representatives satisfy the mixed bound,
with the actual right-conjugating normalizer element. -/
theorem original_suzuki_mixed_bound (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n =
      Q.simple j*Q.simple i) (a b c d : BinaryGaloisField (2*m+1)) :
    ⁅endpointMap Q e i (originalSuzukiParameter Q e split i m μ hB a b),
      (n : X ⧸ Q.D)⁻¹ * endpointMap Q e i (originalSuzukiParameter Q e split i m μ hB c d) * n⁆ ∈
        rootAt Q split j (Q.simple i) := by
  apply (source_six_three Q split i j m μ hB ν T hC hm hij).1
  apply commutator_mem_commutator
  · simpa only [originalSuzukiParameter, originalRootLift_image] using
      (suzukiParameter Q split i m μ hB a b).property
  · exact conjugated_parameter_mem Q e split i j m μ hB n hn c d

include ν hC in
/-- The actual original Omega parameter centralizes the second source root,
including parameter zero; no perfectness is used. -/
theorem original_suzuki_omega_mixed_commute (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n =
      Q.simple j*Q.simple i) (b c d : BinaryGaloisField (2*m+1)) :
    Commute (endpointMap Q e i (originalSuzukiParameter Q e split i m μ hB 0 b))
      ((n : X ⧸ Q.D)⁻¹ * endpointMap Q e i (originalSuzukiParameter Q e split i m μ hB c d) * n) := by
  have hΩ : endpointMap Q e i (originalSuzukiParameter Q e split i m μ hB 0 b) ∈
      omegaOneAmbient (simpleRoot Q split i) := by
    rw [← suzukiOmegaParameter_range Q split i m μ hB]
    exact ⟨Multiplicative.ofAdd b, by simp only [originalSuzukiParameter, originalRootLift_image]; rfl⟩
  exact (mem_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp
      (source_six_three Q split i j m μ hB ν T hC hm hij).2 hΩ) _
        (conjugated_parameter_mem Q e split i j m μ hB n hn c d)).symm

include μ hB in
/-- (6.2) on the literal original linear endpoint coordinates and the
actual normalizer representative of s_i s_j. -/
theorem original_linear_mixed_bound (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n =
      Q.simple i*Q.simple j) (a b : Multiplicative F) :
    ⁅endpointMap Q e j (originalRootLift Q e split j ((linearRootEquiv Q split j ν T hC).symm a)),
      (n : X ⧸ Q.D)⁻¹ * endpointMap Q e j
        (originalRootLift Q e split j ((linearRootEquiv Q split j ν T hC).symm b)) * n⁆ ∈
      omegaOneAmbient (rootAt Q split i (Q.simple j)) := by
  simp only [originalRootLift_image]
  apply source_six_two Q split i j m μ hB ν T hC hm hij
  apply commutator_mem_commutator ((linearRootEquiv Q split j ν T hC).symm a).property
  rw [rootAt_eq Q split j _ n hn]
  change (n : X ⧸ Q.D)*((n : X ⧸ Q.D)⁻¹ *
    ((linearRootEquiv Q split j ν T hC).symm b : X ⧸ Q.D)*n)*(n : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using
    ((linearRootEquiv Q split j ν T hC).symm b).property

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i j : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL(2,F))
  (T : Sylow 2 PSL(2,F))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set PSL(2,F)))

def originalSuzukiGeneratedParameter (a b : BinaryGaloisField (2*m+1)) : generated L S :=
  ⟨originalSuzukiParameter Q (originalMarkedIso Q) split i m μ hB a b,
    parabolic_le_generated i (originalSuzukiParameter Q (originalMarkedIso Q) split i m μ hB a b).property⟩

theorem originalSuzukiGeneratedParameter_quotient (a b : BinaryGaloisField (2*m+1)) :
    Q.q (originalSuzukiGeneratedParameter Q split i m μ hB a b) =
      (suzukiParameter Q split i m μ hB a b : (generated L S) ⧸ Q.D) :=
  originalSuzukiParameter_quotient Q split i m μ hB a b

include ν hC in
/-- Literal Q.q form of (6.3), with any original representative of the
specified normalizer element and both original parameter representatives. -/
theorem original_six_three_quotient (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n =
      Q.simple j*Q.simple i)
    (z : generated L S) (hz : Q.q z = n)
    (a b c d : BinaryGaloisField (2*m+1)) :
    Q.q ⁅originalSuzukiGeneratedParameter Q split i m μ hB a b,
      z⁻¹ * originalSuzukiGeneratedParameter Q split i m μ hB c d * z⁆ ∈
        rootAt Q split j (Q.simple i) ∧
    Q.q ⁅originalSuzukiGeneratedParameter Q split i m μ hB 0 b,
      z⁻¹ * originalSuzukiGeneratedParameter Q split i m μ hB c d * z⁆ = 1 := by
  have hb := original_suzuki_mixed_bound Q (originalMarkedIso Q) split i j m μ hB ν T hC
    hm hij n hn a b c d
  have hc := (commutatorElement_eq_one_iff_commute).mpr
    (original_suzuki_omega_mixed_commute Q (originalMarkedIso Q) split i j m μ hB ν T hC
      hm hij n hn b c d)
  simp only [originalRootLift_image, originalSuzukiParameter] at hb hc
  simpa only [map_commutatorElement, map_mul, map_inv,
    originalSuzukiGeneratedParameter_quotient, hz] using And.intro hb hc

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
