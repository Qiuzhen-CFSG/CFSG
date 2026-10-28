module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.Basic
public import Theory.GroupAction.NoncentralTwoChiefLength.Native
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations.SectionModels
public import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# The subgroup intervals for the final 13.8.33 comparison

The two local filtrations use the literal subgroups `UH`, `UL`, `CQUL`,
`HC`, and `QH`. The cubic fixed-point index is an invariant of an actual
conjugation action. Its logarithm is monotone in the subgroup being acted
on, and differences telescope along the two source filtrations. The
subquotient comparison does not require `UL` to be normal in `HC`.

The final conditional comparison uses actual marked quotient maps. Restricting
the two parabolic maps to the common two-core constructs its top sections;
the checked natural actions give the other contributions. Thus the same
intrinsic cubic invariant is both `4 + k` and `5 + j`, while `k ≤ j`.
This proves the contradiction without assuming numerical chief-factor totals.
The parent retains the source theorem and supplies the abelian-span and
compatible module identifications from the preceding argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed pp.967–968.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33

variable {G : Type*} [Group G]

/-- The endpoint chain used by the actual quotient maps in the comparison. -/
theorem actual_CQUL_interval_chain (Q L H V₃ : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)]
    (hULQ : Source.UL L H V₃ ≤ Q) (hQH : Q ≤ H) :
    Source.UH H V₃ ≤ Source.UL L H V₃ ∧
      Source.UL L H V₃ ≤ CQUL Q L H V₃ ∧
      CQUL Q L H V₃ ≤ Source.HC H V₃ := by
  exact ⟨le_conjugateSpanBy _ _, abelian_UL_le_centralizer Q L H V₃ hULQ,
    centralizer_le_HC Q L H V₃ hQH⟩

/-- In the A₆ case the common local two-group is `O₂(L₁T)`; see
Notation 13.2.1. The join is the actual generated subgroup of the ambient group. -/
def filtrationTop (L₁ T : Subgroup G) : Subgroup G := (L₁ ⊔ T).pCoreIn 2

/-- The coarse filtration through the L-side centralizer. -/
def leftFiltration (Q L H V₃ V L₁ T : Subgroup G) : Fin 6 → Subgroup G :=
  ![⊥, V, Source.UL L H V₃, CQUL Q L H V₃, Q, filtrationTop L₁ T]

/-- The coarse filtration through the H-side centralizer. -/
def rightFiltration (H V₃ L₁ T : Subgroup G) : Fin 5 → Subgroup G :=
  ![⊥, Source.UH H V₃, Source.HC H V₃, Source.QH H, filtrationTop L₁ T]

theorem leftFiltration_monotone (Q L H V₃ V L₁ T : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)]
    (hV : V ≤ Source.UL L H V₃) (hULQ : Source.UL L H V₃ ≤ Q)
    (hQR : Q ≤ filtrationTop L₁ T) : Monotone (leftFiltration Q L H V₃ V L₁ T) := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  fin_cases i
  · exact bot_le
  · exact hV
  · exact abelian_UL_le_centralizer Q L H V₃ hULQ
  · exact inf_le_left
  · exact hQR

theorem rightFiltration_monotone (Q L H V₃ L₁ T : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)]
    (hULQ : Source.UL L H V₃ ≤ Q) (hQH : Q ≤ H)
    (hHC : Source.HC H V₃ ≤ Source.QH H)
    (hQHR : Source.QH H ≤ filtrationTop L₁ T) :
    Monotone (rightFiltration H V₃ L₁ T) := by
  obtain ⟨h₁, h₂, h₃⟩ := actual_CQUL_interval_chain Q L H V₃ hULQ hQH
  rw [Fin.monotone_iff_le_succ]
  intro i
  fin_cases i
  · exact bot_le
  · exact h₁.trans (h₂.trans h₃)
  · exact hHC
  · exact hQHR

/-- The unknown contribution of the literal section `CQUL/UL`. -/
noncomputable def filtrationK (A Q L H V₃ : Subgroup G) : ℕ :=
  sectionCubicLength A (Source.UL L H V₃) (CQUL Q L H V₃)

/-- The unknown contribution of the literal section `HC/UH`. -/
noncomputable def filtrationJ (A H V₃ : Subgroup G) : ℕ :=
  sectionCubicLength A (Source.UH H V₃) (Source.HC H V₃)

/-- The invariant is evaluated on the same actual group on both sides. -/
noncomputable def filtrationN (A L₁ T : Subgroup G) : ℕ :=
  conjugationCubicLength A (filtrationTop L₁ T)

/-- Subquotient comparison uses containment, without asserting `UL ◁ HC`. -/
theorem filtrationK_le_filtrationJ [Finite G] (A Q L H V₃ : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)]
    (hULQ : Source.UL L H V₃ ≤ Q) (hQH : Q ≤ H) :
    filtrationK A Q L H V₃ ≤ filtrationJ A H V₃ := by
  obtain ⟨h₁, _, h₃⟩ := actual_CQUL_interval_chain Q L H V₃ hULQ hQH
  exact sectionCubicLength_mono A h₁ h₃

/-- The K contribution is the invariant of `CQUL/UL` with its actual
quotient conjugation action. Its relative normality follows from abelianness. -/
theorem filtrationK_eq_quotient [Finite G] (A Q L H V₃ : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)]
    (hA : IsPGroup 3 A) (hQ : IsPGroup 2 Q)
    (hULQ : Source.UL L H V₃ ≤ Q)
    (hAC : A ≤ normalizer (CQUL Q L H V₃ : Set G))
    (hAU : A ≤ normalizer (Source.UL L H V₃ : Set G)) :
    letI := UL_normal_in_CQUL Q L H V₃ hULQ
    letI := quotientConjugationAction A (CQUL Q L H V₃) (Source.UL L H V₃) hAC hAU
    filtrationK A Q L H V₃ = FixedPoints.cubicLength A
      (CQUL Q L H V₃ ⧸ (Source.UL L H V₃).subgroupOf (CQUL Q L H V₃)) := by
  let := UL_normal_in_CQUL Q L H V₃ hULQ
  exact sectionCubicLength_eq_quotient_of_twoGroup A _ _ hA
    (hQ.to_le (show CQUL Q L H V₃ ≤ Q from inf_le_left))
    (abelian_UL_le_centralizer Q L H V₃ hULQ) hAC hAU

/-- The J contribution is the invariant of `HC/UH`. This does not assert
normality of the larger subgroup `UL` in `HC`. -/
theorem filtrationJ_eq_quotient [Finite G] (A Q L H V₃ : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)]
    (hA : IsPGroup 3 A) (hULQ : Source.UL L H V₃ ≤ Q) (hQH : Q ≤ H)
    (hHC : Source.HC H V₃ ≤ Source.QH H)
    (hAC : A ≤ normalizer (Source.HC H V₃ : Set G))
    (hAU : A ≤ normalizer (Source.UH H V₃ : Set G)) :
    ∃ hN : ((Source.UH H V₃).subgroupOf (Source.HC H V₃)).Normal,
      letI := hN
      letI := quotientConjugationAction A (Source.HC H V₃) (Source.UH H V₃) hAC hAU
      filtrationJ A H V₃ = FixedPoints.cubicLength A
        (Source.HC H V₃ ⧸ (Source.UH H V₃).subgroupOf (Source.HC H V₃)) := by
  obtain ⟨h₁, h₂, h₃⟩ := actual_CQUL_interval_chain Q L H V₃ hULQ hQH
  let : IsMulCommutative (Source.UH H V₃) :=
    .of_setLike_mul_comm (fun _ ha _ hb => setLike_mul_comm (h₁ ha) (h₁ hb))
  let hN := UH_normal_in_HC H V₃ (h₁.trans (hULQ.trans hQH))
  refine ⟨hN, ?_⟩
  let := hN
  exact sectionCubicLength_eq_quotient_of_twoGroup A _ _ hA
    ((isPGroup_pCoreIn 2 H).to_le hHC) (h₁.trans (h₂.trans h₃)) hAC hAU

/-- Telescoping the actual L-side subgroup chain. Each difference is the
length of its quotient action under the hypotheses of
`Subgroup.sectionCubicLength_eq_quotient`. -/
theorem leftFiltration_total [Finite G] (A Q L H V₃ V L₁ T : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)]
    (hV : V ≤ Source.UL L H V₃) (hULQ : Source.UL L H V₃ ≤ Q)
    (hQR : Q ≤ filtrationTop L₁ T) :
    filtrationN A L₁ T = conjugationCubicLength A V +
      sectionCubicLength A V (Source.UL L H V₃) + filtrationK A Q L H V₃ +
      sectionCubicLength A (CQUL Q L H V₃) Q +
      sectionCubicLength A Q (filtrationTop L₁ T) := by
  have h₁ := conjugationCubicLength_mono A hV
  have h₂ := conjugationCubicLength_mono A
    (abelian_UL_le_centralizer Q L H V₃ hULQ)
  have h₃ := conjugationCubicLength_mono A
    (show CQUL Q L H V₃ ≤ Q from inf_le_left)
  have h₄ := conjugationCubicLength_mono A hQR
  unfold filtrationN filtrationK sectionCubicLength
  omega

/-- Telescoping the actual H-side subgroup chain. -/
theorem rightFiltration_total [Finite G] (A Q L H V₃ L₁ T : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)]
    (hULQ : Source.UL L H V₃ ≤ Q) (hQH : Q ≤ H)
    (hHC : Source.HC H V₃ ≤ Source.QH H)
    (hQHR : Source.QH H ≤ filtrationTop L₁ T) :
    filtrationN A L₁ T = conjugationCubicLength A (Source.UH H V₃) +
      filtrationJ A H V₃ + sectionCubicLength A (Source.HC H V₃) (Source.QH H) +
      sectionCubicLength A (Source.QH H) (filtrationTop L₁ T) := by
  obtain ⟨h₁, h₂, h₃⟩ := actual_CQUL_interval_chain Q L H V₃ hULQ hQH
  have h₄ := conjugationCubicLength_mono A (h₁.trans (h₂.trans h₃))
  have h₅ := conjugationCubicLength_mono A hHC
  have h₆ := conjugationCubicLength_mono A hQHR
  unfold filtrationN filtrationJ sectionCubicLength
  omega

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33

namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33
open Subgroup ChiefModels
variable {G : Type*} [Group G] [Finite G]

/-- The two numerical identities are consequences of the actual compatible
quotient maps and the checked marked actions. No counting identity is an input. -/
theorem filtration_totals_of_models (A Q L H V₃ V V₁ L₁ T : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)]
    (f : A →* cubicActor) (hf : Function.Surjective f) (hA : IsPGroup 3 A) (hQ : IsPGroup 2 Q)
    (d : FiltrationModels A Q L H V₃ V V₁ (L₁ ⊔ T) f)
    (hULQ : Source.UL L H V₃ ≤ Q) (hQH : Q ≤ H)
    (hV₁ : V₁ ≤ centralizer (A : Set G)) :
    filtrationN A L₁ T = 4 + filtrationK A Q L H V₃ ∧
      filtrationN A L₁ T = 5 + filtrationJ A H V₃ := by
  have hR := isPGroup_pCoreIn 2 (L₁ ⊔ T)
  let leftCore := d.leftQuotient.coreSection hQ duadCubicActor_normalizes_parabolic_core
  let rightCore := d.rightQuotient.coreSection (isPGroup_pCoreIn 2 H)
    cubicActor_normalizes_parabolic_core
  have hVUL : V ≤ Source.UL L H V₃ := by
    let := Representation.BinaryFixedPoints.action d.spanShape.opposite
    exact d.span.le
  have hHC : Source.HC H V₃ ≤ Source.QH H := by
    let := Representation.BinaryFixedPoints.action d.duality.shape.standard.dual
    exact d.duality.dual.le
  have hQR : Q ≤ filtrationTop L₁ T := by
    let := conjMulDistribMulActionOfLeNormalizer duadCubicActor
      (Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1.pCoreIn 2)
      duadCubicActor_normalizes_parabolic_core
    exact leftCore.le
  have hQHR : Source.QH H ≤ filtrationTop L₁ T := by
    let := conjMulDistribMulActionOfLeNormalizer cubicActor
      (Theory.SpecificGroups.SymmetricSix.BinaryFlags.H2.pCoreIn 2)
      cubicActor_normalizes_parabolic_core
    exact rightCore.le
  have hUL : IsPGroup 2 (Source.UL L H V₃) := hQ.to_le hULQ
  have hUH : IsPGroup 2 (Source.UH H V₃) := hUL.to_le (le_conjugateSpanBy _ _)
  have hv := opposite_section_length .natural d.v hA (hUL.to_le hVUL) hf
  have hul := opposite_section_length d.spanShape d.span hA hUL hf
  have hc := opposite_section_length d.centralizerShape d.centralizer hA hQ hf
  have hl := duad_core_section_length leftCore hA hR hf
  have hu := standard_section_length d.uhShape d.uh hA hUH hf
  have hd := (d.duality.lengths hA hUH hf).2
  have hr := syntheme_core_section_length rightCore hA hR hf
  have hz : conjugationCubicLength A V₁ = 0 := by
    rw [conjugationCubicLength, relIndex_eq_one.mpr hV₁]
    rfl
  simp only [sectionCubicLength, conjugationCubicLength_bot, Nat.sub_zero] at hv
  rw [sectionCubicLength, hz, Nat.sub_zero] at hu
  have hleft := leftFiltration_total A Q L H V₃ V L₁ T
    hVUL hULQ hQR
  have hright := rightFiltration_total A Q L H V₃ L₁ T
    hULQ hQH hHC hQHR
  change sectionCubicLength A Q (filtrationTop L₁ T) = 1 at hl
  change sectionCubicLength A (Source.QH H) (filtrationTop L₁ T) = 1 at hr
  rw [hv, hul, hc, hl] at hleft
  rw [hu, hd, hr] at hright
  constructor <;> omega

/-- The final conditional contradiction of 13.8.33 (printed p.968).
The parent still supplies the abelian-span and compatible module identifications. -/
theorem filtration_contradiction (A Q L H V₃ V V₁ L₁ T : Subgroup G)
    [IsMulCommutative (Source.UL L H V₃)]
    (f : A →* cubicActor) (hf : Function.Surjective f) (hA : IsPGroup 3 A) (hQ : IsPGroup 2 Q)
    (d : FiltrationModels A Q L H V₃ V V₁ (L₁ ⊔ T) f)
    (hULQ : Source.UL L H V₃ ≤ Q) (hQH : Q ≤ H)
    (hV₁ : V₁ ≤ centralizer (A : Set G)) : False := by
  obtain ⟨hl, hr⟩ := filtration_totals_of_models A Q L H V₃ V V₁ L₁ T
    f hf hA hQ d hULQ hQH hV₁
  have hkj := filtrationK_le_filtrationJ A Q L H V₃ hULQ hQH
  omega

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33
