module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.Reduction
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.G2Marked.Separation
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.CoverFusion.G2Marked.FieldCalculation
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.FieldDegree

/-!
# The marked G₂(4) quotient calculation

The concrete coefficient calculation constructs a highest-root involution
in O² of the full fixed subgroup and an element giving the fusion equation.
Actual conjugacy of automorphisms transports the residual, the two-central
mark, and the equation simultaneously. The order calculation independently
excludes every large-center quotient from 16.1.2(2).

For an arbitrary outer involution, the last theorem reduces the remaining
work to inner-field automorphism coverage and solving the resulting G₂
cocycle. Both are explicit inputs here: no arbitrary-outer fusion theorem
or completed 16.1.4 is claimed. Full fixed G₂(2) and its proper two-residual
are never identified with one another. The coefficient fixed-group descent
equivalence is not needed for this marked calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(4), printed p.1171, and the proof of 16.4.9(2), pp.1190–1191.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion.G2Marked
open Atlas.G2 Atlas.G2.LieAutomorphismExtensions Atlas.G2.EvenFieldFixedResidual
open CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
/-- Transport the complete marked witness through the actual conjugating element. -/
theorem fusion_of_conjugate (b : MulAut (Model F)) (σ : F ≃+* F) (c : Model F)
    (hb : b = MulAut.conj c * fieldAction σ * (MulAut.conj c)⁻¹)
    (hf : TwoCentralResidualFusion (fieldAction σ)) : TwoCentralResidualFusion b := by
  apply TwoCentralResidualFusion.of_equiv (MulAut.conj c).symm b
  have he : MulAut.congr (MulAut.conj c).symm b = fieldAction σ := by
    apply MulEquiv.ext
    intro x
    change c⁻¹ * b (c * x * c⁻¹) * c = fieldAction σ x
    rw [hb]
    change c⁻¹ * (c * fieldAction σ (c⁻¹ * (c * x * c⁻¹) * c) * c⁻¹) * c = _
    simp only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one]
  rwa [he]

/-- Coverage and cocycle descent give the precise field-involution normal form.
These two earlier model results remain explicit premises. -/
theorem field_normal_form_of_coverage_of_cocycle (hF : Nat.card F = 4)
    (hcoverage : Function.Surjective (semilinearAction (F := F)))
    (hcocycle : ∀ (σ : F ≃+* F), orderOf σ = 2 → ∀ g : Model F,
      g * fieldAction σ g = 1 → ∃ c : Model F, g = c * fieldAction σ c⁻¹)
    (b : MulAut (Model F)) (hb : orderOf b = 2)
    (hout : ¬ ∃ g : Model F, b = MulAut.conj g) :
    ∃ (σ : F ≃+* F) (c : Model F), σ ≠ 1 ∧
      b = MulAut.conj c * fieldAction σ * (MulAut.conj c)⁻¹ := by
  obtain ⟨z, hz⟩ := hcoverage b
  have he : b = MulAut.conj z.left * fieldAction z.right := hz.symm
  have hbpow : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  obtain ⟨hs, hg⟩ := coefficient_involution_and_cocycle (by omega : 2 < Nat.card F)
    b hbpow z.left z.right he (fun g hg => hout ⟨g,hg⟩)
  obtain ⟨c, hc⟩ := hcocycle z.right hs z.left hg
  refine ⟨z.right, c, ?_, ?_⟩
  · intro h
    simp [h] at hs
  · rw [he, hc]
    apply MulEquiv.ext
    intro x
    change (c * fieldAction z.right c⁻¹) * fieldAction z.right x *
      (c * fieldAction z.right c⁻¹)⁻¹ =
      c * fieldAction z.right (c⁻¹ * x * c) * c⁻¹
    simp only [map_mul, map_inv]
    group

/-- Marked fusion for a conjugate of a nontrivial coefficient automorphism. -/
theorem twoCentralResidualFusion_of_field_conjugate
    (hF : Nat.card F = 4) (b : MulAut (Model F)) (σ : F ≃+* F)
    (hσ : σ ≠ 1) (c : Model F)
    (hb : b = MulAut.conj c * fieldAction σ * (MulAut.conj c)⁻¹) :
    TwoCentralResidualFusion b :=
  fusion_of_conjugate b σ c hb (field_twoCentralResidualFusion hF σ hσ)

omit [CharP F 2] in
/-- Conditional assembly for every outer involution of the actual G₂(4).
The two missing inputs are automorphism coverage and the genuine octonion
cocycle theorem, not an assumption of marked fusion. -/
theorem twoCentralResidualFusion_of_coverage_of_cocycle
    (hF : Nat.card F = 4)
    (hcoverage : Function.Surjective (semilinearAction (F := F)))
    (hcocycle : ∀ (σ : F ≃+* F), orderOf σ = 2 → ∀ g : Model F,
      g * fieldAction σ g = 1 → ∃ c : Model F, g = c * fieldAction σ c⁻¹)
    (b : MulAut (Model F)) (hb : orderOf b = 2)
    (hout : ¬ ∃ g : Model F, b = MulAut.conj g) :
    TwoCentralResidualFusion b := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (show Fintype.card F = 2 ^ 2 by simpa [Nat.card_eq_fintype_card] using hF)
  obtain ⟨σ, c, hσ, he⟩ :=
    field_normal_form_of_coverage_of_cocycle hF hcoverage hcocycle b hb hout
  exact twoCentralResidualFusion_of_field_conjugate hF b σ hσ c he

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.CoverFusion.G2Marked
