module

public import Theory.SpecificGroups.Monster.Construction.LocalC.Pullback
public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceNormalizer.Orientation.QuarterTurnGeneration.CentralAction
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Orthogonal lifts of extraspecial quarter turns

For the actual extraspecial spin representation, an element whose square is
its central involution acts by an orthogonal complex structure J. The operator
(1 + J)/√2 has inverse (1 - J)/√2 and preserves the fixed spin form. Commutator
calculus shows that it implements the quarter turn fixing the centralizer of
its defining element. This constructs an element of the actual spin normalizer,
including both the intertwining and form-preservation laws.

These lifts supply the factors used by `SpinLift.lean` to lift every Leech
isometry into the spin–Leech pullback.

Source: Aschbacher, *Sporadic Groups*, Section 14, Exercise 4.4, p. 64,
and the spin normalizer construction in Section 27, pp. 147–148.
-/

public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Module
open scoped commutatorElement
namespace Sporadic.Monster.Construction.QuasithinObstruction
open LocalC TrialitySpin LocalC.SourceNormalizer

private theorem sqrtTwoNormalization :
    (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * (2 : ℝ) = 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith

private def normalizedRotation {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : End ℝ V) (hJ : J * J = -1) : V ≃ₗ[ℝ] V :=
  LinearEquiv.ofLinearMap ((Real.sqrt 2)⁻¹ • (1 + J))
    ((Real.sqrt 2)⁻¹ • (1 - J)) (by
      change ((Real.sqrt 2)⁻¹ • (1 + J)) * ((Real.sqrt 2)⁻¹ • (1 - J)) = 1
      have h : (1 + J) * (1 - J) = (2 : ℝ) • (1 : End ℝ V) := by
        noncomm_ring [hJ]
        module
      rw [smul_mul_assoc, mul_smul_comm, h, smul_smul, smul_smul,
        sqrtTwoNormalization, one_smul]) (by
      change ((Real.sqrt 2)⁻¹ • (1 - J)) * ((Real.sqrt 2)⁻¹ • (1 + J)) = 1
      have h : (1 - J) * (1 + J) = (2 : ℝ) • (1 : End ℝ V) := by
        noncomm_ring [hJ]
        module
      rw [smul_mul_assoc, mul_smul_comm, h, smul_smul, smul_smul,
        sqrtTwoNormalization, one_smul])

private theorem normalizedRotation_form {V : Type*} [AddCommGroup V] [Module ℝ V]
    (J : End ℝ V) (hJ : J * J = -1) (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ v w, B (J v) (J w) = B v w) (v w : V) :
    B (normalizedRotation J hJ v) (normalizedRotation J hJ w) = B v w := by
  have hJJ (u : V) : J (J u) = -u := LinearMap.congr_fun hJ u
  have hcross : B (J v) w = - B v (J w) := by
    have h := hB v (J w)
    rw [hJJ, map_neg] at h
    linarith
  change B ((Real.sqrt 2)⁻¹ • (v + J v)) ((Real.sqrt 2)⁻¹ • (w + J w)) = _
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, map_add,
    LinearMap.add_apply, hB, hcross]
  have hs := sqrtTwoNormalization
  calc
    _ = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * 2) * B v w := by ring
    _ = B v w := by rw [hs, one_mul]

private theorem representation_anticommute {K V : Type*} [Group K]
    [AddCommGroup V] [Module ℝ V] (ρ : Representation ℝ K V) (q x z : K)
    (hz : ρ z = -1) (h : q * x = z * (x * q)) : ρ q * ρ x = -(ρ x * ρ q) := by
  rw [← map_mul, h, map_mul, hz, map_mul, neg_mul, one_mul]

private theorem one_add_intertwines {R : Type*} [Ring R] (J A : R)
    (hJ : J * J = -1) (hA : J * A = -(A * J)) :
    (1 + J) * A = (J * A) * (1 + J) := by
  have htriple : J * A * J = A := by rw [hA, neg_mul, mul_assoc, hJ]; simp
  rw [add_mul, one_mul, mul_add, mul_one, htriple, add_comm]

private theorem image_anticommute (q x : Q1Image) (h : ¬ Commute q x) :
    SpinAction.imageRepresentation q * SpinAction.imageRepresentation x =
      -(SpinAction.imageRepresentation x * SpinAction.imageRepresentation q) := by
  have hp : q1CentralQuadraticForm.polarBilin (centralVector q) (centralVector x) = 1 := by
    have hn := mt (commute_iff_polar_zero q x).mpr h
    generalize q1CentralQuadraticForm.polarBilin (centralVector q) (centralVector x) = b at *
    fin_cases b
    · exact (hn rfl).elim
    · rfl
  have hc : ⁅q, x⁆ = q1ImageCenterGenerator := by
    rw [commutator_polar, hp]
    simp [ZMod.val_one_eq_one_mod]
  have he : q * x = q1ImageCenterGenerator * (x * q) := by
    rw [← hc, commutatorElement_def]
    group
  exact representation_anticommute SpinAction.imageRepresentation q x
    q1ImageCenterGenerator SpinAction.imageRepresentation_center he

private theorem quarterTurn_intertwines (q : Q1Image)
    (hq : q ^ 2 = q1ImageCenterGenerator) (x : Q1Image) :
    (1 + SpinAction.imageRepresentation q) * SpinAction.imageRepresentation x =
      SpinAction.imageRepresentation (quarterTurn q hq x) *
        (1 + SpinAction.imageRepresentation q) := by
  have hJ : SpinAction.imageRepresentation q * SpinAction.imageRepresentation q = -1 := by
    rw [← map_mul, ← pow_two, hq, SpinAction.imageRepresentation_center]
  by_cases hc : Commute q x
  · rw [(quarterTurn_spec q hq x).1 hc]
    have hm := (hc.map SpinAction.imageRepresentation).eq
    simp only [add_mul, mul_add, one_mul, mul_one, hm]
  · rw [(quarterTurn_spec q hq x).2 hc, map_mul]
    exact one_add_intertwines (R := End ℝ SpinSpace)
      (SpinAction.imageRepresentation q) (SpinAction.imageRepresentation x)
      hJ (image_anticommute q x hc)

/-- The orthogonal quarter turn implementing the actual extraspecial automorphism. -/
def quarterTurnSpin (q : Q1Image) (hq : q ^ 2 = q1ImageCenterGenerator) : spinNormalizer := by
  have hJ : SpinAction.imageRepresentation q * SpinAction.imageRepresentation q = -1 := by
    rw [← map_mul, ← pow_two, hq, SpinAction.imageRepresentation_center]
  refine ⟨(normalizedRotation (SpinAction.imageRepresentation q) hJ, quarterTurn q hq), ?_, ?_⟩
  · intro x v
    change ((Real.sqrt 2)⁻¹ • (1 + SpinAction.imageRepresentation q))
        (SpinAction.imageRepresentation x v) =
      SpinAction.imageRepresentation (quarterTurn q hq x)
        (((Real.sqrt 2)⁻¹ • (1 + SpinAction.imageRepresentation q)) v)
    have h := congrArg ((Real.sqrt 2)⁻¹ • ·) (quarterTurn_intertwines q hq x)
    rw [← smul_mul_assoc, ← mul_smul_comm] at h
    exact LinearMap.congr_fun h v
  · exact normalizedRotation_form _ hJ _ (SpinAction.imageRepresentation_isometry q)

@[simp] theorem quarterTurnSpin_automorphism (q : Q1Image)
    (hq : q ^ 2 = q1ImageCenterGenerator) :
    (quarterTurnSpin q hq).val.2 = quarterTurn q hq := by rfl

@[simp] theorem quarterTurnSpin_apply (q : Q1Image)
    (hq : q ^ 2 = q1ImageCenterGenerator) (v : SpinSpace) :
    (quarterTurnSpin q hq).val.1 v =
      (Real.sqrt 2)⁻¹ • (v + SpinAction.imageRepresentation q v) := by rfl

end Sporadic.Monster.Construction.QuasithinObstruction
