module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.ModelAction.Equivariance

/-!
# The actual stabilizer of a standard second-axis tensor

Evaluation at a marked natural coordinate and the exact signed-orbit equality
recover both parameters of a pure signed tensor. Applying this criterion to
the collected-word formula forces the first loop parameter to be s^k pi^j,
the marked coordinate to be fixed, and epsilon_x(e) + P(e) + j to vanish.
Thus the stabilizer is computed inside the actual NPlus, without an assumed
orbit or stabilizer description.

Source: Aschbacher, *Sporadic Groups*, 29.7(2), printed p. 156 (PDF page 84).
Products are written in reversed order for left function composition.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction
open LocalC TrialitySpin SpinActions SignedModules
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction


private theorem bit_cases (s : ParkerBit) : s = 0 ∨ s = 1 := by revert s; decide

theorem delta2_eq_iff (b c : ParkerLoop) :
    delta2 b = delta2 c ↔ b = c ∨ b = parkerLoopMultiply c parkerOmega := by
  change secondAxisDomain.vector (axis2Equiv b) = secondAxisDomain.vector (axis2Equiv c) ↔ _
  erw [secondAxisDomain.vector_eq_iff]
  have hk : secondAxisDomain.pairing.flip (axis2Equiv c) =
      axis2Equiv (parkerLoopMultiply c parkerOmega) := Subtype.ext (k1_axis2 c)
  rw [hk]
  exact or_congr axis2Equiv.injective.eq_iff axis2Equiv.injective.eq_iff

theorem delta2_ne_zero (b : ParkerLoop) : delta2 b ≠ 0 := by
  intro h
  have hn := delta2_norm b
  rw [h, map_zero] at hn
  exact zero_ne_one hn

private def firstCoordinates : Natural.B1_24 ⊗[ℝ] B1A2 ≃ₗ[ℝ] (Fin 24 → B1A2) :=
  (TensorProduct.congr naturalLeechComparison (LinearEquiv.refl ℝ B1A2)).trans
    (tensorCoordinates B1A2)

private theorem firstCoordinates_tmul (x : Omega) (b : ParkerLoop) (i : Fin 24) :
    firstCoordinates (Natural.L 0 1 x ⊗ₜ[ℝ] delta2 b) i =
      ((Pi.single (coordinateMarking.symm x) (1 : ℝ) : NaturalSpace) i) • delta2 b := by
  simp only [firstCoordinates, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    naturalLeechComparison_L_one, LinearEquiv.refl_apply, tensorCoordinates_tmul]

theorem firstTensor_vector_eq_iff (x y : Omega) (b c : ParkerLoop) :
    Natural.L 0 1 x ⊗ₜ[ℝ] delta2 b = Natural.L 0 1 y ⊗ₜ[ℝ] delta2 c ↔
      x = y ∧ (b = c ∨ b = parkerLoopMultiply c parkerOmega) := by
  constructor
  · intro h
    have hh := congrArg (fun v => firstCoordinates v (coordinateMarking.symm x)) h
    rw [firstCoordinates_tmul, firstCoordinates_tmul] at hh
    have hxy : x = y := by
      by_contra hn
      have hi : coordinateMarking.symm x ≠ coordinateMarking.symm y :=
        fun hi => hn (coordinateMarking.symm.injective hi)
      simp only [Pi.single_eq_same, one_smul, Pi.single_eq_of_ne hi, zero_smul] at hh
      exact delta2_ne_zero b hh
    subst y
    simp only [Pi.single_eq_same, one_smul] at hh
    exact ⟨rfl,(delta2_eq_iff b c).mp hh⟩
  · rintro ⟨rfl,h⟩
    rw [(delta2_eq_iff b c).mpr h]

/-- The four central loop parameters `s^k π^j` of 29.7(2). -/
def centralParameter (k j : ParkerBit) : ParkerLoop :=
  parkerSign j (if k = 0 then loopOne else parkerOmega)

private theorem standard_sign_eq_one_or_omega (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (d : ParkerLoop) (s : ParkerBit) :
    (parkerSign s (α.val d) = loopOne ∨ parkerSign s (α.val d) = parkerOmega) ↔
    (parkerSign s d = loopOne ∨ parkerSign s d = parkerOmega) := by
  rw [← parkerStandard_preserves_sign]
  have ho : α.val loopOne = loopOne := α.prop.2.1 0
  conv_lhs => rw [← ho, ← hα, α.val.injective.eq_iff, α.val.injective.eq_iff]

private theorem sign_eq_central_iff (d : ParkerLoop) (s : ParkerBit) :
    (parkerSign s d = loopOne ∨ parkerSign s d = parkerOmega) ↔
      ∃ k, d = centralParameter k s := by
  constructor
  · rintro (h | h)
    · refine ⟨0,?_⟩
      have hh := congrArg (parkerSign s) h
      simpa [parkerSign, centralParameter, add_assoc] using hh
    · refine ⟨1,?_⟩
      have hh := congrArg (parkerSign s) h
      simpa [parkerSign, centralParameter, add_assoc] using hh
  · rintro ⟨k,rfl⟩
    rcases bit_cases k with rfl | rfl
    · left; simp [centralParameter, parkerSign, add_assoc]
    · right; simp [centralParameter, parkerSign, add_assoc]

private theorem central_overlap (k j : ParkerBit) (a : golay) :
    golayHalfOverlap (centralParameter k j).1 a = 0 := by
  rcases bit_cases k with rfl | rfl
  · exact golayHalfOverlap_zero_left a
  · exact golayHalfOverlap_one a

/-- Exact stabilizer test for every collected word. -/
theorem firstTensor_evenWord_fixes_iff (d e : ParkerLoop) (α : ParkerStandardGroup)
    (hα : α.val parkerOmega = parkerOmega) (x : Omega) :
    firstTensor (evenWord d e α hα) (Natural.L 0 1 x ⊗ₜ[ℝ] delta2 loopOne) =
      Natural.L 0 1 x ⊗ₜ[ℝ] delta2 loopOne ↔
    (parkerStandardProjection α).val x = x ∧
      ∃ k j, d = centralParameter k j ∧ e.1.val x + golayQuarterWeight e.1 + j = 0 := by
  rw [firstTensor_evenWord]
  simp only [loopOne, parkerLoopMultiply_one_right]
  rw [firstTensor_vector_eq_iff, parkerLoopMultiply_one_left]
  change _ ∧ (parkerSign _ (α.val d) = loopOne ∨ parkerSign _ (α.val d) = parkerOmega) ↔ _
  rw [standard_sign_eq_one_or_omega α hα, sign_eq_central_iff]
  constructor
  · rintro ⟨hx,k,hk⟩
    have hc : golayHalfOverlap d.1 e.1 = 0 := hk ▸ central_overlap k _ e.1
    rw [hc, add_zero] at hk
    refine ⟨hx,k,_,hk,?_⟩
    exact CharTwo.add_self_eq_zero _
  · rintro ⟨hx,k,j,rfl,hj⟩
    refine ⟨hx,k,?_⟩
    rw [central_overlap, add_zero]
    have hj' : e.1.val x + golayQuarterWeight e.1 = j := by
      have hh := congrArg (· + j) hj
      simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using hh
    rw [hj']

/-- Source 29.7(2), including both the coordinate condition and the sign equation.
The order is reversed because multiplication means left function composition. -/
theorem firstTensor_stabilizer (g : NPlus) (x : Omega) :
    firstTensor g (Natural.L 0 1 x ⊗ₜ[ℝ] delta2 loopOne) =
      Natural.L 0 1 x ⊗ₜ[ℝ] delta2 loopOne ↔
    ∃ (e : ParkerLoop) (α : ParkerStandardGroup) (hα : α.val parkerOmega = parkerOmega)
      (k j : ParkerBit), g = evenWord (centralParameter k j) e α hα ∧
        (parkerStandardProjection α).val x = x ∧
        e.1.val x + golayQuarterWeight e.1 + j = 0 := by
  constructor
  · intro h
    obtain ⟨d,e,α,hα,rfl⟩ := evenWord_surjective g
    obtain ⟨hx,k,j,hd,hj⟩ := (firstTensor_evenWord_fixes_iff d e α hα x).mp h
    subst d
    exact ⟨e,α,hα,k,j,rfl,hx,hj⟩
  · rintro ⟨e,α,hα,k,j,rfl,hx,hj⟩
    exact (firstTensor_evenWord_fixes_iff _ e α hα x).mpr ⟨hx,k,j,rfl,hj⟩



end Sporadic.Monster.Construction.NMonomial.ZeroAction.ModelAction
