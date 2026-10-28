module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.SpinActions.Actions

/-!
# Source generator effects and compatibility with ambient restrictions

The signed-vector formulas determine the whole linear maps. In particular,
`psi1(s)` fixes the first module and negates the third, whereas `psi1(sπ)`
has the reverse effect. The two `psi2` generators listed in both source
kernels act trivially. Covariance of signed delta functions identifies the
constructed maps with the actual normalized ambient restrictions.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.3, pp. 146–147.
The effects of the generators in (5)–(6) are proved here; identifying the
entire subgroup kernels is a separate structural assertion. Ambient
hypotheses below specify only invariance and commutation of actual
permutations, together with the ambient element being restricted.
-/

@[expose] public section
open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin.SpinActions
open SignedModules

/-- The sign attached to the central element changes between the two orbit modules. -/
theorem delta2_signOmega (b : ParkerLoop) :
    delta2 (parkerLoopMultiply b (parkerSign 1 parkerOmega)) = -delta2 b := by
  rw [parkerLoopMultiply_sign_right, delta2_sign, delta2_omega]

theorem B3Axis2.delta_omega (b : ParkerLoop) :
    B3Axis2.delta (parkerLoopMultiply b parkerOmega) = -B3Axis2.delta b := by
  have h := B3Axis2.delta_signOmega b
  rw [parkerLoopMultiply_sign_right, B3Axis2.delta_sign] at h
  exact (neg_eq_iff_eq_neg).1 h

def realSign (s : ParkerBit) : ℝ := if s = 0 then 1 else -1

theorem delta2_sign_scalar (s : ParkerBit) (b : ParkerLoop) :
    delta2 (parkerSign s b) = realSign s • delta2 b := by
  have hb : ∀ t : ParkerBit, t = 0 ∨ t = 1 := by decide
  rcases hb s with rfl | rfl
  · simp [realSign]
  · rw [delta2_sign]
    change -delta2 b = (-(1 : ℝ)) • delta2 b
    exact (neg_one_smul ℝ (delta2 b)).symm

/-- The diagonal square/commutator sign in 27.3(2), as a real scalar. -/
theorem psi2B1_sign_scalar (d b : ParkerLoop) : psi2B1 d (delta2 b) =
    realSign (golayQuarterWeight d.1 + golayHalfOverlap b.1 d.1) • delta2 b := by
  rw [psi2B1_delta, delta2_sign_scalar]

private theorem b1_ext (f g : B1A2 →ₗ[ℝ] B1A2)
    (h : ∀ b, f (delta2 b) = g (delta2 b)) : f = g := by
  apply firstSecond.geometry.vector_ext
  intro a
  obtain ⟨b, rfl⟩ := axis2Equiv.surjective a
  exact h b

private theorem b3_ext (f g : B3A2 →ₗ[ℝ] B3A2)
    (h : ∀ b, f (B3Axis2.delta b) = g (B3Axis2.delta b)) : f = g := by
  apply thirdSecond.geometry.vector_ext
  intro a
  obtain ⟨b, rfl⟩ := axis2Equiv.surjective a
  exact h b

/-- The first generator listed in 27.3(5) is trivial on `B1(A2)`. -/
theorem psi1B1_omega : psi1B1 parkerOmega = LinearEquiv.refl ℝ B1A2 := by
  apply LinearEquiv.toLinearMap_injective
  apply b1_ext
  intro b
  change psi1B1 parkerOmega (delta2 b) = delta2 b
  rw [psi1B1_delta, parkerOmega_commutes, delta2_omega]

/-- The first generator listed in 27.3(6) is trivial on `B3(A2)`. -/
theorem psi1B3_signOmega : psi1B3 (parkerSign 1 parkerOmega) = LinearEquiv.refl ℝ B3A2 := by
  apply LinearEquiv.toLinearMap_injective
  apply b3_ext
  intro b
  change psi1B3 (parkerSign 1 parkerOmega) (B3Axis2.delta b) = B3Axis2.delta b
  rw [psi1B3_delta, signOmega_commutes, B3Axis2.delta_signOmega]

/-- The two central generators in (5) and (6) cannot be interchanged. -/
theorem psi1B1_signOmega (v : B1A2) : psi1B1 (parkerSign 1 parkerOmega) v = -v := by
  have h : (psi1B1 (parkerSign 1 parkerOmega)).toLinearMap = -LinearMap.id := by
    apply b1_ext
    intro b
    change psi1B1 (parkerSign 1 parkerOmega) (delta2 b) = -delta2 b
    rw [psi1B1_delta, signOmega_commutes, delta2_signOmega]
  exact LinearMap.congr_fun h v

theorem psi1B3_omega (v : B3A2) : psi1B3 parkerOmega v = -v := by
  have h : (psi1B3 parkerOmega).toLinearMap = -LinearMap.id := by
    apply b3_ext
    intro b
    change psi1B3 parkerOmega (B3Axis2.delta b) = -B3Axis2.delta b
    rw [psi1B3_delta, parkerOmega_commutes, B3Axis2.delta_omega]
  exact LinearMap.congr_fun h v

private theorem sandwich_pi (X : Type*) (U : AxisRealization X) (b : ParkerLoop) :
    U.sandwichAction loopPi (U.geometry.vector (U.param b)) = U.geometry.vector (U.param b) := by
  simp only [AxisRealization.sandwichAction, LinearEquiv.trans_apply,
    AxisRealization.leftAction_vector, AxisRealization.rightAction_vector,
    loopInverse_pi, loopPi_mul, mul_loopPi, parkerSign_add]
  rw [show (1 + 1 : ParkerBit) = 0 from rfl, parkerSign_zero]

private theorem sandwich_omega (X : Type*) (U : AxisRealization X) (b : ParkerLoop) :
    U.sandwichAction parkerOmega (U.geometry.vector (U.param b)) = U.geometry.vector (U.param b) := by
  simp only [AxisRealization.sandwichAction, LinearEquiv.trans_apply,
    AxisRealization.leftAction_vector, AxisRealization.rightAction_vector, loopInverse_omega]
  rw [parkerOmega_commutes]
  have h : parkerLoopMultiply (parkerLoopMultiply b parkerOmega) parkerOmega = b := by
    simpa only [loopInverse_omega] using loopInverse_mul_right parkerOmega b
  rw [h]

theorem psi2B1_pi : psi2B1 loopPi = LinearEquiv.refl ℝ B1A2 := by
  apply LinearEquiv.toLinearMap_injective
  exact b1_ext _ _ (sandwich_pi A2 firstSecond)

theorem psi2B1_omega : psi2B1 parkerOmega = LinearEquiv.refl ℝ B1A2 := by
  apply LinearEquiv.toLinearMap_injective
  exact b1_ext _ _ (sandwich_omega A2 firstSecond)

theorem psi2B3_pi : psi2B3 loopPi = LinearEquiv.refl ℝ B3A2 := by
  apply LinearEquiv.toLinearMap_injective
  exact b3_ext _ _ (sandwich_pi A2 thirdSecond)

theorem psi2B3_omega : psi2B3 parkerOmega = LinearEquiv.refl ℝ B3A2 := by
  apply LinearEquiv.toLinearMap_injective
  exact b3_ext _ _ (sandwich_omega A2 thirdSecond)

/-- All three concrete effects needed for the kernel generators in 27.3(5). -/
theorem kernel_generators_B1 :
    psi1B1 parkerOmega = LinearEquiv.refl ℝ B1A2 ∧
    psi2B1 loopPi = LinearEquiv.refl ℝ B1A2 ∧
    psi2B1 parkerOmega = LinearEquiv.refl ℝ B1A2 :=
  ⟨psi1B1_omega, psi2B1_pi, psi2B1_omega⟩

/-- All three concrete effects needed for the kernel generators in 27.3(6).
Identifying the entire group kernel still requires the ambient group structure. -/
theorem kernel_generators_B3 :
    psi1B3 (parkerSign 1 parkerOmega) = LinearEquiv.refl ℝ B3A2 ∧
    psi2B3 loopPi = LinearEquiv.refl ℝ B3A2 ∧
    psi2B3 parkerOmega = LinearEquiv.refl ℝ B3A2 :=
  ⟨psi1B3_signOmega, psi2B3_pi, psi2B3_omega⟩

/-- Geometric covariance for any ambient action satisfying the stated normalization. -/
theorem induced_delta2 {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
    (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2)
    (hk : ∀ g a, ρ g (k1.val a) = k1.val (ρ g a))
    (hz : ∀ g a, ρ g (z1 a) = z1 (ρ g a)) (g : G) (b c : ParkerLoop)
    (hg : ρ g (axis2 b) = axis2 c) :
    secondAxisDomain.inducedRepresentation ρ hA hk hz g (delta2 b) = delta2 c := by
  calc
    _ = secondAxisDomain.vector
        (secondAxisDomain.restrictPermutations ρ hA g (axis2Equiv b)) :=
      secondAxisDomain.representation_vector _ _ _ g _
    _ = delta2 c := congrArg secondAxisDomain.vector (Subtype.ext hg)

/-- The constructed `psi1B1` is the actual restricted ambient generator. -/
theorem induced_psi1B1 {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
    (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2)
    (hk : ∀ g a, ρ g (k1.val a) = k1.val (ρ g a))
    (hz : ∀ g a, ρ g (z1 a) = z1 (ρ g a)) (g : G) (d : ParkerLoop)
    (hg : ρ g = psi1 d) :
    secondAxisDomain.inducedRepresentation ρ hA hk hz g = (psi1B1 d).toLinearMap := by
  apply b1_ext
  intro b
  change secondAxisDomain.inducedRepresentation ρ hA hk hz g (delta2 b) = psi1B1 d (delta2 b)
  rw [psi1B1_delta]
  exact induced_delta2 ρ hA hk hz g b _ (by rw [hg, psi1_axis2])

theorem induced_psi2B1 {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
    (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2)
    (hk : ∀ g a, ρ g (k1.val a) = k1.val (ρ g a))
    (hz : ∀ g a, ρ g (z1 a) = z1 (ρ g a)) (g : G) (d : ParkerLoop)
    (hg : ρ g = psi2 d) :
    secondAxisDomain.inducedRepresentation ρ hA hk hz g = (psi2B1 d).toLinearMap := by
  apply b1_ext
  intro b
  change secondAxisDomain.inducedRepresentation ρ hA hk hz g (delta2 b) = psi2B1 d (delta2 b)
  rw [psi2B1_delta]
  exact induced_delta2 ρ hA hk hz g b _ (by rw [hg, psi2_on_axis2])

theorem induced_psi3B1 {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
    (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2)
    (hk : ∀ g a, ρ g (k1.val a) = k1.val (ρ g a))
    (hz : ∀ g a, ρ g (z1 a) = z1 (ρ g a)) (g : G) (d : ParkerLoop)
    (hg : ρ g = psi3 d) :
    secondAxisDomain.inducedRepresentation ρ hA hk hz g = (psi3B1 d).toLinearMap := by
  apply b1_ext
  intro b
  change secondAxisDomain.inducedRepresentation ρ hA hk hz g (delta2 b) = psi3B1 d (delta2 b)
  rw [psi3B1_delta]
  exact induced_delta2 ρ hA hk hz g b _ (by rw [hg, psi3_on_axis2])

theorem induced_psiAut2Even {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
    (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2)
    (hk : ∀ g a, ρ g (k1.val a) = k1.val (ρ g a))
    (hz : ∀ g a, ρ g (z1 a) = z1 (ρ g a)) (g : G)
    (e : Equiv.Perm ParkerLoop) (he : IsStandard e) (hε : e parkerOmega = parkerOmega)
    (hg : ρ g = psiAut2 e) :
    secondAxisDomain.inducedRepresentation ρ hA hk hz g = (psiAut2Even e he hε).toLinearMap := by
  apply b1_ext
  intro b
  change secondAxisDomain.inducedRepresentation ρ hA hk hz g (delta2 b) = psiAut2Even e he hε (delta2 b)
  rw [psiAut2Even_delta]
  exact induced_delta2 ρ hA hk hz g b _ (by rw [hg, psiAut2_even_axis e hε])

theorem induced_psi1B3 {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
    (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2)
    (hk : ∀ g a, ρ g (k3.val a) = k3.val (ρ g a))
    (hz : ∀ g a, ρ g (z3 a) = z3 (ρ g a)) (g : G) (d : ParkerLoop)
    (hg : ρ g = psi1 d) :
    B3Axis2.inducedRepresentation ρ hA hk hz g = (psi1B3 d).toLinearMap := by
  apply b3_ext
  intro b
  change B3Axis2.inducedRepresentation ρ hA hk hz g (B3Axis2.delta b) = psi1B3 d (B3Axis2.delta b)
  rw [psi1B3_delta]
  exact B3Axis2.inducedRepresentation_delta ρ hA hk hz g b _ (by rw [hg, psi1_axis2])

theorem induced_psi2B3 {G : Type*} [Group G] (ρ : G →* Equiv.Perm Triple)
    (hA : ∀ g a, a ∈ A2 ↔ ρ g a ∈ A2)
    (hk : ∀ g a, ρ g (k3.val a) = k3.val (ρ g a))
    (hz : ∀ g a, ρ g (z3 a) = z3 (ρ g a)) (g : G) (d : ParkerLoop)
    (hg : ρ g = psi2 d) :
    B3Axis2.inducedRepresentation ρ hA hk hz g = (psi2B3 d).toLinearMap := by
  apply b3_ext
  intro b
  change B3Axis2.inducedRepresentation ρ hA hk hz g (B3Axis2.delta b) = psi2B3 d (B3Axis2.delta b)
  rw [psi2B3_delta]
  exact B3Axis2.inducedRepresentation_delta ρ hA hk hz g b _ (by rw [hg, psi2_on_axis2])

theorem psiAut2Odd_isometry (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega ≠ parkerOmega) (v w : B1A2) :
    B3Axis2.form (psiAut2Odd e he hε v) (psiAut2Odd e he hε w) = secondAxisDomain.form v w := by
  let : Fintype firstSecond.geometry.pairing.Orbit :=
    inferInstanceAs (Fintype secondAxisDomain.pairing.Orbit)
  exact firstSecond.oddAction_isometry thirdSecond e he hε rfl v w

theorem psiAut1Odd_isometry (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega ≠ parkerOmega) (v w : B1A2) :
    thirdAxisDomain.form (psiAut1Odd e he hε v) (psiAut1Odd e he hε w) = secondAxisDomain.form v w := by
  let : Fintype firstSecond.geometry.pairing.Orbit :=
    inferInstanceAs (Fintype secondAxisDomain.pairing.Orbit)
  let : Fintype firstThird.geometry.pairing.Orbit :=
    inferInstanceAs (Fintype thirdAxisDomain.pairing.Orbit)
  exact firstSecond.oddAction_isometry firstThird e he hε rfl v w

theorem psiAut1OddBack_isometry (e : Equiv.Perm ParkerLoop) (he : IsStandard e)
    (hε : e parkerOmega ≠ parkerOmega) (v w : B1A3) :
    secondAxisDomain.form (psiAut1OddBack e he hε v) (psiAut1OddBack e he hε w) = thirdAxisDomain.form v w := by
  let : Fintype firstSecond.geometry.pairing.Orbit :=
    inferInstanceAs (Fintype secondAxisDomain.pairing.Orbit)
  let : Fintype firstThird.geometry.pairing.Orbit :=
    inferInstanceAs (Fintype thirdAxisDomain.pairing.Orbit)
  exact firstThird.oddAction_isometry firstSecond e he hε rfl v w

end Sporadic.Monster.Construction.TrialitySpin.SpinActions
