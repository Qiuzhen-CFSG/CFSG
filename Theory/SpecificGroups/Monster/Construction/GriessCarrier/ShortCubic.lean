module
public import Theory.SpecificGroups.Monster.Construction.GriessCarrier.SignedBlocks
public import Theory.SpecificGroups.Monster.Construction.GriessCarrier.Blocks
public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortLifts

/-!
# The cubic block on actual short extraspecial lifts

The coefficient at three short involutions is one when their product is the
identity, minus one when it is the distinguished central involution, and zero
otherwise. Inversion and conjugation prove both adjacent symmetries. Multiplying
any lift by the center negates the coefficient, so repeated signed extension
constructs a trilinear form on the existing LocalC short space.

The coefficient is proved equal to the pairing with the source product `y(rs)`
when `rs` is short, and zero otherwise. The short-product involution law also
proves the commutation used in the source. The sole external parameter is the
Section 27 lattice comparison; the fixed carrier must instantiate it.

Source: Aschbacher, *Sporadic Groups*, (28.4) and Lemma 28.8, pp. 151–152.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.Griess
open LocalC TrialitySpin TrialitySpin.SignedModules
attribute [local instance] Classical.propDecidable

private theorem center_mul (q : Q1Image) :
    q * q1ImageCenterGenerator = q1ImageCenterGenerator * q :=
  Subgroup.mem_center_iff.mp centerGenerator_mem q

private theorem center_inv : q1ImageCenterGenerator⁻¹ = q1ImageCenterGenerator := by
  apply inv_eq_of_mul_eq_one_right
  exact pow_two q1ImageCenterGenerator ▸ q1ImageCenterGenerator_sq

/-- The signed coefficient of a central product: one at `1`, minus one at `z`. -/
def centralCoefficient (q : Q1Image) : ℝ :=
  (if q = 1 then 1 else 0) - (if q = q1ImageCenterGenerator then 1 else 0)

private theorem centralCoefficient_inv (q : Q1Image) :
    centralCoefficient q⁻¹ = centralCoefficient q := by
  simp only [centralCoefficient, inv_eq_iff_eq_inv, center_inv, inv_one]

private theorem centralCoefficient_conj (a q : Q1Image) :
    centralCoefficient (a * q * a⁻¹) = centralCoefficient q := by
  have hz : a * q * a⁻¹ = q1ImageCenterGenerator ↔ q = q1ImageCenterGenerator := by
    rw [mul_inv_eq_iff_eq_mul, ← center_mul, mul_left_cancel_iff]
  have h1 : a * q * a⁻¹ = 1 ↔ q = 1 := by
    rw [mul_inv_eq_iff_eq_mul, one_mul, mul_eq_left]
  simp only [centralCoefficient, h1, hz]

private theorem centralCoefficient_sign (q : Q1Image) :
    centralCoefficient (q * q1ImageCenterGenerator) = -centralCoefficient q := by
  simp only [centralCoefficient, mul_eq_one_iff_eq_inv, center_inv, mul_eq_right]
  ring

variable (e : LatticeComparison)

private theorem short_inv (r : ShortLift e) : r.val⁻¹ = r.val := by
  apply inv_eq_of_mul_eq_one_right
  exact pow_two r.val ▸ shortLift_square e r

/-- The cubic basis coefficient, using multiplication of actual short lifts. -/
def shortCoefficient (r s t : ShortLift e) : ℝ :=
  centralCoefficient (r.val * s.val * t.val)

/-- Reversal and conjugation preserve central coefficients. This proves the
adjacent swaps even when the product is noncentral. -/
theorem shortCoefficient_swap_left (r s t : ShortLift e) :
    shortCoefficient e r s t = shortCoefficient e s r t := by
  have h := centralCoefficient_conj t.val (r.val * s.val * t.val)⁻¹
  rw [centralCoefficient_inv] at h
  have he : t.val * (r.val * s.val * t.val)⁻¹ * t.val⁻¹ = s.val * r.val * t.val := by
    simp only [mul_inv_rev, short_inv, ← mul_assoc]
    rw [← pow_two, shortLift_square, one_mul]
  rw [he] at h
  exact h.symm

theorem shortCoefficient_swap_right (r s t : ShortLift e) :
    shortCoefficient e r s t = shortCoefficient e r t s := by
  have h := centralCoefficient_conj r.val (r.val * s.val * t.val)⁻¹
  rw [centralCoefficient_inv] at h
  have he : r.val * (r.val * s.val * t.val)⁻¹ * r.val⁻¹ = r.val * t.val * s.val := by
    simp only [mul_inv_rev, short_inv, mul_assoc]
    rw [← pow_two, shortLift_square, mul_one]
  rw [he] at h
  exact h.symm

theorem shortCoefficient_sign_right (r s t : ShortLift e) :
    shortCoefficient e r s ((shortLiftSigns e).flip t) = -shortCoefficient e r s t := by
  change centralCoefficient (r.val * s.val * (t.val * q1ImageCenterGenerator)) = _
  rw [← mul_assoc, centralCoefficient_sign]
  rfl

theorem shortCoefficient_sign_middle (r s t : ShortLift e) :
    shortCoefficient e r ((shortLiftSigns e).flip s) t = -shortCoefficient e r s t := by
  rw [shortCoefficient_swap_right, shortCoefficient_sign_right, shortCoefficient_swap_right e r t s]

theorem shortCoefficient_sign_left (r s t : ShortLift e) :
    shortCoefficient e ((shortLiftSigns e).flip r) s t = -shortCoefficient e r s t := by
  rw [shortCoefficient_swap_left, shortCoefficient_sign_middle, shortCoefficient_swap_left e s r t]

/-- The source cubic block, descended in all three variables through `y(rz)=-y(r)`. -/
def shortCubic : ShortSpace e →ₗ[ℝ] ShortSpace e →ₗ[ℝ] ShortSpace e →ₗ[ℝ] ℝ :=
  signedExtension (shortLiftSigns e) (fun r =>
    signedExtension (shortLiftSigns e) (fun s =>
      signedExtension (shortLiftSigns e) (shortCoefficient e r s)))

theorem shortCubic_vector (r s t : ShortLift e) :
    shortCubic e (shortVector e r) (shortVector e s) (shortVector e t) =
      shortCoefficient e r s t := by
  unfold shortCubic shortVector
  rw [signedExtension_delta]
  · rw [signedExtension_delta]
    · exact signedExtension_delta _ _ (shortCoefficient_sign_right e r s) t
    · intro u
      apply (shortLiftSigns e).basis.ext
      intro i
      simp only [signedExtension_basis, LinearMap.neg_apply, shortCoefficient_sign_middle]
  · intro u
    apply (shortLiftSigns e).basis.ext
    intro i
    apply (shortLiftSigns e).basis.ext
    intro j
    simp only [signedExtension_basis, LinearMap.neg_apply, shortCoefficient_sign_left]

theorem shortCubic_swap_left (x y z : ShortSpace e) :
    shortCubic e x y z = shortCubic e y x z := by
  have h : shortCubic e = (shortCubic e).flip := by
    apply (shortLiftSigns e).basis.ext
    intro i
    apply (shortLiftSigns e).basis.ext
    intro j
    apply (shortLiftSigns e).basis.ext
    intro k
    simp only [LinearMap.flip_apply, shortCubic, signedExtension_basis]
    exact shortCoefficient_swap_left e _ _ _
  exact congrArg (fun f => f x y z) h

theorem shortCubic_swap_right (x y z : ShortSpace e) :
    shortCubic e x y z = shortCubic e x z y := by
  exact signedExtension_symmetric (shortLiftSigns e) _ (fun r s t => by
    have h : signedExtension (shortLiftSigns e) (fun s =>
        signedExtension (shortLiftSigns e) (shortCoefficient e r s)) =
        (signedExtension (shortLiftSigns e) (fun s =>
        signedExtension (shortLiftSigns e) (shortCoefficient e r s))).flip := by
      apply (shortLiftSigns e).basis.ext
      intro i
      apply (shortLiftSigns e).basis.ext
      intro j
      simp only [LinearMap.flip_apply, signedExtension_basis]
      exact shortCoefficient_swap_right e _ _ _
    exact congrArg (fun f => f s t) h) x y z

/-- When the product of short lifts is short, its involution law forces
commutation, as used in the source proof of 28.8. -/
theorem shortLift_commute_of_product_short (r s : ShortLift e)
    (h : latticeClass e (r.val * s.val) ∈ Atlas.Lattices.shellClasses 4) :
    Commute r.val s.val := by
  have hi := short_inv e (⟨r.val * s.val, h⟩ : ShortLift e)
  change (r.val * s.val)⁻¹ = r.val * s.val at hi
  rw [mul_inv_rev, short_inv, short_inv] at hi
  exact hi.symm

/-- Rewrite the central-product coefficient as signed equality of lifts. -/
theorem shortCoefficient_eq (r s t : ShortLift e) :
    shortCoefficient e r s t =
      (if r.val * s.val = t.val then 1 else 0) -
      (if r.val * s.val = t.val * q1ImageCenterGenerator then 1 else 0) := by
  have h1 : r.val * s.val * t.val = 1 ↔ r.val * s.val = t.val := by
    rw [mul_eq_one_iff_eq_inv, short_inv]
  have hz : r.val * s.val * t.val = q1ImageCenterGenerator ↔
      r.val * s.val = t.val * q1ImageCenterGenerator := by
    rw [← eq_mul_inv_iff_mul_eq, short_inv, center_mul]
  simp only [shortCoefficient, centralCoefficient, h1, hz]

/-- Exact agreement with the source pairing when `rs` is a short lift. -/
theorem shortCoefficient_pairing (r s t : ShortLift e)
    (h : latticeClass e (r.val * s.val) ∈ Atlas.Lattices.shellClasses 4) :
    shortCoefficient e r s t =
      shortForm e (shortVector e ⟨r.val * s.val, h⟩) (shortVector e t) := by
  rw [shortCoefficient_eq]
  change _ = (shortLiftSigns e).form ((shortLiftSigns e).delta (⟨r.val * s.val, h⟩ : ShortLift e))
    ((shortLiftSigns e).delta t)
  rw [(shortLiftSigns e).form_delta (⟨r.val * s.val, h⟩ : ShortLift e) ((shortLiftSigns e).delta t),
    (shortLiftSigns e).delta_apply t (⟨r.val * s.val, h⟩ : ShortLift e)]
  have h1 : (⟨r.val * s.val, h⟩ : ShortLift e) = t ↔ r.val * s.val = t.val :=
    Subtype.ext_iff
  have hz : (⟨r.val * s.val, h⟩ : ShortLift e) = (shortLiftSigns e).flip t ↔
      r.val * s.val = t.val * q1ImageCenterGenerator := Subtype.ext_iff
  exact congrArg₂ (fun a b : ℝ => a - b)
    (if_congr h1.symm rfl rfl)
    (if_congr hz.symm rfl rfl)

/-- Every nonzero coefficient has a short product; this is the zero clause
of (28.4), rather than an additional support assumption. -/
theorem shortCoefficient_zero (r s t : ShortLift e)
    (h : latticeClass e (r.val * s.val) ∉ Atlas.Lattices.shellClasses 4) :
    shortCoefficient e r s t = 0 := by
  have h1 : r.val * s.val ≠ t.val := by
    intro he
    apply h
    rw [he]
    exact t.prop
  have hz : r.val * s.val ≠ t.val * q1ImageCenterGenerator := by
    intro he
    apply h
    rw [he, latticeClass_mul, latticeClass_centerGenerator, add_zero]
    exact t.prop
  simp only [shortCoefficient_eq, h1, hz, if_false, sub_self]

/-- The basis product prescribed in (28.4). Its pairing is the cubic block. -/
def shortSourceProduct (r s : ShortLift e) : ShortSpace e :=
  if h : latticeClass e (r.val * s.val) ∈ Atlas.Lattices.shellClasses 4 then
    shortVector e ⟨r.val * s.val, h⟩ else 0

theorem shortCubic_source (r s t : ShortLift e) :
    shortCubic e (shortVector e r) (shortVector e s) (shortVector e t) =
      shortForm e (shortSourceProduct e r s) (shortVector e t) := by
  rw [shortCubic_vector]
  unfold shortSourceProduct
  split_ifs with h
  · exact shortCoefficient_pairing e r s t h
  · rw [shortCoefficient_zero e r s t h]
    simp

/-- Full permutation symmetry of the actual short-lift block. -/
theorem shortCubic_permute (σ : Equiv.Perm (Fin 3)) (v : Fin 3 → ShortSpace e) :
    shortCubic e (v (σ 0)) (v (σ 1)) (v (σ 2)) = shortCubic e (v 0) (v 1) (v 2) :=
  permute_of_swap _ (shortCubic_swap_left e) (shortCubic_swap_right e) σ v

end Sporadic.Monster.Construction.Griess
