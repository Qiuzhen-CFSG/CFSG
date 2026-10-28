module

public import Theory.SpecificGroups.Symplectic.FundamentalPlane

/-!
# The fundamental symplectic centralizer and its residual

In odd positive characteristic, projective commutation with a fundamental
transvection lifts to commutation in Sp: the central commutator has square one
and odd order. Commutation with the two marked transvections forces the same
scalar on both vectors of the hyperbolic pair. Removing this central scalar
places the lift in the pointwise pair stabilizer, which is the full symplectic
group on the orthogonal complement in the published `headTail` coordinates.

Consequently the published complementary map exhausts the actual centralizer.
Its previously proved containment in the prime-to-characteristic residual
identifies that residual with the complementary Sp, including its full center.
The equivalence and subgroup equality retain the literal ambient quotient maps.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17,
printed p.39 of `refs/quasithin.pdf`, the assertion `J ≅ Sp₂ₙ₋₂(q)` with `n = k+1`.
This proof uses the ATLAS-attributed scalar, transvection and pair-stabilizer
APIs in `PSp4Three`, via the published fundamental-plane module.
-/

@[expose] public noncomputable section

open Matrix Matrix.PSp4Three
namespace Theory.SpecificGroups.Symplectic.FundamentalPlane
variable {F : Type*} [Field F]

private theorem central_square (k : ℕ) (g : Sp (k+1) F)
    (hg : g ∈ Subgroup.center (Sp (k+1) F)) : g ^ 2 = 1 := by
  obtain ⟨a, ha⟩ := central_is_scalar g hg
  have hp : form (g • Matrix.PSp4Three.e (n := k+1) (F := F) 0) (g • f 0) =
      form (Matrix.PSp4Three.e (n := k+1) (F := F) 0) (f 0) := preserves g _ _
  rw [ha, ha] at hp
  have ha2 : a * a = 1 := by
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, form_f_right,
      Matrix.PSp4Three.e, Pi.single_eq_same, mul_one] using hp
  apply ext_action
  intro x
  rw [pow_two, mul_smul, ha, ha, smul_smul, ha2, one_smul, one_smul]

private theorem lift_commute (k : ℕ) {r : ℕ} (hr : Odd r)
    (g t : Sp (k+1) F) (ht : t ^ r = 1)
    (hc : Commute (projection g) (projection t)) : Commute g t := by
  let z := g * t * g⁻¹ * t⁻¹
  have hz : z ∈ Subgroup.center (Sp (k+1) F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change projection z = 1
    simp only [z, map_mul, map_inv]
    rw [hc.eq]
    group
  have hcomm : Commute (g * t * g⁻¹) t := by
    have h := (show Commute z t from (Subgroup.mem_center_iff.mp hz t).symm).mul_left
      (Commute.refl t)
    simpa only [z, inv_mul_cancel_right] using h
  have hzr : z ^ r = 1 := by
    rw [hcomm.inv_right.mul_pow, conj_pow, ht, inv_pow, ht, inv_one,
      mul_one, mul_one, mul_inv_cancel]
  have hz1 : z = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (central_square k z hz))
      (orderOf_dvd_of_pow_eq_one hzr)
    simpa only [hr.coprime_two_left.gcd_eq_one] using hd
  change g * t = t * g
  have h := congrArg (fun x => x * t * g) hz1
  simpa only [z, inv_mul_cancel_right, mul_assoc, inv_mul_cancel, mul_one, one_mul] using h

private theorem first_transvection (k : ℕ) (v : Vector 1 F) (a : F) :
    firstHom k (transvection v a) =
      transvection ((headTail k).symm (pairCoord v, 0)) a := by
  apply ext_action
  intro x
  apply (headTail k).injective
  rw [firstHom_headTail, transvection_apply, map_add, map_smul,
    LinearEquiv.apply_symm_apply]
  have hf : form x ((headTail k).symm (pairCoord v, 0)) =
      form ((pairCoord (F := F)).symm (headTail k x).1) v := by
    rw [form_headTail, LinearEquiv.apply_symm_apply, ← pair_form]
    rw [LinearEquiv.symm_apply_apply]
    simp only [map_zero, add_zero]
  rw [hf]
  simp only [pairAction, LinearEquiv.trans_apply, toLinear_apply,
    transvection_apply, map_add, map_smul, LinearEquiv.apply_symm_apply]
  ext <;> simp

private theorem scalar_of_commute_transvection {n : ℕ} (g : Sp n F)
    (v : Vector n F) (hv : v ≠ 0) (hc : Commute g (transvection v 1)) :
    ∃ a : F, g • v = a • v := by
  have hgv : g • v ≠ 0 := by
    change toLinear g v ≠ 0
    exact (map_ne_zero_iff (toLinear g) (toLinear g).injective).mpr hv
  obtain ⟨x, hx⟩ := exists_form_left hgv 1
  have ht := transvection_conjugate g v 1
  rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one] at ht
  have h := congrArg (fun t : Sp n F => t • x) ht
  refine ⟨form x v, ?_⟩
  simpa [transvection_apply, hx] using h.symm

private theorem commute_marked_transvections (k : ℕ) {r : ℕ}
    [Fact r.Prime] [CharP F r] (hr : r ≠ 2)
    (g : Sp (k+1) F) (hg : projection g ∈ centralizer k) :
    Commute g (transvection (Matrix.PSp4Three.e 0) 1) ∧ Commute g (transvection (f 0) 1) := by
  have hc (v : Vector 1 F) :
      Commute g (firstHom k (transvection v 1)) := by
    apply lift_commute k (Nat.Prime.odd_of_ne_two Fact.out hr)
    · rw [← map_pow, transvection_pow]
      simp [nsmul_eq_mul]
    · have h := (Subgroup.mem_centralizer_iff.mp hg)
        (projectFirst k (transvection v 1)) (by
          rw [fundamental_range]
          exact ⟨transvection v 1, rfl⟩)
      exact h.symm
  have he : (headTail k).symm (pairCoord (Matrix.PSp4Three.e (n := 1) (F := F) 0), 0) = Matrix.PSp4Three.e 0 := by
    apply (headTail k).injective
    simp [pairCoord_apply]
  have hf : (headTail k).symm (pairCoord (f (n := 1) (F := F) 0), 0) = f 0 := by
    apply (headTail k).injective
    simp [pairCoord_apply]
  constructor
  · simpa only [first_transvection, he] using hc (Matrix.PSp4Three.e 0)
  · simpa only [first_transvection, hf] using hc (f 0)

private theorem marked_scalar (k : ℕ) (g : Sp (k+1) F)
    (he : Commute g (transvection (Matrix.PSp4Three.e 0) 1))
    (hf : Commute g (transvection (f 0) 1)) :
    ∃ a : F, a * a = 1 ∧ g • Matrix.PSp4Three.e (n := k+1) (F := F) 0 = a • Matrix.PSp4Three.e (n := k+1) 0 ∧
      g • f (n := k+1) (F := F) 0 = a • f (n := k+1) 0 := by
  have hne : Matrix.PSp4Three.e (n := k+1) (F := F) 0 ≠ 0 := by
    intro h
    have := congrFun h (.inl 0)
    simp [Matrix.PSp4Three.e] at this
  have hnf : f (n := k+1) (F := F) 0 ≠ 0 := by
    intro h
    have := congrFun h (.inr 0)
    simp [f] at this
  obtain ⟨a, ha⟩ := scalar_of_commute_transvection g (Matrix.PSp4Three.e 0) hne he
  obtain ⟨b, hb⟩ := scalar_of_commute_transvection g (f 0) hnf hf
  have htf : transvection (f (n := k+1) (F := F) 0) 1 • Matrix.PSp4Three.e (n := k+1) (F := F) 0 =
      Matrix.PSp4Three.e (n := k+1) (F := F) 0 + f 0 := by
    simp [transvection_apply, Matrix.PSp4Three.e]
  have hgadd : g • (Matrix.PSp4Three.e (n := k+1) (F := F) 0 + f 0) =
      g • Matrix.PSp4Three.e (n := k+1) (F := F) 0 + g • f (n := k+1) (F := F) 0 := (toLinear g).map_add _ _
  have h := congrArg
    (fun t : Sp (k+1) F => t • Matrix.PSp4Three.e (n := k+1) (F := F) 0) hf.eq
  rw [mul_smul, mul_smul, htf, hgadd, ha, hb, transvection_apply] at h
  have hab : b = a := by
    have hh := congrFun h (.inr 0)
    simp only [form_f_right] at hh
    simpa [Matrix.PSp4Three.e, f] using hh
  subst b
  refine ⟨a, ?_, ha, hb⟩
  have hp : form (g • Matrix.PSp4Three.e (n := k+1) (F := F) 0) (g • f 0) =
      form (Matrix.PSp4Three.e (n := k+1) (F := F) 0) (f 0) := preserves g _ _
  rw [ha, hb] at hp
  simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, form_f_right,
    Matrix.PSp4Three.e, Pi.single_eq_same, mul_one] using hp

private theorem scalar_correction (k : ℕ) (a : F) (ha : a * a = 1) :
    ∃ s : Sp (k+1) F, s ∈ Subgroup.center (Sp (k+1) F) ∧
      ∀ x : Vector (k+1) F, s • x = a • x := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let l := LinearEquiv.smulOfNeZero F (Vector (k+1) F) a ha0
  have hl (x y : Vector (k+1) F) : form (l x) (l y) = form x y := by
    change form (a • x) (a • y) = form x y
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc, ha, one_mul]
  refine ⟨ofLinear l hl, ?_, ?_⟩
  · apply scalar_is_central _ a
    intro x
    rw [ofLinear_apply]
    rfl
  · intro x
    rw [ofLinear_apply]
    rfl

/-- Every element of the fundamental projective centralizer comes from the
full symplectic group on the orthogonal complement. -/
theorem tailToCentralizer_surjective (k : ℕ) {r : ℕ}
    [Fact r.Prime] [CharP F r] (hr : r ≠ 2) :
    Function.Surjective (tailToCentralizer (F := F) k) := by
  intro x
  obtain ⟨g, hg⟩ := projection_surjective x.val
  have hgc : projection g ∈ centralizer k := hg ▸ x.property
  obtain ⟨he, hf⟩ := commute_marked_transvections k hr g hgc
  obtain ⟨a, ha, hae, haf⟩ := marked_scalar k g he hf
  obtain ⟨s, hs, hsa⟩ := scalar_correction k a ha
  have hsg : s * g ∈ pairStabilizer k F := by
    rw [mem_pairStabilizer]
    constructor
    · rw [mul_smul, hae, hsa, smul_smul, ha, one_smul]
    · rw [mul_smul, haf, hsa, smul_smul, ha, one_smul]
  let u : pairStabilizer k F := ⟨s * g, hsg⟩
  refine ⟨pairStabilizerEquiv u, ?_⟩
  apply Subtype.ext
  change projection (tailHom k (pairStabilizerEquiv u)) = x.val
  have hu : tailHom k (pairStabilizerEquiv u) = s * g :=
    congrArg Subtype.val (pairStabilizerEquiv.symm_apply_apply u)
  have hsproj : projection s = 1 := (QuotientGroup.eq_one_iff s).mpr hs
  rw [hu, map_mul, hsproj, one_mul, hg]

/-- The defining-characteristic residual is all of the fundamental centralizer. -/
theorem residual_eq_top (k r : ℕ) [Fact r.Prime] [CharP F r] (hr : r ≠ 2) :
    residual (F := F) k r = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨g, rfl⟩ := tailToCentralizer_surjective k hr x
  exact image_mem_residual k (tailToCentralizer k) g

/-- The published complementary map exhausts the literal residual J. -/
theorem tailToResidual_surjective (k r : ℕ) [Fact r.Prime] [CharP F r] (hr : r ≠ 2) :
    Function.Surjective (tailToResidual (F := F) k r) := by
  intro x
  obtain ⟨g, hg⟩ := tailToCentralizer_surjective k hr x.val
  exact ⟨g, Subtype.ext hg⟩

/-- The actual complementary symplectic group identifies with J via its
published embedding in the ambient central quotient. -/
noncomputable def tailResidualEquiv (k r : ℕ) [Fact r.Prime] [CharP F r] (hr : r ≠ 2) :
    Sp k F ≃* residual (F := F) k r :=
  MulEquiv.ofBijective (tailToResidual k r)
    ⟨tailToResidual_injective k r, tailToResidual_surjective k r hr⟩

@[simp] theorem tailResidualEquiv_apply (k r : ℕ) [Fact r.Prime] [CharP F r]
    (hr : r ≠ 2) (g : Sp k F) :
    tailResidualEquiv k r hr g = tailToResidual k r g := rfl

@[simp] theorem tailResidualEquiv_ambient (k r : ℕ) [Fact r.Prime] [CharP F r]
    (hr : r ≠ 2) (g : Sp k F) :
    (tailResidualEquiv k r hr g).val.val = projectTail k g := rfl

/-- Equality in the original projective ambient group, with both inclusions retained. -/
theorem residual_map_eq_projectTail_range (k r : ℕ) [Fact r.Prime] [CharP F r]
    (hr : r ≠ 2) :
    (residual (F := F) k r).map (centralizer k).subtype = (projectTail k).range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨g, hg⟩ := tailToResidual_surjective k r hr ⟨y, hy⟩
    exact ⟨g, congrArg (fun z : residual k r => z.val.val) hg⟩
  · rintro ⟨g, rfl⟩
    exact ⟨tailToCentralizer k g, (tailToResidual k r g).property, rfl⟩

end Theory.SpecificGroups.Symplectic.FundamentalPlane
