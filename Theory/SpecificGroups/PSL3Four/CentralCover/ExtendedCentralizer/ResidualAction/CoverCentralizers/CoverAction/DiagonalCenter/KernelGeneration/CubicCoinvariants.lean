module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter.KernelGeneration.BinaryCoordinates

/-!
# Cubic actions on a binary kernel quotient

A nonidentity cubic automorphism of a binary plane cycles its three nonzero
points, so its displacement map is surjective. Apply this to the universal
kernel modulo squares, using its proved C₄ × C₄ × C₃ group structure.
It is enough to exhibit one moved square class; no choice of equivariant
coordinates is required. The same witness gives movement for the square
of the actor. This is the coinvariant step of Aschbacher--Smith 15.3.38,
printed p.1136, with multiplier background I.1.3(6).
-/

public section
open PerfectCentralCovering Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter
private theorem binary_four (x y : BinaryKernelPlane)
    (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) (v : BinaryKernelPlane) :
    v = 1 ∨ v = x ∨ v = y ∨ v = x * y := by
  have h : ∀ a b c : BinaryKernelPlane,
      a = 1 ∨ b = 1 ∨ a = b ∨ c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
    decide +kernel
  rcases h x y v with h | h | h | h
  · exact (hx h).elim
  · exact (hy h).elim
  · exact (hxy h).elim
  · exact h

private theorem binary_cancel (x y : BinaryKernelPlane) :
    x * (x * y) = y ∧ x⁻¹ = x := by
  revert x y
  decide +kernel

private theorem binary_displacement_surjective (f : BinaryKernelPlane → BinaryKernelPlane)
    (h1 : f 1 = 1) (hm : ∀ x y, f (x * y) = f x * f y)
    (h3 : ∀ x, f (f (f x)) = x) (hn : ∃ x, f x ≠ x) :
    ∀ z, ∃ w, f w * w⁻¹ = z := by
  have hi : Function.Injective f := by
    intro a b hab
    have h := congrArg (fun x => f (f x)) hab
    simpa only [h3] using h
  obtain ⟨x, hx⟩ := hn
  have hx1 : x ≠ 1 := by rintro rfl; exact hx h1
  have hy1 : f x ≠ 1 := by intro h; exact hx1 (hi (h.trans h1.symm))
  have hfy : f (f x) = x * f x := by
    rcases binary_four x (f x) hx1 hy1 (Ne.symm hx) (f (f x)) with h | h | h | h
    · exact (hy1 (hi (h.trans h1.symm))).elim
    · have h' := congrArg f h
      exact (hx (h'.symm.trans (h3 x))).elim
    · exact (hx (hi h)).elim
    · exact h
  have hfxy : f (x * f x) = x := by
    rw [hm, hfy, mul_comm x (f x)]
    exact (binary_cancel (f x) x).1
  intro z
  rcases binary_four x (f x) hx1 hy1 (Ne.symm hx) z with hz | hz | hz | hz
  all_goals rw [hz]
  · exact ⟨1, by rw [h1, inv_one, mul_one]⟩
  · refine ⟨f x, ?_⟩
    rw [hfy, mul_inv_cancel_right]
  · refine ⟨x * f x, ?_⟩
    rw [hfxy, (binary_cancel (x * f x) x).2]
    exact (binary_cancel x (f x)).1
  · exact ⟨x, by rw [(binary_cancel x x).2, mul_comm]⟩

private theorem binary_sq (v : BinaryKernelPlane) : v ^ 2 = 1 := by
  revert v
  decide +kernel

theorem universalKernelMap_cube (β : MulAut PSL) (h3 : β ^ 3 = 1)
    (z : (universalProjection PSL).ker) :
    universalKernelMap β (universalKernelMap β (universalKernelMap β z)) = z := by
  have h1 : universalLift (1 : MulAut PSL) = 1 := by
    apply Eq.symm
    exact universalLift_unique 1 1 (fun _ => rfl)
  have h : universalLift β * (universalLift β * universalLift β) = 1 := by
    rw [← universalLift_mul, ← universalLift_mul,
      show β * (β * β) = β ^ 3 by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
      h3, h1]
  apply Subtype.ext
  exact congrArg (fun a : MulAut (UniversalGroup PSL) => a z) h

private theorem binary_displacements_surjective {K : Type*} [Group K] (a : K →* K)
    (q : K →* BinaryKernelPlane) (hq : Function.Surjective q)
    (hsquare : ∀ z, q z = 1 → ∃ w, w ^ 2 = z)
    (hcube : ∀ z, a (a (a z)) = z)
    (hn : ∃ z, q (a z) ≠ q z) :
    ∀ v, ∃ w, q (a w * w⁻¹) = v := by
  have hker : q.ker ≤ (q.comp a).ker := by
    intro z hz
    obtain ⟨w, rfl⟩ := hsquare z hz
    change q (a (w ^ 2)) = 1
    rw [map_pow, map_pow, binary_sq]
  let f : BinaryKernelPlane →* BinaryKernelPlane :=
    q.liftOfSurjective hq ⟨q.comp a, hker⟩
  have hf (z : K) : f (q z) = q (a z) :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z
  have hf3 (v) : f (f (f v)) = v := by
    obtain ⟨z, rfl⟩ := hq v
    rw [hf, hf, hf, hcube]
  have hfn : ∃ v, f v ≠ v := by
    obtain ⟨z, hz⟩ := hn
    exact ⟨q z, by rwa [hf]⟩
  intro v
  obtain ⟨t, ht⟩ := binary_displacement_surjective f (map_one f) (map_mul f) hf3 hfn v
  obtain ⟨w, rfl⟩ := hq t
  exact ⟨w, by simpa only [map_mul, map_inv, hf] using ht⟩
theorem universalKernelMap_mul (β γ : MulAut PSL)
    (z : (universalProjection PSL).ker) :
    universalKernelMap (β * γ) z = universalKernelMap β (universalKernelMap γ z) := by
  apply Subtype.ext
  exact congrArg (fun a : MulAut (UniversalGroup PSL) => a z) (universalLift_mul β γ)

/-- A moved square class for a cubic actor gives one for its square. -/
theorem exists_moved_square_class_square (β : MulAut PSL) (h3 : β ^ 3 = 1)
    (hn : ∃ z : (universalProjection PSL).ker,
      ¬ ∃ w, w ^ 2 = universalKernelMap β z * z⁻¹) :
    ∃ z : (universalProjection PSL).ker,
      ¬ ∃ w, w ^ 2 = universalKernelMap (β ^ 2) z * z⁻¹ := by
  obtain ⟨z, hz⟩ := hn
  refine ⟨universalKernelMap β z, ?_⟩
  rintro ⟨w, hw⟩
  apply hz
  refine ⟨w⁻¹, ?_⟩
  rw [show β ^ 2 = β * β from pow_two β, universalKernelMap_mul,
    universalKernelMap_cube β h3] at hw
  rw [inv_pow, hw, _root_.mul_inv_rev, inv_inv]

/-- One genuinely moved square class suffices for the universal-kernel
coinvariant calculation, given its (nonequivariant) multiplier structure. -/
theorem kernel_generation_of_moved_square_class (β : MulAut PSL) (h3 : β ^ 3 = 1)
    (e : (universalProjection PSL).ker ≃* ExceptionalMultiplierCoordinates)
    (hn : ∃ z : (universalProjection PSL).ker,
      ¬ ∃ w, w ^ 2 = universalKernelMap β z * z⁻¹) :
    (universalProjection PSL).ker ≤ kernelSquaresAndDisplacements β := by
  let q := multiplierBinaryCoordinates.comp e.toMonoidHom
  have hq : Function.Surjective q := multiplierBinaryCoordinates_surjective.comp e.surjective
  have hsquare : ∀ z, q z = 1 → ∃ w, w ^ 2 = z := by
    intro z hz
    obtain ⟨y, hy⟩ := (multiplierBinaryCoordinates_eq_one_iff_square (e z)).mp hz
    refine ⟨e.symm y, e.injective ?_⟩
    simpa only [map_pow, e.apply_symm_apply] using hy
  have hmove : ∃ z, q (universalKernelMap β z) ≠ q z := by
    obtain ⟨z, hz⟩ := hn
    refine ⟨z, fun he => hz (hsquare _ ?_)⟩
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hd := binary_displacements_surjective (universalKernelMap β) q hq hsquare
    (universalKernelMap_cube β h3) hmove
  intro z hz
  let z' : (universalProjection PSL).ker := ⟨z, hz⟩
  obtain ⟨w, hw⟩ := hd (q z')
  let d := universalKernelMap β w * w⁻¹
  have hqd : q d = q z' := hw
  have hv : q (z' * d⁻¹) = 1 := by rw [map_mul, map_inv, hqd, mul_inv_cancel]
  obtain ⟨s, hs⟩ := hsquare _ hv
  have hsN : (s : UniversalGroup PSL) ^ 2 ∈ kernelSquaresAndDisplacements β :=
    subset_closure (Or.inl ⟨s, rfl⟩)
  have hdN : (d : UniversalGroup PSL) ∈ kernelSquaresAndDisplacements β :=
    subset_closure (Or.inr ⟨w, rfl⟩)
  have he : (s : UniversalGroup PSL) ^ 2 * (d : UniversalGroup PSL) = z := by
    have he := congrArg Subtype.val hs
    change (s : UniversalGroup PSL) ^ 2 = z * (d : UniversalGroup PSL)⁻¹ at he
    rw [he, inv_mul_cancel_right]
  exact he ▸ (kernelSquaresAndDisplacements β).mul_mem hsN hdN

end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter
