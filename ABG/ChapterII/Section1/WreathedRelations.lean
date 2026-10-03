module
public import ABG.ChapterII.Section1.WreathedPresentation

/-!
# Elementary identities in the wreathed presentation

ABG Chapter II §1 Lemma 2(x), article p.10, changes generators to Y and sz.
The square of sz is u; multiplication by r recovers s². Since the height is
at least two, a power of s² gives x₂, so d recovers z and then sz recovers s.
This proves generation without any unproved normal-form or subgroup claims.
The accompanying identities identify x with the half-power of r and show
that d squares to x and inverts r, preparing the quaternion recognition.
All notation is the chosen presentation on article p.9.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : ABG.Wreathed.Presentation S n)

public theorem z_inv : P.z⁻¹ = P.z := by
  apply inv_eq_of_mul_eq_one_left
  simpa [pow_two] using P.z_sq

public theorem z_mul_s : P.z * P.s = P.t * P.z := by
  have h := P.conj_s
  rw [P.z_inv] at h
  calc
    P.z * P.s = (P.z * P.s * P.z) * P.z := by rw [mul_assoc, ← pow_two, P.z_sq, mul_one]
    _ = P.t * P.z := by rw [h]

public theorem z_mul_t : P.z * P.t = P.s * P.z := by
  have h := P.conj_t
  rw [P.z_inv] at h
  calc
    P.z * P.t = (P.z * P.t * P.z) * P.z := by rw [mul_assoc, ← pow_two, P.z_sq, mul_one]
    _ = P.s * P.z := by rw [h]

public theorem sz_sq : (P.s * P.z) ^ 2 = P.u := by
  calc
    (P.s * P.z) ^ 2 = P.s * (P.z * P.s) * P.z := by simp only [pow_two, mul_assoc]
    _ = P.s * (P.t * P.z) * P.z := by rw [P.z_mul_s]
    _ = P.u := by simp [u, mul_assoc, ← pow_two, P.z_sq]

public theorem u_mul_r : P.u * P.r = P.s ^ 2 := by
  dsimp [u, r]
  calc
    P.s * P.t * (P.s * P.t⁻¹) = P.s * (P.t * P.s) * P.t⁻¹ := by group
    _ = P.s * (P.s * P.t) * P.t⁻¹ := by rw [← P.commute]
    _ = P.s ^ 2 := by simp only [pow_two]; group

public theorem generator_change :
    (P.s * P.z) ^ 2 = P.u ∧ P.Y ⊔ Subgroup.zpowers (P.s * P.z) = ⊤ := by
  refine ⟨P.sz_sq, ?_⟩
  let H := P.Y ⊔ Subgroup.zpowers (P.s * P.z)
  have hr : P.r ∈ H := (show P.Y ≤ H from le_sup_left) (Subgroup.subset_closure (by simp))
  have hd : P.d ∈ H := (show P.Y ≤ H from le_sup_left) (Subgroup.subset_closure (by simp))
  have hv : P.s * P.z ∈ H := (show Subgroup.zpowers (P.s * P.z) ≤ H from le_sup_right) (Subgroup.mem_zpowers _)
  have hu : P.u ∈ H := P.sz_sq ▸ H.pow_mem hv 2
  have hs2 : P.s ^ 2 ∈ H := P.u_mul_r ▸ H.mul_mem hu hr
  have hx2 : P.x₂ ∈ H := by
    have he : 2 * 2 ^ (n - 2) = 2 ^ (n - 1) := by
      have hn : n - 1 = (n - 2) + 1 := by have := P.height; omega
      rw [hn, pow_succ, Nat.mul_comm]
    simpa only [x₂, ← pow_mul, he] using H.pow_mem hs2 (2 ^ (n - 2))
  have hz : P.z ∈ H := by
    have := H.mul_mem (H.inv_mem hx2) hd
    simpa [d] using this
  have hs : P.s ∈ H := by
    have := H.mul_mem hv (H.inv_mem hz)
    simpa only [mul_inv_cancel_right] using this
  have ht : P.t ∈ H := by
    have := H.mul_mem (H.inv_mem hs) hu
    simpa [u] using this
  apply top_unique
  rw [← P.generate]
  apply (Subgroup.closure_le H).2
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact hs
  · exact ht
  · exact hz

public theorem z_mul_s_pow (k : ℕ) : P.z * P.s ^ k = P.t ^ k * P.z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, P.z_mul_s, ← mul_assoc, ← pow_succ]

public theorem z_mul_t_pow (k : ℕ) : P.z * P.t ^ k = P.s ^ k * P.z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, P.z_mul_t, ← mul_assoc, ← pow_succ]

include P in
private theorem half_double : 2 ^ (n - 1) * 2 = 2 ^ n := by
  have hn : n = (n - 1) + 1 := by have := P.height; omega
  conv_rhs => rw [hn, pow_succ]

public theorem x₂_sq : P.x₂ ^ 2 = 1 := by
  rw [x₂, ← pow_mul, P.half_double, P.s_pow]

public theorem x₃_sq : P.x₃ ^ 2 = 1 := by
  rw [x₃, ← pow_mul, P.half_double, P.t_pow]

public theorem x_eq_x₂_mul_x₃ : P.x = P.x₂ * P.x₃ := by
  exact (show Commute P.s P.t from P.commute).mul_pow (2 ^ (n - 1))

public theorem r_half : P.r ^ (2 ^ (n - 1)) = P.x := by
  have hi : P.x₃⁻¹ = P.x₃ := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using P.x₃_sq)
  rw [P.x_eq_x₂_mul_x₃]
  dsimp only [r]
  rw [(show Commute P.s P.t from P.commute).inv_right.mul_pow]
  simpa only [inv_pow, x₂, x₃] using congrArg (P.x₂ * ·) hi

public theorem d_sq : P.d ^ 2 = P.r ^ (2 ^ (n - 1)) := by
  rw [P.r_half, P.x_eq_x₂_mul_x₃]
  calc
    P.d ^ 2 = P.x₂ * (P.z * P.x₂) * P.z := by simp only [d, pow_two, mul_assoc]
    _ = P.x₂ * (P.x₃ * P.z) * P.z := by rw [x₂, P.z_mul_s_pow]; rfl
    _ = P.x₂ * P.x₃ := by simp [mul_assoc, ← pow_two, P.z_sq]

public theorem z_conj_r : P.z * P.r * P.z⁻¹ = P.r⁻¹ := by
  have hs : P.z * P.s * P.z⁻¹ = P.t := by simpa only [P.z_inv] using P.conj_s
  have ht : P.z * P.t * P.z⁻¹ = P.s := by simpa only [P.z_inv] using P.conj_t
  calc
    P.z * P.r * P.z⁻¹ = (P.z * P.s * P.z⁻¹) * (P.z * P.t * P.z⁻¹)⁻¹ := by dsimp [r]; group
    _ = P.t * P.s⁻¹ := by rw [hs, ht]
    _ = P.r⁻¹ := by simp [r]

public theorem d_conj_r : P.d * P.r * P.d⁻¹ = P.r⁻¹ := by
  have hcomm : Commute P.x₂ P.r :=
    ((Commute.refl P.s).mul_right (show Commute P.s P.t from P.commute).inv_right).pow_left _
  calc
    P.d * P.r * P.d⁻¹ = P.x₂ * (P.z * P.r * P.z⁻¹) * P.x₂⁻¹ := by simp only [d]; group
    _ = P.x₂ * P.r⁻¹ * P.x₂⁻¹ := by rw [P.z_conj_r]
    _ = P.r⁻¹ := by rw [hcomm.inv_right.eq]; group

end ABG.Wreathed.Presentation
