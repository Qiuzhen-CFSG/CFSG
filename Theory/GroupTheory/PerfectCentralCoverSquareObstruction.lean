module

public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# A square obstruction to splitting a central double extension

For a central kernel of exponent two, all lifts of one element have equal
squares. If the base is perfect and the kernel consists of `1` and a square
`z` with `z² = 1`, the derived subgroup contains both the kernel and a lift
of every base element. Thus the extension itself is perfect.

A nontrivial perfect central extension then detects a nontrivial universal
kernel by lifting the universal cover. This supplies the abstract step from
the marked Conway square to the nontrivial G₂(4) cover in Aschbacher–Smith,
I.2.2(5), printed p.411 (PDF p.422); the actual application is in
`Theory.SpecificGroups.G2.FourNontrivialCover`.
-/

public section

namespace PerfectCentralCovering

open Subgroup

variable {E B : Type*} [Group E] [Group B]

/-- Two lifts of the same element have equal squares when the central kernel
has exponent two. -/
theorem square_eq_of_map_eq_of_kernel_exponent_two (f : E →* B)
    (hc : f.ker ≤ center E) (h2 : ∀ k ∈ f.ker, k ^ 2 = 1)
    {x y : E} (hxy : f x = f y) : x ^ 2 = y ^ 2 := by
  have hk : x⁻¹ * y ∈ f.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hc' : Commute x (x⁻¹ * y) := mem_center_iff.mp (hc hk) x
  calc
    x ^ 2 = x ^ 2 * (x⁻¹ * y) ^ 2 := by rw [h2 _ hk, mul_one]
    _ = (x * (x⁻¹ * y)) ^ 2 := (hc'.mul_pow 2).symm
    _ = y ^ 2 := by simp

/-- A central extension of a perfect group with kernel contained in `{1, z}`
is perfect if `z` is an involution and a square. The derived subgroup maps onto
the base; equality of squares puts `z` in that subgroup too. -/
theorem isPerfect_of_central_binary_kernel_of_square [Group.IsPerfect B]
    (f : E →* B) (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (z : E) (hz2 : z ^ 2 = 1) (hk : ∀ k ∈ f.ker, k = 1 ∨ k = z)
    (x : E) (hx : x ^ 2 = z) : Group.IsPerfect E := by
  have hmap : (commutator E).map f = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  have hd (b : B) : ∃ d ∈ commutator E, f d = b := by
    have hb : b ∈ (commutator E).map f := by rw [hmap]; trivial
    exact hb
  have h2 : ∀ k ∈ f.ker, k ^ 2 = 1 := by
    intro k h
    rcases hk k h with rfl | rfl
    · exact one_pow 2
    · exact hz2
  have hzD : z ∈ commutator E := by
    obtain ⟨d, hd, hdx⟩ := hd (f x)
    rw [← hx, square_eq_of_map_eq_of_kernel_exponent_two f hc h2 hdx.symm]
    exact (commutator E).pow_mem hd 2
  refine ⟨top_unique ?_⟩
  intro a _
  obtain ⟨d, hd, hda⟩ := hd (f a)
  have hka : a * d⁻¹ ∈ f.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, hda, mul_inv_cancel]
  have hkD : a * d⁻¹ ∈ commutator E := by
    rcases hk _ hka with h | h
    · rw [h]; exact (commutator E).one_mem
    · rwa [h]
  simpa only [inv_mul_cancel_right] using (commutator E).mul_mem hkD hd

/-- A perfect central extension with nontrivial kernel proves nontriviality
of the kernel of the concrete free-central universal cover. -/
theorem Cover.universalKernel_ne_bot_of_ker_ne_bot
    [Group.IsPerfect B] (f : Cover E B) (hne : f.toMonoidHom.ker ≠ ⊥) :
    (universalProjection B).ker ≠ ⊥ := by
  intro htrivial
  let : Group.IsPerfect E := f.isPerfect
  obtain ⟨a, ha, _⟩ := universalProjection_existsUnique_lift
    f.toMonoidHom f.surjective f.ker_le_center
  have has : Function.Surjective a :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect f.toMonoidHom a
      (ha ▸ universalProjection_surjective B) f.ker_le_center
  apply hne
  apply f.toMonoidHom.ker_eq_bot_iff.mpr
  intro x y hxy
  obtain ⟨x, rfl⟩ := has x
  obtain ⟨y, rfl⟩ := has y
  apply congrArg a
  apply (universalProjection B).ker_eq_bot_iff.mp htrivial
  simpa only [← ha, MonoidHom.comp_apply] using hxy

end PerfectCentralCovering

