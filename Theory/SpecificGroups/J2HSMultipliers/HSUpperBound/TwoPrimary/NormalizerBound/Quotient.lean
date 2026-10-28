module

public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.Reduction
public import Theory.GroupTheory.Commutator.CentralDihedralSylow
public import Theory.GroupTheory.Commutator.CentralDihedralExponentFour
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels.SylowModels

/-!
# Eliminating a split-involution cover of the binary linear quotient

A finite perfect central two-cover of SL₃(2) has kernel of order at most
two, by its dihedral Sylow subgroup. If one nonidentity involution lifts
to an involution, conjugacy supplies such a lift for every involution.
For a kernel of order two, every lift of an involution then squares to one.
The covering Sylow subgroup consequently has exponent four, so the central
dihedral transfer calculation makes its perfect central kernel trivial.

This proves the quotient-cover step used in `NormalizerBound`, for arbitrary
central two-kernels, without assuming that their order is two. The matrix
Sylow model and involution conjugacy refer to the actual PSL₃(2) carrier.
Source: Aschbacher–Smith I.1.1–I.1.3(1), p.407, and the HS argument in
I.2.2(5), p.412. The latter's order-two assumption is discharged here by the
independent dihedral bound before applying the exponent-four result.
-/

public section

open Subgroup
namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound

variable {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]

/-- A nontrivial involution lift kills the entire perfect central two-kernel. -/
theorem quotient_kernel_trivial
    (f : H →* Matrix.PSL3Two.PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center H) (hp : IsPGroup 2 f.ker)
    (hlift : ∃ x : H, f x ≠ 1 ∧ x ^ 2 = 1) : f.ker = ⊥ := by
  let S : Sylow 2 H := default
  obtain ⟨e⟩ := Matrix.PSL3Four.FixedResidualKernels.psl3Two_sylow_dihedral
    (S.mapSurjective hf)
  have hbound : Nat.card f.ker ≤ 2 := by
    simpa only [Group.IsPerfect.commutator_eq_top, inf_top_eq] using
      CentralExtension.card_ker_inf_commutator_le_two_of_dihedral_sylow f hf hc hp S e
  by_contra hne
  let : Nontrivial f.ker := (nontrivial_iff_ne_bot _).mpr hne
  have hcard : Nat.card f.ker = 2 := by have := Finite.one_lt_card (α := f.ker); omega
  have hker2 (z : H) (hz : z ∈ f.ker) : z ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := (⟨z, hz⟩ : f.ker))
    rw [hcard] at h
    exact congrArg Subtype.val h
  obtain ⟨x, hx, hx2⟩ := hlift
  have hxord : orderOf (f x) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, hx2, map_one]) hx
  have hall (a : Matrix.PSL3Two.PSL) (ha : a ^ 2 = 1) :
      ∃ y : H, f y = a ∧ y ^ 2 = 1 := by
    by_cases ha1 : a = 1
    · exact ⟨1, by simpa using ha1.symm, one_pow 2⟩
    obtain ⟨b, hb⟩ := Matrix.PSL3Two.involutions_conjugate (f x) a hxord
      (orderOf_eq_prime ha ha1)
    obtain ⟨b, rfl⟩ := hf b
    refine ⟨b * x * b⁻¹, ?_, ?_⟩
    · simpa only [map_mul, map_inv, MulAut.conj_apply] using hb
    · calc
        (b * x * b⁻¹) ^ 2 = b * x ^ 2 * b⁻¹ := by simp only [pow_two]; group
        _ = 1 := by rw [hx2]; group
  have hsquare (y : H) (hy : f y ^ 2 = 1) : y ^ 2 = 1 := by
    obtain ⟨a, ha, ha2⟩ := hall (f y) hy
    have hk : y * a⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ha, mul_inv_cancel]
    have hcomm : Commute (y * a⁻¹) a := (mem_center_iff.mp (hc hk) a).symm
    calc
      y ^ 2 = ((y * a⁻¹) * a) ^ 2 := by rw [inv_mul_cancel_right]
      _ = (y * a⁻¹) ^ 2 * a ^ 2 := hcomm.mul_pow 2
      _ = 1 := by rw [hker2 _ hk, ha2, one_mul]
  let q : S →* S.mapSurjective hf := f.subgroupMap (S : Subgroup H)
  have hfour (y : S) : y ^ 4 = 1 := by
    have he : e (q y) ^ 4 = 1 := by
      exact (by decide : ∀ a : DihedralGroup 4, a ^ 4 = 1) _
    have he' : (q y) ^ 4 = 1 := e.injective (by
      rw [map_pow, map_one]; exact he)
    have hm : f (y : H) ^ 4 = 1 := congrArg Subtype.val he'
    apply Subtype.ext
    change (y : H) ^ 4 = 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    apply hsquare
    simpa only [map_pow, ← pow_mul] using hm
  have hbot := CentralExtension.ker_inf_commutator_eq_bot_of_dihedral_four_sylow
    f hf hc hcard S e hfour
  exact hne (by simpa only [Group.IsPerfect.commutator_eq_top, inf_top_eq] using hbot)

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
