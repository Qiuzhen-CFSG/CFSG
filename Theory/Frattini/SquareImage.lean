module

public import Theory.Frattini.PGroup

/-!
# Frattini subgroups and exponent-two images

Every homomorphism from a finite group with exponent-two image kills the
Frattini subgroup. Its image is elementary abelian, so has trivial Frattini
subgroup; apply Frattini functoriality to the surjection onto that image.
No two-group assumption on the domain is required.

Source application: Aschbacher–Smith, proof of 2.5.21, printed p.567,
the marked Frattini element in the mixed-action calculation.
-/

public section

open Subgroup
namespace Theory.GroupTheory

/-- Every map with exponent-two image kills the Frattini subgroup. -/
theorem frattini_le_ker_of_square_image {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (hs : ∀ a : A, f a ^ 2 = 1) : frattini A ≤ f.ker := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hs' (a : f.range) : a ^ 2 = 1 := by
    obtain ⟨x, hx⟩ := a.property
    exact Subtype.ext (by simpa only [Subgroup.coe_pow, Subgroup.coe_one, hx] using hs x)
  have hi (a : f.range) : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs' a)
  let : IsElementaryAbelian 2 f.range :=
    { toIsMulCommutative := IsMulCommutative.of_comm (fun a b => by
        calc
          a * b = (a * b)⁻¹ := (hi _).symm
          _ = b * a := by rw [_root_.mul_inv_rev, hi, hi])
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs' }
  let : Fact (IsPGroup 2 f.range) := ⟨IsElementaryAbelian.isPGroup 2 f.range⟩
  have h := frattini_le_comap_frattini_of_surjective f.rangeRestrict_surjective
  rw [frattini_eq_bot_of_isElementaryAbelian (R := f.range) (p := 2)] at h
  intro a ha
  have hh : f.rangeRestrict a ∈ (⊥ : Subgroup f.range) := h ha
  exact congrArg Subtype.val (mem_bot.mp hh)

end Theory.GroupTheory

end
