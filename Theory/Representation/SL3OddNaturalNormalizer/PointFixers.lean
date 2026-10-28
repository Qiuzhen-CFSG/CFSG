module

public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Mathlib.Algebra.CharP.Two

/-!
# Pointwise fixers in the natural SL₃ normalizer

A binary actor normalizing the natural SL₃ layer is semilinear. If it fixes
a nonzero F-subspace pointwise, its coefficient automorphism fixes every
scalar, so the actor is F-linear. In characteristic two a square-one actor
then has determinant one. The resulting special-linear matrix acts by the
original representation, in its original coordinates.

This supplies the linear-image step in Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript of 1 March 2004, G.2.5(1), printed
p.335, using the normalizer argument of G.2.3 on p.333. No restriction on
the binary field degree is needed.
-/

public section
namespace Representation.SL3OddNaturalNormalizer
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H]

/-- Pointwise fixation of a nonzero F-subspace eliminates the coefficient
automorphism of an actor normalizing the natural SL₃ layer. -/
theorem linear_of_fixes_submodule (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (ρ : Representation (ZMod 2) H (Fin 3 → F))
    (hnat : ∀ (g : L) (v : Fin 3 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (P : Submodule F (Fin 3 → F)) (hP : P ≠ ⊥)
    (a : H) (hfix : ∀ v ∈ P, ρ a v = v) :
    ∀ (c : F) (v : Fin 3 → F), ρ a (c • v) = c • ρ a v := by
  obtain ⟨σ, hσ⟩ := normalizer_semilinear L e ρ hnat a
  obtain ⟨w, hwP, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hcoeff (c : F) : σ c = c := by
    have he := hσ c w
    rw [hfix w hwP, hfix (c • w) (P.smul_mem c hwP)] at he
    exact (smul_left_injective F hw) he.symm
  intro c v
  rw [hσ, hcoeff]

/-- A square-one actor fixing a nonzero F-subspace pointwise acts by an
actual determinant-one matrix, including when the field is F₂. -/
theorem exists_specialLinear_of_square_one_of_fixes_submodule [CharP F 2]
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (ρ : Representation (ZMod 2) H (Fin 3 → F))
    (hnat : ∀ (g : L) (v : Fin 3 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (P : Submodule F (Fin 3 → F)) (hP : P ≠ ⊥)
    (a : H) (ha : a ^ 2 = 1) (hfix : ∀ v ∈ P, ρ a v = v) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 3) F, ∀ v, ρ a v = s.val.mulVec v := by
  let t : Module.End F (Fin 3 → F) :=
    { toFun := ρ a
      map_add' := (ρ a).map_add
      map_smul' := linear_of_fixes_submodule L e ρ hnat P hP a hfix }
  have ht : t ^ 2 = 1 := by
    apply LinearMap.ext
    intro v
    change ρ a (ρ a v) = v
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ha, map_one]
    rfl
  have hd : (LinearMap.toMatrix' t).det = 1 := by
    have hm : LinearMap.toMatrix' t * LinearMap.toMatrix' t = 1 := by
      rw [← LinearMap.toMatrix'_mul, ← pow_two, ht, LinearMap.toMatrix'_one]
    have hd2 : (LinearMap.toMatrix' t).det ^ 2 = 1 := by
      rw [pow_two, ← Matrix.det_mul, hm, Matrix.det_one]
    rcases sq_eq_one_iff.mp hd2 with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  exact ⟨⟨LinearMap.toMatrix' t, hd⟩, fun v => (LinearMap.toMatrix'_mulVec t v).symm⟩

end Representation.SL3OddNaturalNormalizer
