module

public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Theory.GroupTheory.ScalarRootResidual

/-!
# Torus generation of the degree-three unipotent group

The (0,1) and (1,2) roots generate the literal upper-unitriangular model;
their commutators supply its central (0,2) root. Consequently a p-element
acting nontrivially by scalars on both simple roots puts the whole image
inside O^{p′}, including the center fixed by the torus.

Source: the inner-action step of Aschbacher–Smith 16.4.8, combined
manuscript of 1 March 2004, printed p.1188. The actual torus and centralizer
identifications are separate matrix calculations.
-/

@[expose] public section
open Subgroup

namespace Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F]

/-- The (0,1) root in upper-unitriangular coordinates. -/
def firstRoot : Multiplicative F →* U F where
  toFun x := ⟨x.toAdd, 0, 0⟩
  map_one' := rfl
  map_mul' x y := by apply U.ext <;> simp

/-- The (1,2) root in upper-unitriangular coordinates. -/
def secondRoot : Multiplicative F →* U F where
  toFun x := ⟨0, x.toAdd, 0⟩
  map_one' := rfl
  map_mul' x y := by apply U.ext <;> simp

/-- The two simple roots generate all three unitriangular coordinates. -/
theorem range_le_of_roots {D : Type*} [Group D] (f : U F →* D)
    (N : Subgroup D)
    (hfirst : (f.comp (firstRoot F)).range ≤ N)
    (hsecond : (f.comp (secondRoot F)).range ≤ N) : f.range ≤ N := by
  have hx (x : F) : f (⟨x, 0, 0⟩ : U F) ∈ N :=
    hfirst ⟨Multiplicative.ofAdd x, rfl⟩
  have hy (y : F) : f (⟨0, y, 0⟩ : U F) ∈ N :=
    hsecond ⟨Multiplicative.ofAdd y, rfl⟩
  have hc (c : F) : f (⟨0, 0, c⟩ : U F) ∈ N := by
    have he : (⟨c,0,0⟩ : U F) * ⟨0,1,0⟩ * (⟨c,0,0⟩ : U F)⁻¹ *
        (⟨0,1,0⟩ : U F)⁻¹ = ⟨0,0,c⟩ := by
      apply U.ext <;> simp [mul_x, mul_y, mul_c, Inv.inv]
    rw [← he, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact N.mul_mem (N.mul_mem (N.mul_mem (hx c) (hy 1)) (N.inv_mem (hx c)))
      (N.inv_mem (hy 1))
  rintro _ ⟨u, rfl⟩
  have he : (⟨u.x,0,0⟩ : U F) * ⟨0,u.y,0⟩ * ⟨0,0,u.c-u.x*u.y⟩ = u := by
    apply U.ext <;> simp
  rw [← he, map_mul, map_mul]
  exact N.mul_mem (N.mul_mem (hx u.x) (hy u.y)) (hc _)
/-- A p-element acting nontrivially by scalars on both simple roots
places the whole unipotent image in O^{p′}. The central root is obtained
by their commutator, even though the torus may fix it pointwise. -/
theorem range_le_primeToResidual_of_scalar_roots {D : Type*} [Group D]
    (p : ℕ) (f : U F →* D) (t : D) {k : ℕ} (ht : t ^ (p ^ k) = 1)
    (a b : F) (ha : a ≠ 1) (hb : b ≠ 1)
    (hfirst : ∀ x : F, t * f (firstRoot F (Multiplicative.ofAdd x)) * t⁻¹ =
      f (firstRoot F (Multiplicative.ofAdd (a * x))))
    (hsecond : ∀ x : F, t * f (secondRoot F (Multiplicative.ofAdd x)) * t⁻¹ =
      f (secondRoot F (Multiplicative.ofAdd (b * x)))) :
    f.range ≤ primeToResidual p D :=
  range_le_of_roots F f _
    (scalar_root_le_primeToResidual p (f.comp (firstRoot F)) t ht a ha hfirst)
    (scalar_root_le_primeToResidual p (f.comp (secondRoot F)) t ht b hb hsecond)

end Matrix.PSL3Even.UnipotentGeometry
