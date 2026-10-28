module
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.Centralizer
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints

/-!
# Center-fixing involutions on the extraspecial lift of a symmetric-three square

Let P be a normal extraspecial subgroup of order 27 mapping onto the
residual of S₃ × S₃ with kernel Z(P). If the whole action kernel
centralizes P, an element with involutory image acts involutively on P.
When it also centralizes the kernel, it fixes Z(P). Nontriviality of its
image excludes the identity automorphism, so the extraspecial involution
theorem forces inversion on P/Z(P), hence on the actual residual image.

Source: Aschbacher--Smith 15.2.5, printed p.1108, exclusion of the
extraspecial row in the full chosen-module comparison.
-/

public section
open Subgroup
namespace SymmetricThreeProductResidual
variable {E D : Type*} [Group E] [Finite E] [Group D] [Finite D]

omit [Finite D] in
/-- The original quotient image involution inverts the full residual. -/
theorem central_kernel_involution_inverts_extraspecial_image
    (f : E →* D) (e : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (P : Subgroup E) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (him : P.map f = pResidual 2 D)
    (hk : (f.domRestrict P).ker = center P)
    (hcentral : f.ker ≤ centralizer (P : Set E))
    (r : E) (hsq : (f r)^2 = 1) (hne : f r ≠ 1)
    (hr : r ∈ centralizer (f.ker : Set E)) :
    ∀ y ∈ pResidual 2 D, f r * y * (f r)⁻¹ = y⁻¹ := by
  let a : MulAut P := MulAut.conjNormal r
  have ha : Function.Involutive a := by
    intro x
    apply Subtype.ext
    have hr2 : r^2 ∈ f.ker := by change f (r^2)=1; rwa [map_pow]
    have hc := hcentral hr2 x x.property
    change r*(r*(x:E)*r⁻¹)*r⁻¹=(x:E)
    calc
      _ = r^2*(x:E)*(r^2)⁻¹ := by simp only [pow_two]; group
      _ = x := mul_inv_eq_iff_eq_mul.mpr hc.symm
  have hane : a ≠ 1 := by
    intro he
    apply hne
    apply eq_one_of_square_of_centralizes_residual e (f r) hsq
    intro y hy
    rw [←him] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    have hh : r*x*r⁻¹=x := congrArg (P.subtype) (show a ⟨x,hx⟩ = ⟨x,hx⟩ from DFunLike.congr_fun he ⟨x,hx⟩)
    exact (map_mul f r x).symm.trans
      ((congrArg f (mul_inv_eq_iff_eq_mul.mp hh)).trans (map_mul f x r))
  have hfix : ∀ z ∈ center P, a z=z := by
    intro z hz
    have hzker : z ∈ (f.domRestrict P).ker := hk.symm ▸ hz
    have hzk : (z:E) ∈ f.ker := hzker
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hr z hzk).symm
  have hinv := (IsExtraspecial.exponent_and_frattini_inversion_of_card27 hP a ha hane hfix).2
  intro y hy
  rw [←him] at hy
  obtain ⟨x,hx,rfl⟩ := hy
  have hh := hinv ⟨x,hx⟩
  have hz : a ⟨x,hx⟩ / (⟨x,hx⟩ : P)⁻¹ ∈ (f.domRestrict P).ker := by
    rw [hk,←IsExtraspecial.frattini_eq_center_three]
    exact QuotientGroup.eq_iff_div_mem.mp hh
  change f ((r*x*r⁻¹) / x⁻¹) = 1 at hz
  simpa only [map_div,map_mul,map_inv,div_eq_one] using hz

end SymmetricThreeProductResidual
