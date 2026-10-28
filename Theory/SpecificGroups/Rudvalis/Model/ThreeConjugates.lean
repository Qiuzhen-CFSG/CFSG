module

public import Theory.SpecificGroups.Rudvalis.Model.ThreeConjugates.Representatives
public import Theory.SpecificGroups.Rudvalis.Model.ThreeConjugates.Fusion
import Mathlib.Tactic.Group

/-!
# Three conjugates of every Rudvalis involution generate the group

The literal ATLAS generators are recovered from three conjugates of `a`
and, separately, from three conjugates of `b²`. The proved coverage of all
involutions by these two representatives transports generation to any input.
No simplicity, perfectness, group-family tag, centralizer table or automorphism
premise is needed.

This proves the Rudvalis involution bound in Revin–Zavarnitsine,
*Conjugate generation of sporadic almost simple groups*, arXiv:2505.05173v2,
Theorem 1, citing Di Martino–Pellegrini–Zalesskii, Theorem 3.1.
The Chapter K degree-window consumer passes `three_involution_conjugates`
as the final argument of `Theory.GroupTheory.threeConjugateAutomorphisms_of_inner`;
that consumer separately supplies injectivity and involutory innerness.
-/

namespace Rudvalis
open Subgroup

private theorem three_generate_of_isConj (t s : Model) (ht : IsConj t s)
    (hs : zpowers s ⊔ zpowers ((a*b)⁻¹*s*(a*b)) ⊔
      zpowers (((a*b)^2)⁻¹*s*((a*b)^2)) = ⊤) :
    ∃ g h : Model,
      zpowers t ⊔ zpowers (g*t*g⁻¹) ⊔ zpowers (h*t*h⁻¹) = ⊤ := by
  obtain ⟨u, hu⟩ := isConj_iff.mp ht
  refine ⟨u⁻¹*(a*b)⁻¹*u, u⁻¹*((a*b)^2)⁻¹*u, ?_⟩
  have he := congrArg (fun H : Subgroup Model => H.map (MulAut.conj u⁻¹).toMonoidHom) hs
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, map_top_of_surjective _ (MulAut.conj u⁻¹).surjective] at he
  have h₀ : u⁻¹*s*u = t := by rw [← hu]; group
  have h₁ : u⁻¹*((a*b)⁻¹*s*(a*b))*u =
      (u⁻¹*(a*b)⁻¹*u)*t*(u⁻¹*(a*b)⁻¹*u)⁻¹ := by rw [← hu]; group
  have h₂ : u⁻¹*(((a*b)^2)⁻¹*s*((a*b)^2))*u =
      (u⁻¹*((a*b)^2)⁻¹*u)*t*(u⁻¹*((a*b)^2)⁻¹*u)⁻¹ := by rw [← hu]; group
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, h₀, h₁, h₂] using he

/-- Every actual Rudvalis involution has three conjugates generating the whole model. -/
public theorem three_involution_conjugates (t : Model) (ht : orderOf t = 2) :
    ∃ g h : Model,
      zpowers t ⊔ zpowers (g*t*g⁻¹) ⊔ zpowers (h*t*h⁻¹) = ⊤ := by
  rcases involution_isConj_a_or_b_sq t ht with h | h
  · exact three_generate_of_isConj t a h standard_three_generate
  · exact three_generate_of_isConj t (b^2) h square_three_generate

end Rudvalis
