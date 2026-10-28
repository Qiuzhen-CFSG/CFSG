module
public import Theory.Representation.CubicClifford.IndexTwoRestriction

/-!
# Literal exchange of index-two Clifford constituents

An index-two subgroup contains the square of the specified exchanger. Its
constituent therefore has the same image under that element and its inverse.
The inverse-image constituent maps back to the first. The restriction
intertwiner and disjointness show that these actual subspaces are complementary.

This keeps the exchange action, rather than only the abstract isomorphism
types, in the partner-chief recognition of Aschbacher–Smith 15.2.27(2), p.1119.
Source: Clifford theory, Isaacs, Theorem 6.5.
-/

public section
open Subgroup Representation
namespace Representation.CubicClifford.Inertia
variable {F G W : Type*} [Field F] [Group G]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]

omit [FiniteDimensional F W] in
/-- The conjugate summand in the index-two restriction is the actual image
under the specified exchanger, in either orientation. -/
theorem constituent_map_exchange (ρ : Representation F G W)
    (I : Subgroup G) [I.Normal] (hi : I.index = 2)
    (C : Subrepresentation (ρ.comp I.subtype)) (t : G) :
    C.toSubmodule.map (ρ t) = C.toSubmodule.map (ρ t⁻¹) ∧
      (C.toSubmodule.map (ρ t⁻¹)).map (ρ t) = C.toSubmodule := by
  constructor
  · apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      refine ⟨ρ (t ^ 2) w,C.apply_mem_toSubmodule ⟨t ^ 2,I.sq_mem_of_index_two hi t⟩ hw,?_⟩
      simp only [←Module.End.mul_apply,←map_mul,pow_two,inv_mul_cancel_left]
    · rintro v ⟨w,hw,rfl⟩
      refine ⟨ρ ((t⁻¹) ^ 2) w,
        C.apply_mem_toSubmodule ⟨(t⁻¹) ^ 2,I.sq_mem_of_index_two hi t⁻¹⟩ hw,?_⟩
      simp only [←Module.End.mul_apply,←map_mul,pow_two,mul_inv_cancel_left]
  · apply le_antisymm
    · rintro v ⟨w,⟨u,hu,rfl⟩,rfl⟩
      have hcancel : ρ t (ρ t⁻¹ u) = u := by
        simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,
          Module.End.one_apply]
      rw [hcancel]
      exact hu
    · intro v hv
      refine ⟨ρ t⁻¹ v,⟨v,hv,rfl⟩,?_⟩
      simp only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,
        Module.End.one_apply]

/-- Disjoint conjugate constituents and the restriction equivalence give
complementarity of the literal subspaces, retaining the specified exchanger. -/
theorem constituent_isCompl (ρ : Representation F G W)
    (I : Subgroup G) [I.Normal]
    (C : Subrepresentation (ρ.comp I.subtype)) (t : G)
    (hd : Disjoint C.toSubmodule (C.toSubmodule.map (ρ t⁻¹)))
    (e : Representation.Equiv (ρ.comp I.subtype)
      (C.toRepresentation.prod (conjugateRep C.toRepresentation t))) :
    IsCompl C.toSubmodule (C.toSubmodule.map (ρ t⁻¹)) := by
  refine ⟨hd,codisjoint_iff.mpr ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have hdim : Module.finrank F (C.toSubmodule.map (ρ t⁻¹)) =
      Module.finrank F C.toSubmodule :=
    (LinearEquiv.ofBijective (ρ t⁻¹)
      (Representation.apply_bijective ρ t⁻¹)).finrank_map_eq C.toSubmodule
  have he := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at he
  have hh := C.toSubmodule.finrank_sup_add_finrank_inf_eq
    (C.toSubmodule.map (ρ t⁻¹))
  rw [hd.eq_bot,finrank_bot,add_zero,hdim] at hh
  exact hh.trans he.symm
end Representation.CubicClifford.Inertia
