module
public import Theory.LinearAlgebra.RankOneInvariantPair
public import Mathlib.LinearAlgebra.Projection

/-!
# Rank-one operators and interchanged complementary summands

An operator sending a subspace into a disjoint subspace has displacement rank
at least the dimension of that subspace. A rank-one operator preserving both
complementary summands must be the identity if it commutes with their
interchange: it vanishes on one summand by rank one, and hence on the other
by commutation. These facts exclude the imprimitive alternative in the
symplectic-four pair of Aschbacher--Smith E.2.7, printed p.220.
-/

public section
namespace LinearEquiv
variable {k X : Type*} [Field k] [AddCommGroup X] [Module k X]
  [FiniteDimensional k X]

/-- Moving a subspace into a disjoint subspace gives an injective displacement. -/
theorem finrank_le_displacement_of_disjoint_image (e : X ≃ₗ[k] X)
    (U W : Submodule k X) (hd : Disjoint U W)
    (he : ∀ x ∈ U, e x ∈ W) :
    Module.finrank k U ≤ Module.finrank k (LinearMap.range (e.toLinearMap - LinearMap.id)) := by
  let δ := e.toLinearMap - LinearMap.id
  let f : U →ₗ[k] LinearMap.range δ :=
    (δ.comp U.subtype).codRestrict _ (fun x => LinearMap.mem_range_self δ x)
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hh : e x - x = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
  have hxy : e x = x := sub_eq_zero.mp hh
  apply Subtype.ext
  exact Submodule.disjoint_def.mp hd x x.property (hxy ▸ he x x.property)

/-- A rank-one operator cannot act identically on just one of two interchanged summands. -/
theorem eq_one_of_rank_one_commute_swap (e t : X ≃ₗ[k] X)
    (U W : Submodule k X) (hc : IsCompl U W)
    (hr : Module.finrank k (LinearMap.range (e.toLinearMap - LinearMap.id)) ≤ 1)
    (hU : ∀ x ∈ U, e x ∈ U) (hW : ∀ x ∈ W, e x ∈ W)
    (htU : ∀ x ∈ U, t x ∈ W) (htW : ∀ x ∈ W, t x ∈ U)
    (hcomm : ∀ x, e (t x) = t (e x)) : e = 1 := by
  let δ := e.toLinearMap - LinearMap.id
  have hz := LinearMap.invariant_disjoint_pair_rank_one δ hr U W hc.disjoint
    (by rintro _ ⟨x,hx,rfl⟩; exact U.sub_mem (hU x hx) hx)
    (by rintro _ ⟨x,hx,rfl⟩; exact W.sub_mem (hW x hx) hx)
  have hfix : (∀ x ∈ U, e x=x) ∧ (∀ x ∈ W, e x=x) := by
    rcases hz with hz | hz
    · have hfixU : ∀ x ∈ U, e x=x := fun x hx => sub_eq_zero.mp (hz hx)
      refine ⟨hfixU,?_⟩
      intro x hx
      apply t.injective
      rw [←hcomm,hfixU (t x) (htW x hx)]
    · have hfixW : ∀ x ∈ W, e x=x := fun x hx => sub_eq_zero.mp (hz hx)
      refine ⟨?_,hfixW⟩
      intro x hx
      apply t.injective
      rw [←hcomm,hfixW (t x) (htU x hx)]
  ext x
  obtain ⟨u,w,hw,_⟩ := Submodule.existsUnique_add_of_isCompl hc x
  rw [←hw,map_add,hfix.1 u u.property,hfix.2 w w.property]
  rfl

end LinearEquiv
