module
public import Theory.Representation.ProductIsotypic
public import Theory.Representation.IsotypicCopies
public import Theory.Representation.FiniteSchurIntertwiner
public import Theory.Representation.SubrepresentationLattice
public import Theory.Representation.Quotient

/-!
# Multiplicity forced by a commuting nonabelian action

An irreducible finite-field representation of a product restricts to copies
of one irreducible module on the first factor. If its second factor acts
noncommutatively, there must be more than one copy: multiplicity zero gives
a zero module, while multiplicity one puts the second factor in the finite
Schur field, whose endomorphisms commute by Wedderburn's theorem.

The repeated coordinates and their multiplicity are constructed together.
The literal odd-prime consumer is Chapter13's FFContradiction.RepeatedProduct.
Source: Aschbacher--Smith 13.1.9, printed p.871, preceding (*).
-/

public noncomputable section
namespace Representation.ProductIsotypic
variable {k G H V I : Type*} [Field k] [Finite k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup I] [Module k I] [FiniteDimensional k I]

private theorem right_commutes_of_left_irreducible
    (ρ : Representation k (G × H) V) [IsIrreducible (left ρ)] (a b : H) :
    ρ (1,a*b) = ρ (1,b*a) := by
  let f (h : H) : (left ρ).IntertwiningMap (left ρ) := {
    toLinearMap := ρ (1,h)
    isIntertwining' g := by
      change ρ (1,h) * ρ (g,1) = ρ (g,1) * ρ (1,h)
      rw [←map_mul,←map_mul]
      simp }
  apply LinearMap.ext
  intro v
  have he := FiniteSchurIntertwiner.commute (left ρ) (f a) (f b) v
  change ρ (1,a) (ρ (1,b) v) = ρ (1,b) (ρ (1,a) v) at he
  simpa only [←Module.End.mul_apply,←map_mul,Prod.mk_mul_mk,one_mul] using he

omit [FiniteDimensional k I] in
/-- Noncommuting action of the second factor forces multiplicity greater than
one in any isotypic decomposition of the first-factor restriction. -/
theorem copies_multiple_of_noncommuting
    (ρ : Representation k (G × H) V)
    (hn : ∃ a b : H, ρ (1,a*b) ≠ ρ (1,b*a))
    (σ : Representation k G I) [IsIrreducible σ] {r : ℕ}
    (e : V ≃ₗ[k] (Fin r → I))
    (he : ∀ g v, e (ρ (g,1) v) = fun i => σ g (e v i)) : 1 < r := by
  by_contra! hr
  interval_cases r
  · let : Subsingleton V := Function.Injective.subsingleton e.injective
    obtain ⟨a,b,hab⟩ := hn
    exact hab (Subsingleton.elim _ _)
  · let a : V ≃ₗ[k] I := e.trans (LinearEquiv.funUnique (Fin 1) k I)
    let q : (left ρ).Equiv σ := Representation.Equiv.mk a (by
      intro g
      apply LinearMap.ext
      intro v
      exact congrFun (he g v) 0)
    let : IsIrreducible (left ρ) :=
      (RepEquiv.ofRepresentationEquiv q).irreducible_of_euqiv inferInstance
    obtain ⟨a,b,hab⟩ := hn
    exact hab (right_commutes_of_left_irreducible ρ a b)

/-- Clifford's homogeneous restriction provides the actual repeated
coordinates; the other factor's nonabelian action proves r > 1. -/
theorem exists_multiple_copy_coordinates
    (ρ : Representation k (G × H) V) [IsIrreducible ρ]
    (hn : ∃ a b : H, ρ (1,a*b) ≠ ρ (1,b*a)) :
    ∃ S : Subrepresentation (left ρ), IsIrreducible S.toRepresentation ∧
      ∃ r : ℕ, 1 < r ∧ ∃ e : V ≃ₗ[k] (Fin r → S.toSubmodule),
        ∀ g v, e (ρ (g,1) v) = fun i => S.toRepresentation g (e v i) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨S,hS⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional (left ρ)
  let : IsIrreducible S.toRepresentation := hS
  let : Nontrivial S.toSubmodule := Subrepresentation.irreducible_module_nontrivial S.toRepresentation
  let f : S.toRepresentation.IntertwiningMap (left ρ) :=
    .mk S.toSubmodule.subtype (by intro g; ext v; rfl)
  have hf : f ≠ 0 := by
    obtain ⟨v,hv⟩ := exists_ne (0 : S.toSubmodule)
    intro he
    exact hv (Subtype.ext (congrArg (fun f : S.toRepresentation.IntertwiningMap (left ρ) => f v) he))
  obtain ⟨r,e,he⟩ := exists_copy_coordinates ρ S.toRepresentation f hf
  exact ⟨S,hS,r,copies_multiple_of_noncommuting ρ hn S.toRepresentation e he,e,he⟩
end Representation.ProductIsotypic
