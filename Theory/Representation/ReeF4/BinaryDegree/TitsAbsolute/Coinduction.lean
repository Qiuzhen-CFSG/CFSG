module

public import Theory.AlgebraicGroup.Representations.Coinduction.RightQuotient
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Passing a small-degree catalogue to a subgroup

Let H have index at most two in a finite group G. Suppose every irreducible
G-module of degree below 2b is trivial or has degree b, and every irreducible
G-module of degree b remains irreducible on H. Then every nontrivial
irreducible H-module has degree at least b.

Coinduction has dimension [G : H] times the original dimension. Evaluation
at the identity is nonzero on every nonzero G-submodule of coinduction, so
it surjects onto the original irreducible H-module. A simple G-submodule of
coinduction therefore gives either a trivial H-module or, using the stated
restriction hypothesis, an isomorphism of H-modules of degree b.

This is a direct coinduction/Frobenius reciprocity argument, valid in any
characteristic. It supplies the subgroup step for the Tits endpoint of
Aschbacher--Smith, *The Classification of Quasithin Groups*, printed p.356
(PDF p.367), where the full binary Ree group must be distinguished from its
derived subgroup. The concrete catalogue and restriction facts are separate
inputs, not asserted here.
-/

public section

open Representation
namespace ReeF4.BinaryDegree.TitsAbsolute

universe u v w
variable {F : Type u} {G : Type w} {W : Type v} [Field F] [Group G] [Finite G]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  (H : Subgroup G) (σ : Representation F H W)

private noncomputable def evalOne (U : Subrepresentation (coind H.subtype σ)) :
    Representation.IntertwiningMap (U.toRepresentation.comp H.subtype) σ where
  toLinearMap := (LinearMap.proj 1).comp
    ((coindV H.subtype σ).subtype.comp U.toSubmodule.subtype)
  isIntertwining' h := by
    ext f
    change f.val.val (1 * (h : G)) = σ h (f.val.val 1)
    simpa using f.val.property h 1

omit [Finite G] [FiniteDimensional F W] in
private theorem evalOne_ne_zero (U : Subrepresentation (coind H.subtype σ)) (hU : U ≠ ⊥) :
    evalOne H σ U ≠ 0 := by
  intro he
  apply hU
  apply Subrepresentation.toSubmodule_injective
  apply eq_bot_iff.mpr
  intro f hf
  change f = 0
  apply Subtype.ext
  funext g
  let z : U.toSubmodule := ⟨coind H.subtype σ g f, U.apply_mem_toSubmodule g hf⟩
  have hz := congrArg (fun p => p z) he
  change f.val (1 * g) = 0 at hz
  simpa using hz

private theorem coind_finrank :
    Module.finrank F (coindV H.subtype σ) = H.index * Module.finrank F W := by
  classical
  let Q := Quotient (QuotientGroup.rightRel H)
  let : Fintype Q := Fintype.ofFinite Q
  rw [LinearEquiv.finrank_eq
    (Theory.AlgebraicGroup.Representation.coindVEquivRightQuotientPi H (Rep.of σ))]
  rw [Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  rw [H.index_eq_card, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_small_ambient [σ.IsIrreducible] :
    ∃ U : Subrepresentation (coind H.subtype σ),
      Representation.IsIrreducible (k := F) (G := G) (V := U.toSubmodule)
        U.toRepresentation ∧
      Function.Surjective (evalOne H σ U) ∧
      Module.finrank F U.toSubmodule ≤ H.index * Module.finrank F W := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  let e := Theory.AlgebraicGroup.Representation.coindVEquivRightQuotientPi H (Rep.of σ)
  let : Nontrivial (Rep.of σ) := ‹Nontrivial W›
  let : Nonempty (Quotient (QuotientGroup.rightRel H)) := ⟨Quotient.mk _ 1⟩
  let : Nontrivial (coindV H.subtype σ) := e.toEquiv.nontrivial
  obtain ⟨U, hU⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (coind H.subtype σ)
  have hn : U ≠ ⊥ := (Subrepresentation.irreducible_iff_isAtom U).mp hU |>.ne_bot
  refine ⟨U, hU, ?_, ?_⟩
  · have hs : Function.Surjective (evalOne H σ U) ∨ evalOne H σ U = 0 :=
      Representation.IsIrreducible.surjective_or_eq_zero
        (k := F) (G := H) (V := W) (W := U.toSubmodule)
        (ρ := σ) (σ := U.toRepresentation.comp H.subtype) (evalOne H σ U)
    exact hs.resolve_right (evalOne_ne_zero H σ U hn)
  · exact U.toSubmodule.finrank_le.trans_eq (coind_finrank H σ)

set_option backward.isDefEq.respectTransparency false in
/-- A catalogue below twice the desired degree passes to an index-at-most-two
subgroup when the degree-b modules have irreducible restrictions. -/
theorem minimum_of_small_ambient_catalogue (b : ℕ) (hindex : H.index ≤ 2)
    (hsmall : ∀ (V : Type (max v w)) [AddCommGroup V] [Module F V]
      [FiniteDimensional F V] (τ : Representation F G V),
      τ.IsIrreducible → Module.finrank F V < 2 * b →
        τ.IsTrivial ∨ Module.finrank F V = b)
    (hrestrict : ∀ (V : Type (max v w)) [AddCommGroup V] [Module F V]
      [FiniteDimensional F V] (τ : Representation F G V),
      τ.IsIrreducible → Module.finrank F V = b →
        Representation.IsIrreducible (k := F) (G := H) (V := V) (τ.comp H.subtype))
    [σ.IsIrreducible] (hn : ¬ σ.IsTrivial) : b ≤ Module.finrank F W := by
  classical
  let : Fintype G := Fintype.ofFinite G
  by_contra! hd
  obtain ⟨U, hU, hev, hu⟩ := exists_small_ambient H σ
  have hdim : Module.finrank F U.toSubmodule < 2 * b :=
    (hu.trans (Nat.mul_le_mul_right _ hindex)).trans_lt (by omega)
  rcases hsmall U.toSubmodule U.toRepresentation hU hdim with ht | hb
  · let := ht
    apply hn
    constructor
    intro h
    ext w
    obtain ⟨u, rfl⟩ := hev w
    rw [← IntertwiningMap.isIntertwining _ _ (evalOne H σ U)]
    change evalOne H σ U (U.toRepresentation h.val u) = evalOne H σ U u
    rw [Representation.isTrivial_def]
    rfl
  · let := hrestrict U.toSubmodule U.toRepresentation hU hb
    have hne := evalOne_ne_zero H σ U
      ((Subrepresentation.irreducible_iff_isAtom U).mp hU).ne_bot
    have hi : Function.Injective (evalOne H σ U) ∨ evalOne H σ U = 0 :=
      Representation.IsIrreducible.injective_or_eq_zero
        (k := F) (G := H) (V := U.toSubmodule) (W := W)
        (ρ := U.toRepresentation.comp H.subtype) (σ := σ) (evalOne H σ U)
    have hinj := hi.resolve_right hne
    have he := (LinearEquiv.ofBijective (evalOne H σ U).toLinearMap
      ⟨hinj, hev⟩).finrank_eq
    omega

end ReeF4.BinaryDegree.TitsAbsolute
