module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.SubspaceQuotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.SetLike.Fintype

/-!
# Maximal avoiding submodules and the surviving seed

Maximizing dimension constructs an invariant subspace maximal subject to
avoiding a specified nonzero commutator subspace. If the seed orbit spans
the whole representation, it survives every proper invariant quotient.
The quotient projection intertwines the actual marked seed action; an
irreducible seed therefore maps injectively and is isomorphic to its image.

These results supply the selection and seed steps in Aschbacher–Smith,
proof of 13.8.16(1), printed p.952 (PDF p.969), combined manuscript of
1 March 2004. They do not identify the source conjugation representation
or derive the alternatives of F.9.18 and B.5. Maximality among H-submodules
alone is not used to assert irreducibility under the smaller group K₀.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]

/-- Choose the actual maximal invariant subspace avoiding the component
commutator, by maximizing its dimension. -/
theorem exists_maximal_avoiding [Finite U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) G U) (D : Submodule (ZMod 2) U) (hD : D ≠ ⊥) :
    ∃ W : Subrepresentation ρ, ¬ D ≤ W.toSubmodule ∧
      ∀ Y : Subrepresentation ρ, W ≤ Y → ¬ D ≤ Y.toSubmodule → Y = W := by
  classical
  let _ : Finite (Subrepresentation ρ) :=
    Finite.of_injective Subrepresentation.toSubmodule Subrepresentation.toSubmodule_injective
  obtain ⟨W, hW, hmax⟩ := Set.exists_max_image
    {W : Subrepresentation ρ | ¬ D ≤ W.toSubmodule}
    (fun W => Module.finrank (ZMod 2) W.toSubmodule) (Set.toFinite _)
    ⟨⊥, fun h => hD (le_bot_iff.mp h)⟩
  refine ⟨W, hW, ?_⟩
  intro Y hWY hY
  apply Subrepresentation.toSubmodule_injective
  exact (Submodule.eq_of_le_of_finrank_eq hWY
    (le_antisymm (Submodule.finrank_mono hWY) (hmax Y hY))).symm

/-- If the seed generates the whole representation, no proper invariant
subspace can contain it. The span is the actual linear span of the seed orbit. -/
theorem seed_not_le_proper (ρ : Representation (ZMod 2) G U)
    (X : Submodule (ZMod 2) U)
    (hspan : Submodule.span (ZMod 2) {u | ∃ g : G, ∃ x ∈ X, u = ρ g x} = ⊤)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤) : ¬ X ≤ W.toSubmodule := by
  intro h
  apply hW
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, x, hx, rfl⟩
  exact W.apply_mem_toSubmodule g (h hx)

/-- The seed has a nonzero image in the chosen quotient. -/
theorem seed_image_ne_bot_of_generates (ρ : Representation (ZMod 2) G U)
    (X : Submodule (ZMod 2) U)
    (hspan : Submodule.span (ZMod 2) {u | ∃ g : G, ∃ x ∈ X, u = ρ g x} = ⊤)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤) : X.map W.toSubmodule.mkQ ≠ ⊥ := by
  intro he
  apply seed_not_le_proper ρ X hspan W hW
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
  have hm : W.toSubmodule.mkQ x ∈ X.map W.toSubmodule.mkQ := ⟨x, hx, rfl⟩
  rwa [he] at hm
/-- The actual restriction of the quotient projection to the invariant seed,
with its equivariance proved from the quotient representation. -/
def seedQuotientMap (ρ : Representation (ZMod 2) G U) (A : Subgroup G)
    (X : Subrepresentation (ρ.comp A.subtype)) (W : Subrepresentation ρ) :
    Representation.IntertwiningMap X.toRepresentation
      (W.quotientRepresentation.comp A.subtype) where
  toLinearMap := W.toSubmodule.mkQ.comp X.toSubmodule.subtype
  isIntertwining' _ := by ext x; rfl

/-- Irreducibility of the marked seed makes its nonzero quotient projection
injective, as required in case (a). -/
theorem seedQuotientMap_injective (ρ : Representation (ZMod 2) G U) (A : Subgroup G)
    (X : Subrepresentation (ρ.comp A.subtype)) (W : Subrepresentation ρ)
    [Representation.IsIrreducible X.toRepresentation]
    (hne : ¬ X.toSubmodule ≤ W.toSubmodule) :
    Function.Injective (seedQuotientMap ρ A X W) := by
  apply (Representation.IsIrreducible.injective_or_eq_zero (seedQuotientMap ρ A X W)).resolve_right
  intro hz
  apply hne
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
  have he := congrArg (fun f => f (⟨x, hx⟩ : X.toSubmodule)) hz
  exact he

/-- The seed is linearly isomorphic to its actual quotient image; the
isomorphism is the quotient map itself, not an arbitrary dimension match. -/
noncomputable def seedQuotientEquiv (ρ : Representation (ZMod 2) G U) (A : Subgroup G)
    (X : Subrepresentation (ρ.comp A.subtype)) (W : Subrepresentation ρ)
    [Representation.IsIrreducible X.toRepresentation]
    (hne : ¬ X.toSubmodule ≤ W.toSubmodule) :
    X.toSubmodule ≃ₗ[ZMod 2] X.toSubmodule.map W.toSubmodule.mkQ := by
  let f : X.toSubmodule →ₗ[ZMod 2] X.toSubmodule.map W.toSubmodule.mkQ :=
    (seedQuotientMap ρ A X W).toLinearMap.codRestrict _
      (fun x => ⟨x, x.property, rfl⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    exact seedQuotientMap_injective ρ A X W hne (congrArg Subtype.val h)
  · rintro ⟨y, x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[simp] theorem seedQuotientEquiv_apply (ρ : Representation (ZMod 2) G U) (A : Subgroup G)
    (X : Subrepresentation (ρ.comp A.subtype)) (W : Subrepresentation ρ)
    [Representation.IsIrreducible X.toRepresentation]
    (hne : ¬ X.toSubmodule ≤ W.toSubmodule) (x : X.toSubmodule) :
    (seedQuotientEquiv ρ A X W hne x : U ⧸ W.toSubmodule) = W.toSubmodule.mkQ x := rfl

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo

end
