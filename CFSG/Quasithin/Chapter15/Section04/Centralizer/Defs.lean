module

public import CFSG.Quasithin.Chapter1.Defs
public import Mathlib.GroupTheory.Index

/-!
# The prime-quotient family in Section 15.4

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp. 1155–1156 and 1159.

The family `Xi` is the lowercase `ξ`, distinct from Chapter 1's uppercase
`Ξ`. The condition `X = O²(X)` is expressed by its exact universal property:
every normal subgroup with a 2-group quotient is the whole group. `XiStar`
adds uniqueness of the maximal **2-local** overgroup of `XT`. The product
`XT` is represented by `X ⊔ T`, using the required normalization by `T`.

The final theorem below is the overgroup argument of 15.4.3(3); its
uniqueness input must be established by 15.4.3(1).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04

open Subgroup

variable {G : Type*} [Group G]

/-- The family `ξ(G,T)` of 2-residual, `T`-invariant subgroups with odd
prime quotient by their two-core, whose product with `T` belongs to `H(T)`. -/
def Xi (T : Subgroup G) : Set (Subgroup G) :=
  {X | T ≤ normalizer (X : Set G) ∧
    (∀ (N : Subgroup X) (_ : N.Normal), IsPGroup 2 (X ⧸ N) → N = ⊤) ∧
    X ⊔ T ∈ Chapter1.HOver G (T : Set G) ∧
    (pCore 2 X).index.Prime ∧ Odd (pCore 2 X).index}

/-- The members of `ξ(G,T)` with a unique maximal two-local overgroup of `XT`. -/
def XiStar (T : Subgroup G) : Set (Subgroup G) :=
  {X | X ∈ Xi T ∧ ∃! M : Subgroup G, IsMaximalTwoLocal M ∧ X ⊔ T ≤ M}

/-- The counterexample family `𝒳` used in 15.4.9–10. The parameter `Z` is
specialized to `Ω₁(Z(T))` by the section's final assembly. -/
def NormalCentralizerXi (T Z : Subgroup G) : Set (Subgroup G) :=
  {X | X ∈ Xi T ∧ X ≤ centralizer (Z : Set G) ∧
    centralizer (Z : Set G) ≤ normalizer (X : Set G)}

/-- A member of `ξ` has a nontrivial quotient by its two-core. -/
theorem Xi.core_ne_top {T X : Subgroup G} (hX : X ∈ Xi T) :
    pCore 2 X ≠ ⊤ := by
  intro h
  exact hX.2.2.2.1.ne_one ((pCore 2 X).index_eq_one.mpr h)

/-- The uniqueness argument in 15.4.3(3): two distinct maximal two-local
overgroups of `C_G(Z)` prevent a member of `ξ*` from centralizing `Z`. -/
theorem XiStar.not_le_centralizer {T Z X M₁ M₂ : Subgroup G}
    (hX : X ∈ XiStar T)
    (hT : T ≤ centralizer (Z : Set G))
    (hM₁ : IsMaximalTwoLocal M₁) (hM₂ : IsMaximalTwoLocal M₂)
    (hC₁ : centralizer (Z : Set G) ≤ M₁)
    (hC₂ : centralizer (Z : Set G) ≤ M₂) (hne : M₁ ≠ M₂) :
    ¬ X ≤ centralizer (Z : Set G) := by
  intro hXC
  obtain ⟨M, _, huniq⟩ := hX.2
  exact hne ((huniq M₁ ⟨hM₁, (sup_le hXC hT).trans hC₁⟩).trans
    (huniq M₂ ⟨hM₂, (sup_le hXC hT).trans hC₂⟩).symm)

end CFSG.Quasithin.Chapter15.Section04
