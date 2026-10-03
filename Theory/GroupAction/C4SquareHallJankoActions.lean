module

public import Theory.GroupTheory.PGroup.C4SquareBasis

/-!
# Hall–Janko actions on an abelian base

This interface describes a basis and three automorphisms of a C₄-square.
The two inner actions belong to a designated subgroup of the full action
group. It deliberately makes no assertion about an extension or its lifts.
Selecting this data is a finite automorphism problem; lifting it through an
actual conjugation map is a separate group-theoretic operation.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386,
citing MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

@[expose] public section
namespace C4SquareExtension

/-- The six Hall–Janko actions in two nested automorphism subgroups. -/
structure HallJankoAutActions {A : Type*} [Group A]
    (H K : Subgroup (MulAut A)) where
  a : A
  b : A
  a_four : a ^ 4 = 1
  b_four : b ^ 4 = 1
  ba : b * a = a * b
  base : Subgroup.closure ({a, b} : Set A) = ⊤
  four : omega₁ A (p := 2) = Subgroup.closure ({a ^ 2, b ^ 2} : Set A)
  u : MulAut A
  v : MulAut A
  t : MulAut A
  u_mem : u ∈ H
  v_mem : v ∈ H
  t_mem : t ∈ K
  ua : u a = a⁻¹ * b ^ 2
  ub : u b = b⁻¹
  va : v a = a * b ^ 2
  vb : v b = a ^ 2 * b
  ta : t a = a * b
  tb : t b = b⁻¹

/-- The competing action: two partial inversions exchanged by an outer
coset. This finite-action interface carries no assertion about its occurrence
in a group extension. In an elementary supplement it forces a normal
elementary sixteen, so it will be excluded by the intrinsic hypotheses. -/
structure SplitInversionAutActions {A : Type*} [Group A]
    (H K : Subgroup (MulAut A)) where
  a : A
  b : A
  a_four : a ^ 4 = 1
  b_four : b ^ 4 = 1
  ba : b * a = a * b
  base : Subgroup.closure ({a, b} : Set A) = ⊤
  a_two_ne : a ^ 2 ≠ 1
  b_two_ne : b ^ 2 ≠ 1
  squares_ne : a ^ 2 ≠ b ^ 2
  u : MulAut A
  v : MulAut A
  t : MulAut A
  u_mem : u ∈ H
  v_mem : v ∈ H
  t_mem : t ∈ K
  ua : u a = a⁻¹
  ub : u b = b
  va : v a = a
  vb : v b = b⁻¹
  ta_two : t (a ^ 2) = b ^ 2
  tb_two : t (b ^ 2) = a ^ 2
  tut : t * u * t⁻¹ = v
  tvt : t * v * t⁻¹ = u

end C4SquareExtension
