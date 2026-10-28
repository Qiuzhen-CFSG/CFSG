module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Theory.GroupTheory.DoubleCosetCard

/-!
# The local subgroups needed for Janko's fixed-space argument

The source constructs actual subgroups `X = (N(F))'`, `Y = EQ*Z*`, and
`B = EQ*`. Their element counts give fixed-space dimensions 2, 3, and 4
for the degree-21 character. The double-coset calculation gives a lower
bound of 20160 for the subgroup they generate. These facts do not assert
that the generated subgroup is proper or has index 22.

`LocalConfiguration` is the shared conclusion of the local-subgroup
construction, whose existence from `LocalData` remains to be proved.
It contains subgroups of the input group, not abstract local model tags.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, DOI 10.1016/0021-8693(68)90002-1,
Section 8, pp.16--17, proof of Lemma 17. Here `Y` is the subgroup
`EQ*Z*`, whereas the source's intermediate letter Y has another meaning.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction

universe u

/-- The full element-order census used by the three local subgroups. -/
@[expose] public def localOrderCount (a2 a3 a4 a5 k : ℕ) : ℕ :=
  if k = 1 then 1 else if k = 2 then a2 else if k = 3 then a3 else
    if k = 4 then a4 else if k = 5 then a5 else 0

/-- Actual local subgroups, their intersection inclusions, and the census and
size facts needed for the fixed-space construction. No proper overgroup or
degree-22 action is included. -/
public structure LocalConfiguration (G : Type u) [Group G] where
  X : Subgroup G
  Y : Subgroup G
  B : Subgroup G
  B_le_X : B ≤ X
  B_le_Y : B ≤ Y
  X_card : Nat.card X = 960
  Y_card : Nat.card Y = 96
  B_card : Nat.card B = 48
  X_count : ∀ k : ℕ, Nat.card {x : X // orderOf x = k} = localOrderCount 75 320 180 384 k
  Y_count : ∀ k : ℕ, Nat.card {y : Y // orderOf y = k} = localOrderCount 27 32 36 0 k
  B_count : ∀ k : ℕ, Nat.card {b : B // orderOf b = k} = localOrderCount 15 32 0 0 k
  generated_card_lower : 20160 ≤ Nat.card (X ⊔ Y : Subgroup G)

/-- The source's conjugate-intersection calculation supplies the size field:
`X` and `X z X` contribute `960 + 960² / 48 = 20160` elements. It is not
necessary to assume that their union is a subgroup. -/
public theorem generated_card_lower_of_conjugate_intersection
    {G : Type u} [Group G] [Finite G] (X Y : Subgroup G)
    (hX : Nat.card X = 960) (z : G) (hzY : z ∈ Y) (hzX : z ∉ X)
    (hinter : Nat.card (X ⊓ X.map (MulAut.conj z).toMonoidHom : Subgroup G) = 48) :
    20160 ≤ Nat.card (X ⊔ Y : Subgroup G) := by
  have h := Subgroup.card_add_doubleCoset_le_card X (X ⊔ Y) le_sup_left z
    ((show Y ≤ X ⊔ Y from le_sup_right) hzY) hzX
  simpa only [hX, hinter] using h

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction
