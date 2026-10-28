module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers inside subgroups

This module provides the standard intersections expressing the centralizer of
a subgroup or an element inside a specified ambient subgroup.
-/

/-- The centralizer of a subgroup `S` inside a subgroup `H`. -/
@[expose] public def subgroupCentralizerIn {G : Type*} [Group G]
    (H S : Subgroup G) : Subgroup G :=
  H ⊓ Subgroup.centralizer (S : Set G)

/-- The centralizer of an element `x` inside a subgroup `H`. -/
@[expose] public def elementCentralizerIn {G : Type*} [Group G]
    (H : Subgroup G) (x : G) : Subgroup G :=
  H ⊓ Subgroup.centralizer ({x} : Set G)
