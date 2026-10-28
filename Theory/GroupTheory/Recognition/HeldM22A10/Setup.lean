module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Theory.ElementaryAbelian.Basic

/-!
# Local hypotheses for Held's M22/A10 recognition

`LocalData G` records a Sylow two-subgroup with cyclic intrinsic center, a
central involution, and a normal elementary abelian subgroup of order sixteen
in its actual ambient centralizer, with quotient isomorphic to S4. Finiteness
and simplicity of G are separate hypotheses of the recognition problem.
There is no splitting or global identification in this data.

The elementary bridges identify the original involution in G and in its
centralizer and restrict the chosen Sylow subgroup to that centralizer without
conjugation. The exposed definitions specify these exact subgroup inclusions.

Source: Huppert--Blackburn, *Finite Groups III*, XII, 1.18(b), printed p.314
(PDF p.322 of `books/KGroup/HuppertBlackburn_FiniteGroupsIII.pdf`). The cited
papers are D. Held, J. Algebra 8 (1968), 436--449,
DOI 10.1016/0021-8693(68)90054-9, and Z. Janko, J. Algebra 9 (1968), 1--19
and 20--41. This module states only the local input and its elementary bridges.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10
universe u

/-- The local input of the M22/A10 recognition problem, with actual quotient data. -/
public structure LocalData (G : Type u) [Group G] where
  /-- The chosen ambient Sylow two-subgroup. -/
  sylow : Sylow 2 G
  /-- The involution lies in the intrinsic center of the chosen Sylow subgroup. -/
  involution : center sylow
  involution_order : orderOf involution = 2
  cyclic_center : IsCyclic (center sylow)
  /-- The elementary subgroup is inside the actual ambient involution centralizer. -/
  kernel : Subgroup (centralizer ({((involution : sylow) : G)} : Set G))
  /-- Normality is relative to the involution centralizer. -/
  kernel_normal : kernel.Normal
  kernel_elementary : IsElementaryAbelian 2 kernel
  kernel_card : Nat.card kernel = 16
  quotientEquiv : letI := kernel_normal;
    (centralizer ({((involution : sylow) : G)} : Set G) ⧸ kernel) ≃* Equiv.Perm (Fin 4)

namespace LocalData
variable {G : Type u} [Group G] (D : LocalData G)

/-- The ambient image of the specified central involution. -/
public abbrev z : G := ((D.involution : D.sylow) : G)

/-- The actual centralizer in G of the specified involution. -/
public abbrev centralizer : Subgroup G := Subgroup.centralizer {D.z}

/-- The same involution, viewed inside its ambient centralizer. -/
@[expose] public def centralInvolution : D.centralizer :=
  ⟨D.z, mem_centralizer_singleton_iff.mpr rfl⟩

/-- Taking the ambient image preserves the involution's order. -/
public theorem z_order : orderOf D.z = 2 := by
  simpa only [z, Subgroup.orderOf_coe] using D.involution_order

/-- The distinguished ambient element is nonidentity. -/
public theorem z_ne_one : D.z ≠ 1 := by
  intro h
  simpa [h] using D.z_order

/-- An element is central in its own centralizer. -/
public theorem centralInvolution_mem_center : D.centralInvolution ∈ center D.centralizer := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)

/-- The given Sylow subgroup lies in the distinguished involution centralizer. -/
public theorem sylow_le_centralizer : (D.sylow : Subgroup G) ≤ D.centralizer := by
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_center_iff.mp D.involution.property ⟨x, hx⟩))

/-- The restriction of the original Sylow subgroup, with no conjugation. -/
@[expose] public def localSylow : Sylow 2 D.centralizer := D.sylow.subtype D.sylow_le_centralizer

end LocalData
end Theory.GroupTheory.HeldM22A10
