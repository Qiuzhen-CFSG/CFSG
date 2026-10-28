module

public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.PGroupCore

/-!
# Solvability of the prime-core central-quotient kernel

The preimage of Z(G/Oₚ(G)) is an extension of a p-group by an abelian
subgroup. It is therefore solvable; no triviality of the central cover
is asserted. This lets a perfect local subgroup retain its simple quotient
under the literal O₂,Z projection in Aschbacher--Smith, 3.3.22, pp.597--598.
-/

public section
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- The literal Oₚ,Z kernel is solvable, including its central factor. -/
theorem centralPreimage_pCore_isSolvable (p : ℕ) [Fact p.Prime] :
    Group.IsSolvable (centralPreimage (pCore p G)) := by
  let : Group.IsNilpotent (pCore p G) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (QuotientGroup.mk' (pCore p G)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  exact isSolvable_comap_of_solvable_ker (QuotientGroup.mk' (pCore p G)) _
end Subgroup
