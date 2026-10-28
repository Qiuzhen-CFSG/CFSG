module
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Recovering an invariant subspace from its simple projected blocks

Polynomial projections onto distinct irreducible blocks preserve every
invariant subspace. Once each block intersection is zero or the whole
block, summing the projections recovers the subspace as a literal selection
of the original blocks. This is the final lattice step for the endpoint
induction certificate; no module classification is assumed here.
-/
public section
namespace BinaryEndpointInduction
variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype ι]

/-- A subspace preserved by a complete family of projections is the sum
of precisely those blocks which it contains, when intersections are simple. -/
theorem eq_iSup_blocks_of_projection_dichotomy
    (E : ι → Submodule F V) (π : ι → Module.End F V)
    (hπ : ∀ i, LinearMap.range (π i) ≤ E i)
    (hsum : ∑ i, π i=LinearMap.id)
    (U : Submodule F V) (hU : ∀ i x, x ∈ U → π i x ∈ U)
    (hblocks : ∀ i, U ⊓ E i=⊥ ∨ U ⊓ E i=E i) :
    U=⨆ i, ⨆ (_ : E i ≤ U), E i := by
  classical
  apply le_antisymm
  swap
  · refine iSup_le fun i => ?_
    exact iSup_le fun h => h
  intro x hx
  have hxsum : x=∑ i, π i x := by
    have hh := LinearMap.congr_fun hsum x
    simpa only [LinearMap.sum_apply,LinearMap.id_apply] using hh.symm
  rw [hxsum]
  apply Submodule.sum_mem
  intro i _
  have he : π i x ∈ U ⊓ E i := ⟨hU i x hx,hπ i ⟨x,rfl⟩⟩
  rcases hblocks i with hz | ht
  · rw [hz,Submodule.mem_bot] at he
    rw [he]
    exact Submodule.zero_mem _
  · have hEU : E i ≤ U := ht ▸ inf_le_left
    have hi : E i ≤ ⨆ j, ⨆ (_ : E j ≤ U), E j :=
      le_iSup_of_le i (le_iSup_of_le hEU le_rfl)
    exact hi (hπ i ⟨x,rfl⟩)
end BinaryEndpointInduction
