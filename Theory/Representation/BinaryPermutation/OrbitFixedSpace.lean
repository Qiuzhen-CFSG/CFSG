module

public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.PermutationBasisOrbits

/-!
# The orbit formula for full binary permutation modules

A fixed function is constant on each subgroup orbit. Identifying these
functions with functions on the orbit quotient gives one dimension per orbit,
and rank-nullity gives the fixed codimension. This is the linear-algebra part
of the orbit argument for Aschbacher–Smith, *The Classification of Quasithin
Groups*, B.3.2, pp. 83–84.
-/

public section

namespace BinaryPermutation

open Representation Representation.BinaryOffender

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
/-- Full fixed functions are precisely the functions respecting the orbit relation. -/
theorem full_fixedSpace_eq_respectful (A : Subgroup (Equiv.Perm Ω)) :
    fixedSpace (representation Ω) A =
      RespectfulFunctions (ZMod 2) Ω (MulAction.orbitRel A Ω) := by
  ext v
  rw [mem_full_fixedSpace_iff]
  constructor
  · intro hv i j hij
    obtain ⟨a, ha⟩ := (MulAction.orbitRel_apply.mp hij)
    change a.val j = i at ha
    subst i
    simpa only [Equiv.symm_apply_apply] using (hv a.val a.property (a.val j)).symm
  · intro hv a ha i
    apply hv
    exact MulAction.orbitRel_apply.mpr ⟨⟨a⁻¹, A.inv_mem ha⟩, rfl⟩

/-- The full fixed space has one dimension for each orbit. -/
theorem finrank_full_fixedSpace_eq_card_orbits (A : Subgroup (Equiv.Perm Ω)) :
    Module.finrank (ZMod 2) (fixedSpace (representation Ω) A) =
      Nat.card (MulAction.orbitRel.Quotient A Ω) := by
  rw [full_fixedSpace_eq_respectful]
  exact quotientFunctionsLinearEquivRespectful_finrank (ZMod 2) Ω _

/-- Fixed codimension plus the number of orbits equals the permutation degree. -/
theorem fixedCodim_full_add_card_orbits (A : Subgroup (Equiv.Perm Ω)) :
    fixedCodim (representation Ω) A + Nat.card (MulAction.orbitRel.Quotient A Ω) =
      Fintype.card Ω := by
  rw [← finrank_full_fixedSpace_eq_card_orbits, fixedCodim_add_finrank, finrank_full]

/-- The full fixed codimension is the degree minus the number of orbits. -/
theorem fixedCodim_full_eq_card_sub_card_orbits (A : Subgroup (Equiv.Perm Ω)) :
    fixedCodim (representation Ω) A =
      Fintype.card Ω - Nat.card (MulAction.orbitRel.Quotient A Ω) := by
  have := fixedCodim_full_add_card_orbits A
  omega

end BinaryPermutation
