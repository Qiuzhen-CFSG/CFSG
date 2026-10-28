module

public import Theory.SpecificGroups.ReeTwo.InvolutionCharacters

/-!
# The first omega subgroup of the Ree two Sylow model

The first omega subgroup is exactly the intersection of the parity and core
character kernels. The forward inclusion follows because both characters kill
involutions. Conversely, the core coordinate lies in the core omega subgroup,
and the even cyclic-four coordinate itself has square one. Their product
therefore lies in the Sylow omega subgroup.

Source: the verified Shinoda (1975), (2.3), pp. 81–82, coordinate model and the
core omega calculation in `CoreCharacterKernel`. This argument does not use a
subgroup census.
-/

namespace ReeTwo.SylowModel

private theorem inl_omega_le :
    (omega₁ Core (p := 2)).map (SemidirectProduct.inl : Core →* SylowModel) ≤
      omega₁ SylowModel (p := 2) := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  intro x hx
  apply Subgroup.subset_closure
  change (SemidirectProduct.inl x : SylowModel) ^ (2 ^ 1) = 1
  rw [← map_pow, show x ^ (2 ^ 1) = 1 from hx, map_one]

/-- The two binary coordinates detect exactly the quotient by the first omega subgroup. -/
public theorem omega_eq_character_ker_inf_coreCharacter_ker :
    omega₁ SylowModel (p := 2) = character.ker ⊓ coreCharacter.ker := by
  apply le_antisymm
  · refine le_inf ?_ (omega_le_alternativeCharacter_ker coreCharacter (Or.inl rfl))
    apply (Subgroup.closure_le _).mpr
    intro x hx
    exact character_eq_one_of_square_eq_one x (by simpa only [Set.mem_ofPred_eq, pow_one] using hx)
  · intro g hg
    have hl : Core.binaryCharacter g.left = 1 := hg.2
    have hlmem : SemidirectProduct.inl g.left ∈ omega₁ SylowModel (p := 2) := by
      apply inl_omega_le
      apply Subgroup.mem_map_of_mem
      rw [← Core.binaryCharacter_ker_eq_omega]
      exact hl
    have hr : parity g.right = 1 := hg.1
    have hrsq : g.right ^ 2 = 1 :=
      (by decide +kernel : ∀ t : FiveFour.Cyclic 4, parity t = 1 → t ^ 2 = 1) g.right hr
    have hrmem : (SemidirectProduct.inr g.right : SylowModel) ∈ omega₁ SylowModel (p := 2) := by
      apply Subgroup.subset_closure
      change (SemidirectProduct.inr g.right : SylowModel) ^ (2 ^ 1) = 1
      rw [pow_one, ← map_pow, hrsq, map_one]
    have heq := (SemidirectProduct.inl_left_mul_inr_right g).symm
    rw [heq]
    exact (omega₁ SylowModel (p := 2)).mul_mem hlmem hrmem

/-- Membership in the first omega subgroup is a pair of binary character tests. -/
public theorem mem_omega_iff (g : SylowModel) :
    g ∈ omega₁ SylowModel (p := 2) ↔ character g = 1 ∧ coreCharacter g = 1 := by
  rw [omega_eq_character_ker_inf_coreCharacter_ker]
  rfl

/-- Omega containment separates into parity containment and core-character containment. -/
public theorem le_omega_iff (U : Subgroup SylowModel) :
    U ≤ omega₁ SylowModel (p := 2) ↔ U ≤ character.ker ∧ U ≤ coreCharacter.ker := by
  rw [omega_eq_character_ker_inf_coreCharacter_ker, le_inf_iff]

end ReeTwo.SylowModel
