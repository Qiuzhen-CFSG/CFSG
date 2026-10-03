module

public import Theory.SpecificGroups.GL2.ThreeBorelCensus

/-!
# Generators of the upper-triangular subgroup of GL₂(3)

The scalar involution, diagonal reflection, and upper unipotent generate the
actual Borel subgroup. The reflection inverts the unipotent and has no
nonidentity commuting element of cube one. All matrix calculations below are
finite calculations checked by the kernel.

Source: Wong (1964), Appendix (b), pp.109–110.
-/

namespace Matrix.GeneralLinearGroup
open Matrix

private abbrev Mat := Matrix (Fin 2) (Fin 2) (ZMod 3)

private theorem borel_matrix_forms : ∀ A : Mat, A.det ≠ 0 → A 1 0 = 0 →
    ∃ i : Fin 2, ∃ j : Fin 2, ∃ k : Fin 3,
      A = (threeCentral ^ i.val * threeReflection ^ j.val * threeUnipotent ^ k.val).val := by
  decide +kernel

/-- The diagonal involution reverses the upper unipotent. -/
public theorem threeReflection_inverts_unipotent :
    threeReflection * threeUnipotent * threeReflection⁻¹ = threeUnipotent⁻¹ := by
  decide +kernel

/-- The two involutions commute. -/
public theorem threeCentral_commute_reflection : Commute threeCentral threeReflection := by
  exact show threeCentral * threeReflection = threeReflection * threeCentral from by decide +kernel

/-- A matrix of cube one commuting with the diagonal reflection is the identity. -/
public theorem threeReflection_cubic_centralizer (x : GL (Fin 2) (ZMod 3))
    (hx : x ^ 3 = 1) (hc : Commute threeReflection x) : x = 1 := by
  have hm : ∀ A : Mat, A ^ 3 = 1 →
      threeReflection.val * A = A * threeReflection.val → A = 1 := by
    decide +kernel
  apply Units.ext
  exact hm x.val (congrArg Units.val hx) (congrArg Units.val hc.eq)

/-- The three particular matrices generate the upper-triangular subgroup. -/
public theorem three_borel_eq_closure : GLTwo.borelSubgroup (ZMod 3) =
    Subgroup.closure ({threeCentral, threeReflection, threeUnipotent} :
      Set (GL (Fin 2) (ZMod 3))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨i, j, k, he⟩ := borel_matrix_forms x.val x.det_ne_zero hx
    have hx' : x = threeCentral ^ i.val * threeReflection ^ j.val * threeUnipotent ^ k.val :=
      Units.ext he
    rw [hx']
    apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
      · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
    · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · change threeCentral.val 1 0 = 0
      decide +kernel
    · change threeReflection.val 1 0 = 0
      decide +kernel
    · change threeUnipotent.val 1 0 = 0
      decide +kernel

end Matrix.GeneralLinearGroup
