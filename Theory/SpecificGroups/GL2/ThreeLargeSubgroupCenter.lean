module
public import Theory.SpecificGroups.GL2.SubgroupCenter
public import Theory.SpecificGroups.GL2.ThreeConjugacy
public import Mathlib.GroupTheory.IndexNormal

/-!
# Centers of large subgroups of GL₂(3)

Every subgroup of order 24 or 48 contains the scalar involution, and its
center consists exactly of the identity and that involution. Index-two
subgroups contain squares; two explicit squares do not commute. The
noncommutative subgroup-center theorem then reduces the center to scalars.

Source: Wong (1964), Theorem 6(b), printed p.110.
-/

open Matrix
namespace Matrix.GeneralLinearGroup

private theorem threeGL_card : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field]
  decide

private theorem three_scalar_cases (u : (ZMod 3)ˣ) :
    scalar (Fin 2) u = (1 : GL (Fin 2) (ZMod 3)) ∨
      scalar (Fin 2) u = threeCentral := by
  fin_cases u <;> decide +kernel

private theorem threeCentral_scalar :
    threeCentral = scalar (Fin 2) (-1 : (ZMod 3)ˣ) := by
  decide +kernel

/-- An order-24 or order-48 subgroup has precisely the scalar involution in its
center besides the identity. -/
public theorem three_large_subgroup_center
    (D : Subgroup (GL (Fin 2) (ZMod 3)))
    (hcard : Nat.card D = 24 ∨ Nat.card D = 48) :
    threeCentral ∈ D ∧
      ∀ z : D, z ∈ Subgroup.center D ↔ (z : GL (Fin 2) (ZMod 3)) = 1 ∨
        (z : GL (Fin 2) (ZMod 3)) = threeCentral := by
  have hindex : D.index = 1 ∨ D.index = 2 := by
    have h := D.card_mul_index
    rw [threeGL_card] at h
    rcases hcard with hc | hc
    · rw [hc] at h
      omega
    · rw [hc] at h
      omega
  have hsquare (x : GL (Fin 2) (ZMod 3)) : x ^ 2 ∈ D := by
    rcases hindex with h | h
    · rw [Subgroup.index_eq_one.mp h]
      trivial
    · exact D.sq_mem_of_index_two h x
  have hcentral : threeCentral ∈ D := by
    have h := hsquare (threeRotation ^ 2)
    have he : threeRotation ^ 4 = threeCentral := by decide +kernel
    simpa only [← pow_mul, two_mul, he] using h
  have hnoncomm : ¬ IsMulCommutative D := by
    intro hc
    have h := congrArg (fun z : D => (z : GL (Fin 2) (ZMod 3)))
      ((isMulCommutative_iff.mp hc)
        (⟨threeRotation ^ 2, hsquare threeRotation⟩ : D)
        (⟨threeUnipotent ^ 2, hsquare threeUnipotent⟩ : D))
    have hne : threeRotation ^ 2 * threeUnipotent ^ 2 ≠
        threeUnipotent ^ 2 * threeRotation ^ 2 := by decide +kernel
    exact hne (by simpa using h)
  refine ⟨hcentral, ?_⟩
  intro z
  constructor
  · intro hz
    have hm : (z : GL (Fin 2) (ZMod 3)) ∈
        (D ⊓ (scalar (Fin 2) : (ZMod 3)ˣ →* GL (Fin 2) (ZMod 3)).range) := by
      rw [← center_map_eq_inf_scalar_of_noncommutative D hnoncomm]
      exact ⟨z, hz, rfl⟩
    obtain ⟨u, hu⟩ := hm.2
    rcases three_scalar_cases u with h | h
    · left; exact hu.symm.trans h
    · right; exact hu.symm.trans h
  · rintro (h | h)
    · have hz : z = 1 := Subtype.ext h
      rw [hz]
      exact Subgroup.one_mem _
    · have hzcentral : (z : GL (Fin 2) (ZMod 3)) ∈
          Subgroup.center (GL (Fin 2) (ZMod 3)) := by
        rw [h, threeCentral_scalar, center_eq_range_scalar]
        exact ⟨_, rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro x
      apply Subtype.ext
      simpa using (Subgroup.mem_center_iff.mp hzcentral x)

end Matrix.GeneralLinearGroup
