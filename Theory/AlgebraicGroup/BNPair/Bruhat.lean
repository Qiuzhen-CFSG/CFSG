module

public import Mathlib.Algebra.Group.Submonoid.Membership
public import Theory.AlgebraicGroup.BNPair.DoubleCoset
public import Theory.AlgebraicGroup.BNPair.Generation

/-! Bruhat double-coset coverage for a Tits system. -/

namespace Theory.AlgebraicGroup.TitsSystem

open scoped Pointwise

variable {X : Type*} [Group X]

private lemma exists_doubleCoset_of_mem_mul (T : TitsSystem (X := X))
    (u v : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) {x : X}
    (hx : x ∈
      ((T.B : Set X) * representativeSet T.B T.N u * (T.B : Set X)) *
        ((T.B : Set X) * representativeSet T.B T.N v * (T.B : Set X))) :
    ∃ w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N,
      x ∈ (T.B : Set X) * representativeSet T.B T.N w * (T.B : Set X) := by
  induction u using Submonoid.induction_of_closure_eq_top_left
      T.submonoid_closure_S_eq_top generalizing x with
  | one =>
      rw [doubleCoset_one_eq_B] at hx
      obtain ⟨b, hb, z, hz, rfl⟩ := Set.mem_mul.mp hx
      refine ⟨v, ?_⟩
      simpa only [mul_one] using
        mul_mem_doubleCoset T.B T.N v hb T.B.one_mem hz
  | mul_left s hs u ih =>
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
      have ha' := doubleCoset_mul_subset_product T.B T.N s u ha
      obtain ⟨as, has, au, hau, hasu⟩ := Set.mem_mul.mp ha'
      have haub : au * b ∈
          ((T.B : Set X) * representativeSet T.B T.N u * (T.B : Set X)) *
            ((T.B : Set X) * representativeSet T.B T.N v * (T.B : Set X)) :=
        ⟨au, hau, b, hb, rfl⟩
      obtain ⟨w, hw⟩ := ih haub
      have hasw : as * (au * b) ∈
          ((T.B : Set X) * representativeSet T.B T.N s * (T.B : Set X)) *
            ((T.B : Set X) * representativeSet T.B T.N w * (T.B : Set X)) :=
        ⟨as, has, au * b, hw, rfl⟩
      have hx' : a * b = as * (au * b) := by rw [← hasu, mul_assoc]
      rw [hx']
      rcases doubleCoset_mul_doubleCoset_subset_of_mem_S T hs w hasw with hsw | hw'
      · exact ⟨s * w, hsw⟩
      · exact ⟨w, hw'⟩

private lemma inv_mem_doubleCoset (B N : Subgroup X)
    [((B ⊓ N).subgroupOf N).Normal]
    (w : N ⧸ (B ⊓ N).subgroupOf N) {x : X}
    (hx : x ∈ (B : Set X) * representativeSet B N w * (B : Set X)) :
    x⁻¹ ∈ (B : Set X) * representativeSet B N w⁻¹ * (B : Set X) := by
  obtain ⟨y, hy, b₂, hb₂, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨b₁, hb₁, n, ⟨nN, hnw, rfl⟩, rfl⟩ := Set.mem_mul.mp hy
  refine ⟨(b₂⁻¹ * (nN⁻¹ : N) : X), ?_, b₁⁻¹, B.inv_mem hb₁, ?_⟩
  · exact ⟨b₂⁻¹, B.inv_mem hb₂, (nN⁻¹ : N),
      ⟨nN⁻¹, by rw [map_inv, hnw], rfl⟩, rfl⟩
  · simp only [mul_inv_rev, Subgroup.coe_inv, mul_assoc]

/-- Every element of a group with a Tits system belongs to a double coset
indexed by its quotient `N / (B ∩ N)`. -/
public theorem exists_mem_doubleCoset (T : TitsSystem (X := X)) (x : X) :
    ∃ w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N,
      x ∈ (T.B : Set X) * representativeSet T.B T.N w * (T.B : Set X) := by
  have hx : x ∈ Subgroup.closure ((T.B : Set X) ∪ (T.N : Set X)) := by
    rw [T.generate]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with hxB | hxN
      · refine ⟨1, ?_⟩
        rw [doubleCoset_one_eq_B]
        exact hxB
      · let n : T.N := ⟨x, hxN⟩
        let w := QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n
        refine ⟨w, x, ⟨1, T.B.one_mem, x, ⟨n, rfl, rfl⟩, one_mul x⟩,
          1, T.B.one_mem, mul_one x⟩
  | one =>
      refine ⟨1, ?_⟩
      rw [doubleCoset_one_eq_B]
      exact T.B.one_mem
  | mul x y hx hy ihx ihy =>
      obtain ⟨u, hu⟩ := ihx
      obtain ⟨v, hv⟩ := ihy
      exact exists_doubleCoset_of_mem_mul T u v ⟨x, hu, y, hv, rfl⟩
  | inv x hx ih =>
      obtain ⟨u, hu⟩ := ih
      exact ⟨u⁻¹, inv_mem_doubleCoset T.B T.N u hu⟩

end Theory.AlgebraicGroup.TitsSystem
