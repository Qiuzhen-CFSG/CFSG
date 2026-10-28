module
public import Theory.GroupTheory.CyclicExtension
/-!
# Collection through a cyclic quotient

The new generator's bounded power need only belong to the old subgroup.
Positive-word collection absorbs that power in the old subgroup whenever
an exponent wraps. Finiteness permits positive-word induction for the
whole generated subgroup. This is the nonsplit form of cyclic collection,
used in the order-96 vertex of Aschbacher–Smith F.1.12(I)(8), p.263.
-/
namespace Theory.GroupTheory
public theorem exists_mul_pow_of_mem_closure_insert_of_pow_mem
    {G : Type*} [Group G] [Finite G]
    (S : Set G) (a : G) (m : ℕ) (hm : 0 < m) (ha : a ^ m ∈ Subgroup.closure S)
    (hc : ∀ b ∈ S, a * b * a⁻¹ ∈ Subgroup.closure S)
    {x : G} (hx : x ∈ Subgroup.closure (insert a S)) :
    ∃ y ∈ Subgroup.closure S, ∃ i : Fin m, y * a ^ i.val = x := by
  have hconj : ∀ y ∈ Subgroup.closure S, a * y * a⁻¹ ∈ Subgroup.closure S := by
    have hle : Subgroup.closure S ≤
        (Subgroup.closure S).comap (MulAut.conj a).toMonoidHom :=
      (Subgroup.closure_le _).mpr hc
    exact hle
  change x ∈ (Subgroup.closure (insert a S)).toSubmonoid at hx
  rw [Subgroup.closure_toSubmonoid_of_finite] at hx
  induction hx using Submonoid.closure_induction_left with
  | one => exact ⟨1, (Subgroup.closure S).one_mem, ⟨0, hm⟩, by simp⟩
  | mul_left b hb x _ ih =>
    rcases ih with ⟨y, hy, i, rfl⟩
    rcases hb with rfl | hb
    · by_cases hi : i.val+1<m
      · refine ⟨b*y*b⁻¹,hconj y hy,⟨i.val+1,hi⟩,?_⟩
        rw [pow_succ']
        simp [mul_assoc]
      · have he : i.val+1=m := by omega
        refine ⟨(b*y*b⁻¹)*b^m,(Subgroup.closure S).mul_mem (hconj y hy) ha,
          ⟨0,hm⟩,?_⟩
        change (b*y*b⁻¹)*b^m*b^0=b*(y*b^i.val)
        have hp : b^m=b*b^i.val :=
          (congrArg (fun n:ℕ => b^n) he.symm).trans (pow_succ' b i.val)
        rw [hp]
        simp [mul_assoc]
    · exact ⟨b * y, (Subgroup.closure S).mul_mem (Subgroup.subset_closure hb) hy,
        i, mul_assoc _ _ _⟩
end Theory.GroupTheory
