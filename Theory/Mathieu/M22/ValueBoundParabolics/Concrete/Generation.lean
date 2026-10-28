module
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Geometry

/-!
# Generation by the marked M₂₂ local subgroups

Six words in the standard degree-22 generators lie in the pair stabilizer or
in the hexad-partition stabilizer. Conversely, explicit words in these six
elements recover both standard generators. All permutation identities are
checked by the Lean kernel. The standard odd design involution belongs to
the outer pair stabilizer, giving generation of the full design group too.

This proves the generation clause used in Aschbacher–Smith E.4.3(2),
printed pp. 241–242. The words were found with GAP on the repository's
standard generators; GAP output is not used as a proof oracle.
-/

namespace Sporadic.Mathieu.M22ValueBound.Concrete
open Subgroup
open scoped Pointwise

private noncomputable def a : M22 := ⟨m22GeneratorA, m22GeneratorA_mem_M22⟩
private noncomputable def b : M22 := ⟨m22GeneratorB, m22GeneratorB_mem_M22⟩

private def localPerm : Fin 6 → Equiv.Perm (Fin 22) :=
  ![List.formPerm [5, 17, 16] * List.formPerm [6, 0, 11] * List.formPerm [7, 21, 15] * List.formPerm [8, 13, 14] * List.formPerm [9, 12, 19] * List.formPerm [10, 20, 18],
    List.formPerm [4, 6, 0] * List.formPerm [5, 8, 7] * List.formPerm [9, 21, 14] * List.formPerm [10, 18, 20] * List.formPerm [12, 13, 16] * List.formPerm [15, 19, 17],
    List.formPerm [4, 15] * List.formPerm [5, 6] * List.formPerm [7, 21] * List.formPerm [8, 17] * List.formPerm [9, 0] * List.formPerm [11, 13] * List.formPerm [12, 16] * List.formPerm [14, 19],
    List.formPerm [3, 21, 0] * List.formPerm [4, 8, 20] * List.formPerm [6, 19, 14] * List.formPerm [7, 9, 10] * List.formPerm [11, 16, 13] * List.formPerm [15, 17, 18],
    List.formPerm [1, 2] * List.formPerm [4, 8, 16, 6] * List.formPerm [5, 15, 17, 12] * List.formPerm [7, 0, 13, 19] * List.formPerm [9, 11, 14, 21] * List.formPerm [10, 20],
    List.formPerm [1, 18] * List.formPerm [2, 20] * List.formPerm [6, 21] * List.formPerm [8, 12] * List.formPerm [9, 11] * List.formPerm [13, 16] * List.formPerm [14, 15] * List.formPerm [17, 0]]

private noncomputable def localElement : Fin 6 → M22 :=
  ![[(b⁻¹) ^ 2, a, b⁻¹, a, b ^ 2, a, b, a, b, a, b, a, b⁻¹, a, b, a, b⁻¹, a ^ 2, b, a, b ^ 2, a, b⁻¹, a, b, a, b, a, b, a, b⁻¹, a, b, a, b, a, b⁻¹, a, b⁻¹, a].prod,
    [a⁻¹, b, a⁻¹, b, a⁻¹, b⁻¹, a⁻¹, b, a⁻¹, b⁻¹, a, b, a, b⁻¹, a, b ^ 2, a, b⁻¹, a, b ^ 2, a, b, a, b, a, b⁻¹, a, b, a, (b⁻¹) ^ 2, a⁻¹, b⁻¹, a⁻¹, b⁻¹, a⁻¹, b, a⁻¹, (b⁻¹) ^ 2, a⁻¹, b⁻¹, a⁻¹, (b⁻¹) ^ 2].prod,
    [a⁻¹, b⁻¹, a⁻¹, b⁻¹, a⁻¹, (b⁻¹) ^ 2, a⁻¹, b⁻¹, a⁻¹, (b⁻¹) ^ 2, a⁻¹, b, a, b, a, b⁻¹, a, b ^ 2, a, b⁻¹, a, b⁻¹, a, b, a, b, a ^ 2, b, a, b, a, b⁻¹, a, b, a, b, a, b⁻¹, a, b⁻¹, a, b⁻¹, a, b, a⁻¹, (b⁻¹) ^ 2, a⁻¹, b⁻¹, a⁻¹, b⁻¹, a, b, a, b⁻¹, a, b⁻¹, a].prod,
    [a⁻¹, b, (a⁻¹) ^ 2, b⁻¹, a⁻¹, b⁻¹, a⁻¹, b ^ 2, a, b⁻¹, a, b ^ 2, a, b⁻¹, a, b, a, b, a, b, a].prod,
    [b, a, b, a, b⁻¹, a, (b⁻¹) ^ 2, a⁻¹, b⁻¹, a⁻¹, b⁻¹, a⁻¹, b, a⁻¹, b, a⁻¹, b⁻¹, a, b, a, b, a, b, a, b ^ 2, a].prod,
    [a⁻¹, (b⁻¹) ^ 2, a⁻¹].prod]

private theorem localElement_coe (i : Fin 6) :
    (localElement i : Equiv.Perm (Fin 22)) = localPerm i := by
  fin_cases i <;> decide +kernel

private theorem localElement_mem (i : Fin 6) : localElement i ∈ first ⊔ second := by
  by_cases h : i = 5
  · subst i
    apply mem_sup_right
    change (localElement 5 : Equiv.Perm (Fin 22)) • hexadPartition = hexadPartition
    rw [localElement_coe]
    decide +kernel
  · apply mem_sup_left
    change (localElement i : Equiv.Perm (Fin 22)) • m22Pair12 = m22Pair12
    rw [localElement_coe]
    have hc : ∀ i : Fin 6, i ≠ 5 → localPerm i • m22Pair12 = m22Pair12 := by
      decide +kernel
    exact hc i h

private theorem a_word : a = [(localElement 0)⁻¹, (localElement 5)⁻¹, localElement 3, (localElement 5)⁻¹, (localElement 3)⁻¹, (localElement 5)⁻¹, (localElement 4)⁻¹, (localElement 5)⁻¹, localElement 1, localElement 3, localElement 2, (localElement 0)⁻¹, (localElement 1)⁻¹].prod := by
  apply Subtype.ext
  change m22GeneratorA = _
  simp only [List.prod_cons, List.prod_nil, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_one, localElement_coe]
  decide +kernel

private theorem a_mem_join : a ∈ first ⊔ second := by
  rw [a_word]
  apply (first ⊔ second).list_prod_mem
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (first ⊔ second).inv_mem (localElement_mem 0)
  · exact (first ⊔ second).inv_mem (localElement_mem 5)
  · exact localElement_mem 3
  · exact (first ⊔ second).inv_mem (localElement_mem 5)
  · exact (first ⊔ second).inv_mem (localElement_mem 3)
  · exact (first ⊔ second).inv_mem (localElement_mem 5)
  · exact (first ⊔ second).inv_mem (localElement_mem 4)
  · exact (first ⊔ second).inv_mem (localElement_mem 5)
  · exact localElement_mem 1
  · exact localElement_mem 3
  · exact localElement_mem 2
  · exact (first ⊔ second).inv_mem (localElement_mem 0)
  · exact (first ⊔ second).inv_mem (localElement_mem 1)

private theorem b_word : b = [localElement 0, (localElement 3)⁻¹, (localElement 1)⁻¹, localElement 5, localElement 4, localElement 5, localElement 3, localElement 0, localElement 5, (localElement 3)⁻¹, localElement 0].prod := by
  apply Subtype.ext
  change m22GeneratorB = _
  simp only [List.prod_cons, List.prod_nil, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_one, localElement_coe]
  decide +kernel

private theorem b_mem_join : b ∈ first ⊔ second := by
  rw [b_word]
  apply (first ⊔ second).list_prod_mem
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact localElement_mem 0
  · exact (first ⊔ second).inv_mem (localElement_mem 3)
  · exact (first ⊔ second).inv_mem (localElement_mem 1)
  · exact localElement_mem 5
  · exact localElement_mem 4
  · exact localElement_mem 5
  · exact localElement_mem 3
  · exact localElement_mem 0
  · exact localElement_mem 5
  · exact (first ⊔ second).inv_mem (localElement_mem 3)
  · exact localElement_mem 0

public theorem first_sup_second : first ⊔ second = ⊤ := by
  apply Subgroup.map_injective M22.subtype_injective
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply le_antisymm (Subgroup.map_subtype_le _)
  conv_lhs => rw [← m22Atlas_eq_M22, m22Atlas_eq_closure]
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact ⟨a, a_mem_join, rfl⟩
  · exact ⟨b, b_mem_join, rfl⟩

public theorem outerFirst_sup_outerSecond : outerFirst ⊔ outerSecond = ⊤ := by
  let P := outerFirst ⊔ outerSecond
  have hi : inner ≤ P := by
    rw [← inclusion_range, MonoidHom.range_eq_map, ← first_sup_second,
      Subgroup.map_sup, map_first, map_second]
    exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
  let o : m22DesignAut := ⟨m22OddPairSwap, m22OddPairSwap_mem_designAut⟩
  have ho : o ∈ outerFirst := by
    change m22OddPairSwap • m22Pair12 = m22Pair12
    decide +kernel
  have hh (h : M22) : inclusion h ∈ P := hi (by exact h.property)
  apply top_unique
  intro g _
  obtain ⟨h, hg | hg⟩ := m22DesignAut_normalForm g
  · have he : g = inclusion h := Subtype.ext hg
    rw [he]
    exact hh h
  · have he : g = inclusion h * o := Subtype.ext hg
    rw [he]
    exact P.mul_mem (hh h) (mem_sup_left ho)

end Sporadic.Mathieu.M22ValueBound.Concrete
