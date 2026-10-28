module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelLower.RelationTests
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.GeneratorLiftCertificate.Interpretation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.SourceActions
public import Theory.GroupTheory.BinaryCollection

/-!
# Binary collection for the last three Fi23 suffix points

Six commuting involutions have at most 64 ordered binary products. Checking
their images at 78, 86 and 108 leaves only products 0 and 10. The latter must
still be identified with the exact ATLAS candidate. The two premises below
are precisely the remaining full-permutation table checks: commutation of the
six generators and identification of product 10 with the checked candidate map.

This is a conditional certificate consumer for the Fi23 restriction kernel,
GLS3 Table 5.3u; it does not assert the outstanding numerical identities.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerData
open Theory.GroupTheory.BinaryCollection

def normalForm (n : Fin 64) : Equiv.Perm (Fin 31671) :=
  product (List.ofFn afterFourGenerator) n.val

private theorem triangular_of_commuting {G : Type*} [Group G] (l : List G)
    (hs : ∀ a ∈ l, a * a = 1) (hc : ∀ a ∈ l, ∀ b ∈ l, a * b = b * a) :
    triangular l := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    refine ⟨?_, ?_, ih (fun b hb => hs b (List.mem_cons_of_mem _ hb))
      (fun b hb c hc' => hc b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc'))⟩
    · rw [hs a List.mem_cons_self]
      exact Subgroup.one_mem _
    · intro b hb
      have he : a⁻¹ * b * a = b := by
        rw [mul_assoc, ← hc a List.mem_cons_self b (List.mem_cons_of_mem _ hb),
          inv_mul_cancel_left]
      rw [he]
      exact Subgroup.subset_closure hb

theorem normalForm_cover
    (hcomm : ∀ i j, afterFourGenerator i * afterFourGenerator j =
      afterFourGenerator j * afterFourGenerator i)
    {p : Equiv.Perm (Fin 31671)} (hp : p ∈ afterFour) :
    ∃ n : Fin 64, normalForm n = p := by
  have ht : triangular (List.ofFn afterFourGenerator) := by
    apply triangular_of_commuting
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact afterFourGenerator_square i
    · intro a ha b hb
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
      exact hcomm i j
  obtain ⟨n, hn, he⟩ := cover (List.ofFn afterFourGenerator) ht p (by
    simpa only [afterFour, List.mem_ofFn', Set.ofPred_mem_eq] using hp)
  exact ⟨⟨n, by simpa using hn⟩, he⟩

theorem normalForm_zero : normalForm 0 = 1 := by
  simp [normalForm, List.ofFn_succ, product]

theorem normalForm_ten : normalForm 10 = afterFourGenerator 1 * afterFourGenerator 3 := by
  simp [normalForm, List.ofFn_succ, product]

theorem normalForm_fixed_test (n : Fin 64) :
    (normalForm n 78 = 78 ∧ normalForm n 86 = 86 ∧ normalForm n 108 = 108) →
      n = 0 ∨ n = 10 := by
  revert n
  decide +kernel

theorem afterFour_tail_bound_of_relations
    (hcomm : ∀ i j, afterFourGenerator i * afterFourGenerator j =
      afterFourGenerator j * afterFourGenerator i)
    (htarget : ∀ x, afterFourGenerator 1 (afterFourGenerator 3 x) =
      GeneratorLiftCertificate.candidateMap x)
    (p : Equiv.Perm (Fin 31671)) (hp : p ∈ afterFour)
    (h78 : p 78 = 78) (h86 : p 86 = 86) (h108 : p 108 = 108) :
    p = 1 ∨ p = inclusion candidate := by
  obtain ⟨n, rfl⟩ := normalForm_cover hcomm hp
  rcases normalForm_fixed_test n ⟨h78, h86, h108⟩ with h | h
  · exact Or.inl (h ▸ normalForm_zero)
  · right
    rw [h, normalForm_ten]
    apply Equiv.ext
    intro x
    change afterFourGenerator 1 (afterFourGenerator 3 x) = inclusion candidate x
    rw [htarget]
    exact GeneratorLiftCertificate.candidateMap_eq_inclusion_candidate
      Fi24Prime.Fi23Lift.Certificate.generatorA_apply_eq_sourceA
      Fi24Prime.Fi23Lift.Certificate.generatorB_apply_eq_sourceB x

/-- Balanced certificates discharge the two numerical premises of the actual
three-point bound. -/
theorem afterFour_tail_bound_of_checks
    (hcomm : ∀ i j, Fi24Prime.Fi23Lift.Certificate.checkPow (commutationTest i j) 0 15 = true)
    (htarget : Fi24Prime.Fi23Lift.Certificate.checkPow candidateTest 0 15 = true)
    (p : Equiv.Perm (Fin 31671)) (hp : p ∈ afterFour)
    (h78 : p 78 = 78) (h86 : p 86 = 86) (h108 : p 108 = 108) :
    p = 1 ∨ p = inclusion candidate :=
  afterFour_tail_bound_of_relations (fun i j => commute_of_checked i j (hcomm i j))
    (candidate_eq_of_checked htarget) p hp h78 h86 h108

end Sporadic.Fischer.Fi23.CentralizerSection.KernelLowerData
