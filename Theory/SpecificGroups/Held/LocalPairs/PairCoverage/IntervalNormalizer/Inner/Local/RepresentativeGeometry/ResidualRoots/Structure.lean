module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Words

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.Orbits
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.Planes
public import Theory.GroupTheory.PGroup.GeneratorSeries
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# From the Held word relations to the intrinsic residual core

Order-three generators lie in the relative two-residual. Its normality puts
all ten conjugate letters there. An ascending series of cyclic two-extensions
shows that the eight word generators generate a two-group. The six checked
conjugation tables make this subgroup normal in the pair product, hence in
the actual residual. Its inclusion in the intrinsic two-core then follows
from the defining maximality of that core.
-/

public section
open Subgroup
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots

private theorem evalSigned_mem {G : Type*} [Group G] (H : Subgroup G)
    (g : Fin 10 → G) (hg : ∀ k, g k ∈ H) (w : List (Fin 10 × Bool)) :
    evalSigned g w ∈ H := by
  apply H.list_prod_mem
  intro x hx
  obtain ⟨⟨k, b⟩, _, rfl⟩ := List.mem_map.mp hx
  cases b
  · exact hg k
  · exact H.inv_mem (hg k)

theorem pairGenerator_mem (i : Bool) (j : Fin 2) (k : Fin 6) :
    pairGenerator i j k ∈ pairProduct i j := by
  have ho (t : Fin 2) : LocalActions.evalLocalWord i (LocalActions.oddWord i j t) ∈
      pairProduct i j := mem_sup_left (subset_closure (Set.mem_range_self t))
  have ht (t : Fin 4) : LocalActions.evalLocalWord i (LocalActions.twoWord i j t) ∈
      pairProduct i j := mem_sup_right (subset_closure (Set.mem_range_self t))
  fin_cases k
  · exact ho 0
  · exact ho 1
  · exact ht 0
  · exact ht 1
  · exact ht 2
  · exact ht 3

theorem pairProduct_le_of_generators (i : Bool) (j : Fin 2) (H : Subgroup Held.He)
    (h : ∀ k, pairGenerator i j k ∈ H) : pairProduct i j ≤ H := by
  apply sup_le
  · apply (closure_le _).mpr
    rintro x ⟨k, rfl⟩
    fin_cases k
    · exact h 0
    · exact h 1
  · apply (closure_le _).mpr
    rintro x ⟨k, rfl⟩
    fin_cases k
    · exact h 2
    · exact h 3
    · exact h 4
    · exact h 5

private theorem odd_mem_residual (i : Bool) (j k : Fin 2) :
    LocalActions.RepresentativeImages.oddGenerator i j k ∈
      Held.LocalPairs.residual (LocalActions.candidateTwo i j) (LocalActions.candidateOdd i j) := by
  let x : pairProduct i j := ⟨_, mem_sup_left
    (LocalActions.RepresentativeImages.oddGenerator_mem i j k)⟩
  have hx : x ^ 3 = 1 := Subtype.ext (LocalActions.RepresentativeImages.oddGenerator_cube i j k)
  have hm : x ∈ pResidual 2 (pairProduct i j) :=
    mem_pResidual_of_orderOf_coprime ((show Nat.Coprime 2 3 by decide).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hx))
  exact ⟨x, hm, rfl⟩

private theorem residual_conjugate_mem (i : Bool) (j : Fin 2) (x y : Held.He)
    (hx : x ∈ Held.LocalPairs.residual (LocalActions.candidateTwo i j) (LocalActions.candidateOdd i j))
    (hy : y ∈ pairProduct i j) :
    y * x * y⁻¹ ∈ Held.LocalPairs.residual
      (LocalActions.candidateTwo i j) (LocalActions.candidateOdd i j) := by
  obtain ⟨x, hx, rfl⟩ := hx
  let z : pairProduct i j := ⟨y, hy⟩
  let u : pairProduct i j := x
  exact ⟨z * u * z⁻¹, (inferInstance : (pResidual 2 (pairProduct i j)).Normal).conj_mem u hx z, rfl⟩

theorem generator_mem_residual (i : Bool) (j : Fin 2) (k : Fin 8) :
    generator i j k ∈ Held.LocalPairs.residual
      (LocalActions.candidateTwo i j) (LocalActions.candidateOdd i j) := by
  apply evalSigned_mem
  have ho (t : Fin 2) := odd_mem_residual i j t
  have hc (t : Fin 6) (r : Fin 2) := residual_conjugate_mem i j _ _ (ho r) (pairGenerator_mem i j t)
  intro t
  fin_cases t
  · exact ho 0
  · exact ho 1
  · exact hc 2 0
  · exact hc 2 1
  · exact hc 3 0
  · exact hc 3 1
  · exact hc 4 0
  · exact hc 4 1
  · exact hc 5 0
  · exact hc 5 1

theorem group_le_residual (i : Bool) (j : Fin 2) :
    group i j ≤ Held.LocalPairs.residual
      (LocalActions.candidateTwo i j) (LocalActions.candidateOdd i j) := by
  apply (closure_le _).mpr
  rintro _ ⟨k, rfl⟩
  exact generator_mem_residual i j k

theorem product_mem_group (i : Bool) (j : Fin 2) (w : List (Fin 8)) :
    product i j w ∈ group i j := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  exact subset_closure (Set.mem_range_self k)

private theorem internalWord_lt (i : Bool) (j : Fin 2) :
    ∀ k l : Fin 8, l < k → ∀ t ∈ internalWord i j k l, t < k := by
  cases i <;> fin_cases j <;> decide +kernel

/-- The concrete relation hypotheses concern words, not residual/core membership. -/
theorem group_le_pairTwoCore_of_relations (i : Bool) (j : Fin 2)
    (hfour : ∀ k, generator i j k ^ 4 = 1)
    (hint : ∀ k l, l < k → generator i j k * generator i j l * (generator i j k)⁻¹ =
      product i j (internalWord i j k l))
    (hpair : ∀ k l, pairGenerator i j k * generator i j l * (pairGenerator i j k)⁻¹ =
      product i j (pairConjugateWord i j k l)) :
    group i j ≤ pairTwoCore i j := by
  have hp : IsPGroup 2 (group i j) := by
    apply isPGroup_closure_of_normalizing_generators
    · intro k
      exact ⟨2, hfour k⟩
    · intro k
      apply mem_normalizer_closure_of_conjugates
      rintro x ⟨l, hl, rfl⟩
      rw [hint k l hl]
      apply Subgroup.list_prod_mem
      intro y hy
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
      exact subset_closure ⟨t, internalWord_lt i j k l hl t ht, rfl⟩
  have hn : pairProduct i j ≤ normalizer (group i j : Set Held.He) := by
    apply pairProduct_le_of_generators
    intro k
    apply mem_normalizer_closure_of_conjugates
    rintro x ⟨l, rfl⟩
    rw [hpair]
    exact product_mem_group i j _
  exact le_pCoreIn_of_normalizes hp (group_le_residual i j)
    ((Held.LocalPairs.residual_le _ _).trans hn)

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.ResidualRoots
