module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.Coordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus

/-!
# An elementary tail of the positive Ree coordinates

After the main parameters of all four B₂ blocks, the paired parameters of
blocks 2 and 8, and the central parameter of block 1 vanish, the only remaining
curves are x₄, x₆, y₃, y₅ and y₇ (GLS numbering). Their ten split-root factors
have pairwise nonnegative inner products. The checked split-root commutation
relations therefore make the subgroup they generate abelian; each generator
has square one in characteristic two. Consequently every word in this tail
has square one, in the actual split matrix group.

The small integral-vector table proves the root geometry before casting to
real vectors. No matrix enumeration or center-classification hypothesis is
used. The seven vanishing coordinates remain explicit inputs, consumed by
`CenterExponent.unipotent_center_sq_of_coordinate_elimination`.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith, proof of 13.6.6, printed p.927 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.NormalizedRootCentralizers.CenterExponent
open Theory.AlgebraicGroup StandardRootSystem
open Parabolics
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.RadicalCoordinates.FixedCoordinates
open MatrixRelations.LongCommutators Subgroup

private def tailIndex : Fin 10 → Fin 24 := ![16, 17, 10, 11, 15, 14, 21, 20, 9, 8]

private def integralVector : Fin 10 → Fin 4 → ℤ :=
  ![![2,0,0,-2], ![1,1,-1,1], ![2,0,0,2], ![1,1,1,-1], ![2,2,0,0],
    ![2,0,0,0], ![2,0,-2,0], ![1,1,-1,-1], ![2,0,2,0], ![1,1,1,1]]
private theorem geometry (i : Fin 10) :
    V (tailIndex i) = fun k => (integralVector i k : ℝ) / 2 := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    norm_num [tailIndex, V, integralVector]
private theorem integral_nonneg :
    ∀ i j : Fin 10, 0 ≤ ∑ k, integralVector i k * integralVector j k := by decide
private theorem tail_nonneg (i j : Fin 10) : 0 ≤ dot (V (tailIndex i)) (V (tailIndex j)) := by
  rw [geometry, geometry]
  have h : (0 : ℝ) ≤ ∑ k, (integralVector i k : ℝ) * (integralVector j k : ℝ) := by
    exact_mod_cast integral_nonneg i j
  change 0 ≤ ∑ k, (integralVector i k : ℝ) / 2 * ((integralVector j k : ℝ) / 2)
  have he : (∑ k, (integralVector i k : ℝ) / 2 * ((integralVector j k : ℝ) / 2)) =
      (∑ k, (integralVector i k : ℝ) * (integralVector j k : ℝ)) / 4 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  positivity

private def tailGroup (m : ℕ) : Subgroup (SplitGroup m) :=
  closure {x | ∃ i : Fin 10, ∃ t : CoefficientField m, x = X m (tailIndex i) t}

private theorem tail_mul_comm (m : ℕ) : IsMulCommutative (tailGroup m) := by
  apply isMulCommutative_closure
  rintro _ ⟨i, a, rfl⟩ _ ⟨j, b, rfl⟩
  exact (xc m _ _ (tail_nonneg i j) a b).eq

private theorem tail_sq (m : ℕ) (x : SplitGroup m) (hx : x ∈ tailGroup m) : x ^ 2 = 1 := by
  let : IsMulCommutative (tailGroup m) := tail_mul_comm m
  induction hx using closure_induction with
  | mem x hx =>
    obtain ⟨i, t, rfl⟩ := hx
    exact (pow_two _).trans (xx m _ _)
  | one => exact one_pow _
  | mul x y hx hy hxx hyy =>
    have hx' : x ∈ tailGroup m := hx
    have hy' : y ∈ tailGroup m := hy
    have hc : Commute x y := setLike_mul_comm hx' hy'
    rw [hc.mul_pow, hxx, hyy, one_mul]
  | inv x hx hxx => rw [inv_pow, hxx, inv_one]

private theorem tail_mem (m : ℕ) (i : Fin 10) (t : CoefficientField m) :
    X m (tailIndex i) t ∈ tailGroup m := subset_closure ⟨i, t, rfl⟩

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong i), halfFrobenius]

private theorem pair_three_mem (m : ℕ) (t : CoefficientField m) :
    rootWord m 3 t ∈ tailGroup m := by
  have h : rootWord m 3 t = X m 10 t * X m 11 (halfFrobenius m t) := by
    simp only [rootWord, fieldEnd_half]
    change X m 10 t * X m 11 (halfFrobenius m t) * 1 = _
    exact mul_one _
  rw [h]
  exact mul_mem (tail_mem m 2 _) (tail_mem m 3 _)

private theorem pair_five_mem (m : ℕ) (t : CoefficientField m) :
    rootWord m 5 t ∈ tailGroup m := by
  have h : rootWord m 5 t = X m 16 t * X m 17 (halfFrobenius m t) := by
    simp only [rootWord, fieldEnd_half]
    change X m 16 t * X m 17 (halfFrobenius m t) * 1 = _
    exact mul_one _
  rw [h]
  exact mul_mem (tail_mem m 0 _) (tail_mem m 1 _)

private theorem central_two_mem (m : ℕ) (t : CoefficientField m) :
    centralWord m 2 t ∈ tailGroup m := by
  have h : centralWord m 2 t = X m 9 t * X m 8 (halfFrobenius m t) := by
    simp only [centralWord, fieldEnd_half]
    rfl
  rw [h]
  exact mul_mem (tail_mem m 8 _) (tail_mem m 9 _)

private theorem central_four_mem (m : ℕ) (t : CoefficientField m) :
    centralWord m 4 t ∈ tailGroup m := by
  have h : centralWord m 4 t = X m 15 t * X m 14 (halfFrobenius m t) := by
    simp only [centralWord, fieldEnd_half]
    rfl
  rw [h]
  exact mul_mem (tail_mem m 4 _) (tail_mem m 5 _)

private theorem central_six_mem (m : ℕ) (t : CoefficientField m) :
    centralWord m 6 t ∈ tailGroup m := by
  have h : centralWord m 6 t = X m 21 t * X m 20 (halfFrobenius m t) := by
    simp only [centralWord, fieldEnd_half]
    rfl
  rw [h]
  exact mul_mem (tail_mem m 6 _) (tail_mem m 7 _)

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)

private theorem main_zero (m : ℕ) (i : Fin 8) : rootWord m i 0 = 1 := by
  simp [rootWord, root_zero]

private theorem central_zero (m : ℕ) (i : Fin 8) : centralWord m i 0 = 1 := by
  simp [centralWord, root_zero]

private theorem pair_mem (m : ℕ) (i : Fin 8) (hi : i.val % 2 ≠ 0)
    (t : CoefficientField m) (hz : i = 1 ∨ i = 7 → t = 0) :
    rootWord m i t ∈ tailGroup m := by
  fin_cases i <;> norm_num at hi
  · rw [hz (Or.inl rfl), main_zero]; exact one_mem _
  · exact pair_three_mem m t
  · exact pair_five_mem m t
  · rw [hz (Or.inr rfl), main_zero]; exact one_mem _

private theorem central_mem (m : ℕ) (i : Fin 8) (hi : i.val % 2 = 0)
    (t : CoefficientField m) (hz : i = 0 → t = 0) :
    centralWord m i t ∈ tailGroup m := by
  fin_cases i <;> norm_num at hi
  · rw [hz rfl, central_zero]; exact one_mem _
  · exact central_two_mem m t
  · exact central_four_mem m t
  · exact central_six_mem m t

/-- After the seven specified coordinates vanish, all remaining split factors
belong to a commuting family of root involutions. -/
theorem positiveWord_sq_of_coordinate_vanishing (m : ℕ) (p : PositiveParameters m)
    (hpair : ∀ j, positiveRootWordLayout.pairIndex j = 1 ∨
      positiveRootWordLayout.pairIndex j = 7 → p.pair j = 0)
    (hmain : ∀ j, p.main j = 0)
    (hcentral : ∀ j, positiveRootWordLayout.quartetIndex j = 0 → p.central j = 0) :
    positiveWord m p ^ 2 = 1 := by
  apply tail_sq
  apply mul_mem
  · apply list_prod_mem
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact pair_mem m _ (positiveRootWordLayout.pair_odd j) _ (hpair j)
  · apply list_prod_mem
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    change Fin 4 at j
    rw [hmain j, main_zero, one_mul]
    exact central_mem m _ (positiveRootWordLayout.quartet_even j) _ (hcentral j)

end ReeF4.NormalizedRootCentralizers.CenterExponent
