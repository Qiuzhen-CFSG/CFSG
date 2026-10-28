module

public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Coordinates

/-!
# Concrete five-dimensional overgroups in 13.8.25

The nodes are numbered from zero, and a node deletes the cut of dimension
one greater than its index. Adjacent basis swaps detect the deleted cuts,
so adding nodes gives strict inclusions of the actual flag stabilizers.
Every single node has a nonadjacent partner. For the marked pair at the
first and third nodes, deleting the last remaining end cut constructs the
two-space stabilizer with diagonal blocks of sizes two and three. The
reversed orientation is retained as well.

These are the geometric constructions used in Aschbacher–Smith 13.8.25,
combined manuscript of 1 March 2004, printed pp.959–960 (PDF pp.976–977).
The corresponding two-core quotient calculations, the source marking,
and the restrictions imposed by its normalizers remain separate proof
obligations. No source-theorem assertion is made by these containments.
-/

@[expose] public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

/-- Nodes are indexed from zero: node `i` deletes the cut of dimension `i+1`. -/
noncomputable def fiveParabolic (b : FiveBasis) (nodes : Set (Fin 4)) :
    Subgroup (LinearGroup 5) := flagStabilizer b nodesᶜ

private noncomputable def swapNode (b : FiveBasis) (i : Fin 4) : LinearGroup 5 :=
  b.equiv b (Equiv.swap i.castSucc i.succ)

private theorem swapNode_mem (b : FiveBasis) (cuts : Set (Fin 4)) (i : Fin 4) :
    swapNode b i ∈ flagStabilizer b cuts ↔ i ∉ cuts := by
  classical
  constructor
  · intro h hi
    have hv := ((mem_flagStabilizer_iff b cuts _).mp h i hi (b i.castSucc)).mpr
      ((basis_mem_flagSpace_iff b i _).mpr le_rfl)
    rw [swapNode, Module.Basis.equiv_apply, Equiv.swap_apply_left,
      basis_mem_flagSpace_iff] at hv
    simp at hv
  · intro hi
    rw [mem_flagStabilizer_iff_maps]
    intro j hj v hv
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    have hle : flagSpace b j ≤ (flagSpace b j).comap (swapNode b i).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      change swapNode b i (b k) ∈ flagSpace b j
      rw [swapNode, Module.Basis.equiv_apply, basis_mem_flagSpace_iff]
      by_cases hki : k = i.castSucc
      · subst k
        rw [Equiv.swap_apply_left]
        simp only [Fin.val_succ]
        have : j.val ≠ i.val := fun h => hji (Fin.ext h)
        change i.val ≤ j.val at hk
        omega
      · by_cases hks : k = i.succ
        · subst k
          rw [Equiv.swap_apply_right]
          simp only [Fin.val_castSucc]
          change i.val + 1 ≤ j.val at hk
          omega
        · rw [Equiv.swap_apply_of_ne_of_ne hki hks]
          exact hk
    exact hle hv

/-- The actual stabilizers detect their node sets, by adjacent basis swaps. -/
theorem fiveParabolic_le_iff (b : FiveBasis) (s t : Set (Fin 4)) :
    fiveParabolic b s ≤ fiveParabolic b t ↔ s ⊆ t := by
  classical
  constructor
  · intro h i hi
    by_contra hn
    have hs : swapNode b i ∈ fiveParabolic b s :=
      (swapNode_mem b sᶜ i).mpr (by simpa using hi)
    exact ((swapNode_mem b tᶜ i).mp (h hs)) hn
  · intro h
    exact flagStabilizer_antitone b (Set.compl_subset_compl.mpr h)

theorem fiveParabolic_lt_iff (b : FiveBasis) (s t : Set (Fin 4)) :
    fiveParabolic b s < fiveParabolic b t ↔ s ⊂ t := by
  rw [lt_iff_le_not_ge, fiveParabolic_le_iff, fiveParabolic_le_iff]
  rfl

/-- The complete flag is contained in every constructed parabolic. -/
theorem fullFlag_le_fiveParabolic (b : FiveBasis) (nodes : Set (Fin 4)) :
    flagStabilizer b Set.univ ≤ fiveParabolic b nodes :=
  flagStabilizer_antitone b (Set.subset_univ _)

/-- Every node of A₄ has a distinct nonadjacent node. -/
theorem exists_nonadjacent_five_node (i : Fin 4) :
    ∃ j : Fin 4, i.val + 1 < j.val ∨ j.val + 1 < i.val := by
  fin_cases i
  · exact ⟨2, Or.inl (by decide)⟩
  · exact ⟨3, Or.inl (by decide)⟩
  · exact ⟨0, Or.inr (by decide)⟩
  · exact ⟨0, Or.inr (by decide)⟩

/-- The overgroup in the single-node degree-five branch is constructed by
adding a nonadjacent node. Its quotient calculation is a separate obligation. -/
theorem five_single_node_overgroup (b : FiveBasis) (i : Fin 4) :
    ∃ j : Fin 4, (i.val + 1 < j.val ∨ j.val + 1 < i.val) ∧
      fiveParabolic b {i} < fiveParabolic b {i, j} := by
  obtain ⟨j, hj⟩ := exists_nonadjacent_five_node i
  have hne : j ≠ i := by intro he; subst j; omega
  refine ⟨j, hj, (fiveParabolic_lt_iff b _ _).mpr ?_⟩
  simpa only [Set.pair_comm] using
    (Set.ssubset_insert (s := {i}) (a := j) (by simpa using hne))

/-- With the source markings at the first and third nodes, adjoining the
fourth node gives the actual two-space stabilizer, with block sizes 2 and 3. -/
theorem five_first_third_overgroup (b : FiveBasis) :
    fiveParabolic b ({0, 2} : Set (Fin 4)) < flagStabilizer b {1} := by
  have hc : ({1} : Set (Fin 4)) = ({0, 2, 3} : Set (Fin 4))ᶜ := by
    ext i
    fin_cases i <;> simp
  rw [hc]
  exact (fiveParabolic_lt_iff b _ _).mpr (by
    simp only [Set.ssubset_def, Set.subset_def]
    decide)

/-- The reversed marking gives the three-space stabilizer, with block sizes
3 and 2. Both orientations of the diagram are retained. -/
theorem five_second_fourth_overgroup (b : FiveBasis) :
    fiveParabolic b ({1, 3} : Set (Fin 4)) < flagStabilizer b {2} := by
  have hc : ({2} : Set (Fin 4)) = ({0, 1, 3} : Set (Fin 4))ᶜ := by
    ext i
    fin_cases i <;> simp
  rw [hc]
  exact (fiveParabolic_lt_iff b _ _).mpr (by
    simp only [Set.ssubset_def, Set.subset_def]
    decide)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
