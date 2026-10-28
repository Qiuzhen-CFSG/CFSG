module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.OrbitCandidates
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.OrbitTest.Tables

/-!
# Certified coordinates for saturated Held subsets

The listed fibers are strictly increasing, carry their stated labels, and have
sizes summing to 2058. Disjointness and counting therefore prove that they cover
the whole vertex set. Kernel reduction checks the 24 representative degree rows
against `Held.NormalizerGraph.Adj`. Partitioning a saturated subset into fibers
then expresses its size and degrees as the displayed weighted sums.

Only representatives are tested; constancy within each fiber is not required.
Source data: `ThreePrimeOvergroups/Source/orbit_lists.json` and the actual
ATLAS HeG1-p2058B0 graph in `Normalizer/GraphData.lean`.
-/

-- Keep the finite kernel checks sequential to bound peak memory.
set_option Elab.async false

namespace Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.OrbitTest
public section

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem lists_sorted : ∀ i : Fin 24, (fiberList i).IsChain (· < ·) := by decide +kernel

private theorem lists_nodup (i : Fin 24) : (fiberList i).Nodup := (lists_sorted i).pairwise.nodup

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem lists_labels : ∀ i : Fin 24,
    (fiberList i).all (fun x => orbitLabel x == i.val) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem lists_lengths : ∀ i : Fin 24, (fiberList i).length = weights i := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem representatives_labels : ∀ i : Fin 24, orbitLabel (representative i) = i.val := by
  decide +kernel

theorem representative_zero : representative 0 = basepoint := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row0 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 0) x)) = matrix 0 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row1 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 1) x)) = matrix 1 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row2 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 2) x)) = matrix 2 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row3 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 3) x)) = matrix 3 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row4 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 4) x)) = matrix 4 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row5 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 5) x)) = matrix 5 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row6 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 6) x)) = matrix 6 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row7 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 7) x)) = matrix 7 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row8 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 8) x)) = matrix 8 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row9 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 9) x)) = matrix 9 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row10 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 10) x)) = matrix 10 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row11 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 11) x)) = matrix 11 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row12 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 12) x)) = matrix 12 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row13 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 13) x)) = matrix 13 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row14 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 14) x)) = matrix 14 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row15 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 15) x)) = matrix 15 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row16 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 16) x)) = matrix 16 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row17 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 17) x)) = matrix 17 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row18 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 18) x)) = matrix 18 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row19 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 19) x)) = matrix 19 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row20 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 20) x)) = matrix 20 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row21 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 21) x)) = matrix 21 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row22 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 22) x)) = matrix 22 j := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem row23 : ∀ j : Fin 24, (fiberList j).countP (fun x => decide
    (Held.NormalizerGraph.Adj (representative 23) x)) = matrix 23 j := by decide +kernel

@[expose] def fiber (i : Fin 24) : Finset (Fin 2058) := (fiberList i).toFinset

theorem fiber_label (i : Fin 24) {x : Fin 2058} (hx : x ∈ fiber i) :
    orbitLabel x = i.val := by
  exact beq_iff_eq.mp ((List.all_eq_true.mp (lists_labels i)) x (List.mem_toFinset.mp hx))

theorem card_fiber (i : Fin 24) : (fiber i).card = weights i := by
  rw [fiber, List.toFinset_card_of_nodup (lists_nodup i), lists_lengths]

open scoped BigOperators

theorem fibers_cover : Finset.univ.biUnion fiber = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_biUnion]
  · simp only [card_fiber]
    decide +kernel
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    exact hij (Fin.ext ((fiber_label i hxi).symm.trans (fiber_label j hxj)))

theorem mem_fiber (i : Fin 24) (x : Fin 2058) : x ∈ fiber i ↔ orbitLabel x = i.val := by
  refine ⟨fiber_label i, ?_⟩
  intro hx
  have hm : x ∈ Finset.univ.biUnion fiber := by rw [fibers_cover]; exact Finset.mem_univ x
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hm
  have he : j = i := Fin.ext ((fiber_label j hj).symm.trans hx)
  exact he ▸ hj

theorem count_fiber (i j : Fin 24) : neighborCount (fiber j) (representative i) = matrix i j := by
  rw [neighborCount, fiber, (lists_nodup j).card_eq_countP]
  fin_cases i
  · exact row0 j
  · exact row1 j
  · exact row2 j
  · exact row3 j
  · exact row4 j
  · exact row5 j
  · exact row6 j
  · exact row7 j
  · exact row8 j
  · exact row9 j
  · exact row10 j
  · exact row11 j
  · exact row12 j
  · exact row13 j
  · exact row14 j
  · exact row15 j
  · exact row16 j
  · exact row17 j
  · exact row18 j
  · exact row19 j
  · exact row20 j
  · exact row21 j
  · exact row22 j
  · exact row23 j

/-- Saturation lets a representative decide membership in an entire fiber. -/
theorem mem_iff_representative (U : Finset (Fin 2058))
    (hsat : ∀ x ∈ U, ∀ y, orbitLabel x = orbitLabel y → y ∈ U)
    (i : Fin 24) (x : Fin 2058) (hx : orbitLabel x = i.val) :
    x ∈ U ↔ representative i ∈ U := by
  constructor
  · intro h
    exact hsat x h (representative i) (hx.trans (representatives_labels i).symm)
  · intro h
    exact hsat (representative i) h x ((representatives_labels i).trans hx.symm)

open scoped BigOperators

theorem filter_card_eq_sum (U : Finset (Fin 2058))
    (hsat : ∀ x ∈ U, ∀ y, orbitLabel x = orbitLabel y → y ∈ U)
    (p : Fin 2058 → Prop) [DecidablePred p] :
    (U.filter p).card = ∑ i : Fin 24,
      if representative i ∈ U then ((fiber i).filter p).card else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun x : Fin 2058 => (⟨orbitLabel x, orbitLabel_lt x⟩ : Fin 24))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : representative i ∈ U
  · rw [if_pos hi]
    congr 1
    ext x
    simp only [Finset.mem_filter, mem_fiber]
    constructor
    · rintro ⟨⟨_, hp⟩, he⟩
      exact ⟨congrArg Fin.val he, hp⟩
    · rintro ⟨he, hp⟩
      exact ⟨⟨(mem_iff_representative U hsat i x he).mpr hi, hp⟩, Fin.ext he⟩
  · rw [if_neg hi, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [Finset.mem_filter] at hx
    exact hi ((mem_iff_representative U hsat i x (congrArg Fin.val hx.2)).mp hx.1.1)

@[expose] def selection (U : Finset (Fin 2058)) (i : Fin 24) : ℕ :=
  if representative i ∈ U then 1 else 0

theorem selection_le_one (U : Finset (Fin 2058)) (i : Fin 24) : selection U i ≤ 1 := by
  unfold selection
  split <;> omega

theorem selection_card (U : Finset (Fin 2058))
    (hsat : ∀ x ∈ U, ∀ y, orbitLabel x = orbitLabel y → y ∈ U) :
    U.card = ∑ i : Fin 24, weights i * selection U i := by
  simpa only [Finset.filter_true, card_fiber, selection, mul_ite, mul_one, mul_zero]
    using filter_card_eq_sum U hsat (fun _ => True)

theorem selection_count (U : Finset (Fin 2058))
    (hsat : ∀ x ∈ U, ∀ y, orbitLabel x = orbitLabel y → y ∈ U) (i : Fin 24) :
    neighborCount U (representative i) = ∑ j : Fin 24, matrix i j * selection U j := by
  change (U.filter (Held.NormalizerGraph.Adj (representative i))).card = _
  rw [filter_card_eq_sum U hsat]
  apply Finset.sum_congr rfl
  intro j _
  change (if representative j ∈ U then neighborCount (fiber j) (representative i) else 0) = _
  rw [count_fiber]
  simp only [selection, mul_ite, mul_one, mul_zero]

end
end Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.OrbitTest
