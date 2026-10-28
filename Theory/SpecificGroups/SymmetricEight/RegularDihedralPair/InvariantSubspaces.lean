module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.NativeSquareAction
public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.PairConjugacy
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic

/-!
# Invariant subspaces of the native order-168 square action

The finite certificate separates the four nonzero vector orbits of the marked
order-168 subgroup.  The two seven-point orbits are the nonzero points of two
singular three-spaces; the other two orbits contain six independent vectors.
This is used only through the actual deleted-eight action, so no abstract
natural/dual splitting is assumed by consumers.
-/

@[expose] public noncomputable section
open scoped BigOperators
open Equiv Subgroup
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.SquareModule
open ClassicalOrthogonal

abbrev D3 := Fin 3 → F

private def v5 : D := Sum.elim ![1,0,1] ![0,0,0]
private def v8 : D := Sum.elim ![0,0,0] ![1,0,0]
private def v1 : D := Sum.elim ![1,0,0] ![0,0,0]
private def v9 : D := Sum.elim ![1,0,0] ![1,0,0]

def graphMap : D3 →ₗ[F] D :=
  { toFun := fun x => Sum.elim ![x 0 + x 1, x 2, x 0] ![x 2, x 1, x 2]
    map_add' := by
      intro x y
      funext i
      rcases i with i | i <;> fin_cases i <;>
        simp [Pi.add_apply, add_assoc, add_left_comm, add_comm]
    map_smul' := by
      intro a x
      funext i
      rcases i with i | i <;> fin_cases i <;>
        simp [Pi.smul_apply, mul_add] }

def rightMap : D3 →ₗ[F] D :=
  { toFun := fun x => Sum.elim ![0,0,0] x
    map_add' := by
      intro x y
      funext i
      rcases i with i | i <;> fin_cases i <;> simp [Pi.add_apply]
    map_smul' := by
      intro a x
      funext i
      rcases i with i | i <;> fin_cases i <;> simp [Pi.smul_apply] }

def graphPlane : Submodule F D := LinearMap.range graphMap
def rightPlane : Submodule F D := LinearMap.range rightMap

private theorem graphMap_injective : Function.Injective graphMap := by
  intro x y h
  revert x y
  decide +kernel

private theorem rightMap_injective : Function.Injective rightMap := by
  intro x y h
  revert x y
  decide +kernel

private theorem graphPlane_finrank : Module.finrank F graphPlane = 3 := by
  rw [graphPlane, LinearMap.finrank_range_of_inj graphMap_injective]
  simp [D3]

private theorem rightPlane_finrank : Module.finrank F rightPlane = 3 := by
  rw [rightPlane, LinearMap.finrank_range_of_inj rightMap_injective]
  simp [D3]

private theorem graphPlane_singular (v : D) (hv : v ∈ graphPlane) :
    formD 3 F v = 0 := by
  obtain ⟨x, rfl⟩ := hv
  revert x
  decide +kernel

private theorem rightPlane_singular (v : D) (hv : v ∈ rightPlane) :
    formD 3 F v = 0 := by
  obtain ⟨x, rfl⟩ := hv
  revert x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem vector_cases : ∀ v : D,
    (∃ x : D3, graphMap x = v) ∨ (∃ x : D3, rightMap x = v) ∨
    (∃ i : Fin 168, nativeAction (modelWord i) v = v1) ∨
    (∃ i : Fin 168, nativeAction (modelWord i) v = v9) := by
  decide +kernel

private theorem nativeAction_inv_apply (g : P8) (v : D) :
    nativeAction g⁻¹ (nativeAction g v) = v := by
  rw [nativeAction_eq, nativeAction_eq, map_inv]
  change (BinaryD3Comparison.symmetricEquiv g).val.symm
    ((BinaryD3Comparison.symmetricEquiv g).val v) = v
  exact (BinaryD3Comparison.symmetricEquiv g).val.symm_apply_apply v

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem graph_orbit (x : D3) (hx : x ≠ 0) :
    ∃ i : Fin 168, nativeAction (modelWord i) v5 = graphMap x := by
  decide +revert +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem right_orbit (x : D3) (hx : x ≠ 0) :
    ∃ i : Fin 168, nativeAction (modelWord i) v8 = rightMap x := by
  decide +revert +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem graph_stable (i : Fin 168) (x : D3) :
    ∃ y : D3, nativeAction (modelWord i) (graphMap x) = graphMap y := by
  decide +revert +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem right_stable (i : Fin 168) (x : D3) :
    ∃ y : D3, nativeAction (modelWord i) (rightMap x) = rightMap y := by
  decide +revert +kernel

private def orbitBasis21 : Fin 6 → D := ![
  Sum.elim ![1,0,0] ![0,0,0],
  Sum.elim ![0,1,0] ![0,0,0],
  Sum.elim ![0,0,1] ![0,0,0],
  Sum.elim ![0,1,0] ![1,0,0],
  Sum.elim ![1,0,1] ![0,1,0],
  Sum.elim ![1,0,0] ![0,0,1]]

private def orbitBasis28 : Fin 6 → D := ![
  Sum.elim ![1,0,0] ![1,0,0],
  Sum.elim ![1,1,0] ![1,0,0],
  Sum.elim ![1,0,1] ![1,0,0],
  Sum.elim ![0,1,0] ![0,1,0],
  Sum.elim ![1,1,0] ![0,1,0],
  Sum.elim ![0,0,1] ![0,0,1]]

private theorem orbitBasis21_independent : LinearIndependent F orbitBasis21 := by
  rw [Fintype.linearIndependent_iff]
  decide +kernel

private theorem orbitBasis28_independent : LinearIndependent F orbitBasis28 := by
  rw [Fintype.linearIndependent_iff]
  decide +kernel

private theorem orbitBasis21_span_top :
    Submodule.span F (Set.range orbitBasis21) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card orbitBasis21_independent, vectorD_finrank]
  decide

private theorem orbitBasis28_span_top :
    Submodule.span F (Set.range orbitBasis28) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card orbitBasis28_independent, vectorD_finrank]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem orbitBasis21_reachable :
    ∀ j : Fin 6, ∃ i : Fin 168,
      nativeAction (modelWord i) v1 = orbitBasis21 j := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem orbitBasis28_reachable :
    ∀ j : Fin 6, ∃ i : Fin 168,
      nativeAction (modelWord i) v9 = orbitBasis28 j := by
  decide +kernel

private theorem graph_le_of_mem_rep (S : Submodule F D)
    (hS : ∀ g, g ∈ modelGroup → ∀ v, v ∈ S → nativeAction g v ∈ S)
    (hv5 : v5 ∈ S) : graphPlane ≤ S := by
  rintro _ ⟨x, rfl⟩
  by_cases hx : x = 0
  · subst x
    simpa only [map_zero] using S.zero_mem
  · obtain ⟨i, hi⟩ := graph_orbit x hx
    rw [← hi]
    exact hS (modelWord i) (modelWord_mem i) v5 hv5

private theorem right_le_of_mem_rep (S : Submodule F D)
    (hS : ∀ g, g ∈ modelGroup → ∀ v, v ∈ S → nativeAction g v ∈ S)
    (hv8 : v8 ∈ S) : rightPlane ≤ S := by
  rintro _ ⟨x, rfl⟩
  by_cases hx : x = 0
  · subst x
    simpa only [map_zero] using S.zero_mem
  · obtain ⟨i, hi⟩ := right_orbit x hx
    rw [← hi]
    exact hS (modelWord i) (modelWord_mem i) v8 hv8

private theorem top_of_mem_orbitBasis (S : Submodule F D)
    (hS : ∀ g, g ∈ modelGroup → ∀ v, v ∈ S → nativeAction g v ∈ S)
    (hv : v1 ∈ S) : S = ⊤ := by
  have hle : Submodule.span F (Set.range orbitBasis21) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := orbitBasis21_reachable j
    rw [← hi]
    exact hS (modelWord i) (modelWord_mem i) v1 hv
  rw [orbitBasis21_span_top] at hle
  exact top_unique hle

private theorem top_of_mem_orbitBasis28 (S : Submodule F D)
    (hS : ∀ g, g ∈ modelGroup → ∀ v, v ∈ S → nativeAction g v ∈ S)
    (hv : v9 ∈ S) : S = ⊤ := by
  have hle : Submodule.span F (Set.range orbitBasis28) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨i, hi⟩ := orbitBasis28_reachable j
    rw [← hi]
    exact hS (modelWord i) (modelWord_mem i) v9 hv
  rw [orbitBasis28_span_top] at hle
  exact top_unique hle

private theorem rep_one_mem_of_graph_and_right (S : Submodule F D)
    (hgraph : graphPlane ≤ S) (hright : rightPlane ≤ S) : v1 ∈ S := by
  have hg : graphMap (![0,1,0] : D3) ∈ S := hgraph ⟨_, rfl⟩
  have hr : rightMap (![0,1,0] : D3) ∈ S := hright ⟨_, rfl⟩
  have heq : v1 = graphMap (![0,1,0] : D3) + rightMap (![0,1,0] : D3) := by
    decide +kernel
  rw [heq]
  exact S.add_mem hg hr

private theorem proper_eq_plane (S : Submodule F D)
    (hS : ∀ g, g ∈ modelGroup → ∀ v, v ∈ S → nativeAction g v ∈ S)
    (h0 : S ≠ ⊥) (h1 : S ≠ ⊤) : S = graphPlane ∨ S = rightPlane := by
  have hcover : ∀ v ∈ S, v ∈ graphPlane ∨ v ∈ rightPlane := by
    intro v hv
    rcases vector_cases v with hg | hr | ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl hg
    · exact Or.inr hr
    · exact False.elim (h1 (top_of_mem_orbitBasis S hS
        (hi ▸ hS (modelWord i) (modelWord_mem i) v hv)))
    · exact False.elim (h1 (top_of_mem_orbitBasis28 S hS
        (hi ▸ hS (modelWord i) (modelWord_mem i) v hv)))
  have hupper : S ≤ graphPlane ∨ S ≤ rightPlane := by
    by_cases hg : S ≤ graphPlane
    · exact Or.inl hg
    · right
      obtain ⟨x, hx, hxg⟩ : ∃ x ∈ S, x ∉ graphPlane := by
        classical
        by_contra hn
        apply hg
        intro x hx
        by_contra hxg
        exact hn ⟨x, hx, hxg⟩
      have hxr := (hcover x hx).resolve_left hxg
      intro y hy
      rcases hcover y hy with hyg | hyr
      · by_contra hyr
        rcases hcover (x + y) (S.add_mem hx hy) with hxy | hxy
        · exact hxg (by simpa only [add_sub_cancel_right] using graphPlane.sub_mem hxy hyg)
        · exact hyr (by simpa only [add_sub_cancel_left] using rightPlane.sub_mem hxy hxr)
      · exact hyr
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hlower : graphPlane ≤ S ∨ rightPlane ≤ S := by
    rcases vector_cases v with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨i, hi⟩ | ⟨i, hi⟩
    · have hx : x ≠ 0 := fun he => hv0 (he ▸ graphMap.map_zero)
      obtain ⟨i, hi⟩ := graph_orbit x hx
      have hm := hS (modelWord i)⁻¹ (modelGroup.inv_mem (modelWord_mem i)) _ hv
      rw [← hi, nativeAction_inv_apply] at hm
      exact Or.inl (graph_le_of_mem_rep S hS hm)
    · have hx : x ≠ 0 := fun he => hv0 (he ▸ rightMap.map_zero)
      obtain ⟨i, hi⟩ := right_orbit x hx
      have hm := hS (modelWord i)⁻¹ (modelGroup.inv_mem (modelWord_mem i)) _ hv
      rw [← hi, nativeAction_inv_apply] at hm
      exact Or.inr (right_le_of_mem_rep S hS hm)
    · exact False.elim (h1 (top_of_mem_orbitBasis S hS
        (hi ▸ hS (modelWord i) (modelWord_mem i) v hv)))
    · exact False.elim (h1 (top_of_mem_orbitBasis28 S hS
        (hi ▸ hS (modelWord i) (modelWord_mem i) v hv)))
  rcases hupper with hg | hr <;> rcases hlower with hg' | hr'
  · exact Or.inl (le_antisymm hg hg')
  · have hbad : v8 ∈ graphPlane := hg (hr' (show v8 ∈ rightPlane from ⟨![1,0,0], by decide +kernel⟩))
    have hn : ¬ ∃ x : D3, graphMap x = v8 := by decide +kernel
    exact False.elim (hn hbad)
  · have hbad : v5 ∈ rightPlane := hr (hg' (show v5 ∈ graphPlane from ⟨![1,0,0], by decide +kernel⟩))
    have hn : ¬ ∃ x : D3, rightMap x = v5 := by decide +kernel
    exact False.elim (hn hbad)
  · exact Or.inr (le_antisymm hr hr')

/-- The native model has only zero, the two singular planes, and the whole space as invariant subspaces. -/
theorem invariant_subspace_cases (S : Submodule F D)
    (hS : ∀ g, g ∈ modelGroup → ∀ v, v ∈ S → nativeAction g v ∈ S) :
    S = ⊥ ∨ S = graphPlane ∨ S = rightPlane ∨ S = ⊤ := by
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  by_cases h1 : S = ⊤
  · exact Or.inr (Or.inr (Or.inr h1))
  rcases proper_eq_plane S hS h0 h1 with hg | hr
  · exact Or.inr (Or.inl hg)
  · exact Or.inr (Or.inr (Or.inl hr))

/-- Every proper nonzero native invariant subspace has dimension three and is singular. -/
theorem invariant_subspace_finrank_three_singular (S : Submodule F D)
    (hS : ∀ g, g ∈ modelGroup → ∀ v, v ∈ S → nativeAction g v ∈ S)
    (h0 : S ≠ ⊥) (h1 : S ≠ ⊤) :
    Module.finrank F S = 3 ∧ ∀ v ∈ S, formD 3 F v = 0 := by
  rcases proper_eq_plane S hS h0 h1 with rfl | rfl
  · exact ⟨graphPlane_finrank, graphPlane_singular⟩
  · exact ⟨rightPlane_finrank, rightPlane_singular⟩

/-- An actual invariant singular plane for the marked model. -/
theorem exists_model_invariant_singular_plane :
    ∃ S : Submodule F D, Module.finrank F S = 3 ∧
      (∀ g, g ∈ modelGroup → ∀ v ∈ S,
        (BinaryD3Comparison.symmetricEquiv g).val v ∈ S) ∧
      (∀ v ∈ S, formD 3 F v = 0) := by
  refine ⟨graphPlane, graphPlane_finrank, ?_, graphPlane_singular⟩
  intro g hg v hv
  obtain ⟨i, rfl⟩ := (mem_modelGroup g).mp hg
  obtain ⟨x, rfl⟩ := hv
  obtain ⟨y, hy⟩ := graph_stable i x
  exact ⟨y, hy.symm.trans (nativeAction_eq _ _)⟩

set_option maxRecDepth 100000 in
private theorem graph_faithful (i : Fin 168)
    (hi : ∀ x : D3, nativeAction (modelWord i) (graphMap x) = graphMap x) :
    modelWord i = 1 := by
  decide +revert +kernel

set_option maxRecDepth 100000 in
private theorem right_faithful (i : Fin 168)
    (hi : ∀ x : D3, nativeAction (modelWord i) (rightMap x) = rightMap x) :
    modelWord i = 1 := by
  decide +revert +kernel

/-- Restriction of the actual model action to either nonzero proper constituent is faithful. -/
theorem invariant_subspace_faithful (S : Submodule F D)
    (hS : ∀ g, g ∈ modelGroup → ∀ v ∈ S, nativeAction g v ∈ S)
    (h0 : S ≠ ⊥) (h1 : S ≠ ⊤) (g : P8) (hg : g ∈ modelGroup)
    (hfix : ∀ v ∈ S, nativeAction g v = v) : g = 1 := by
  obtain ⟨i, rfl⟩ := (mem_modelGroup g).mp hg
  rcases proper_eq_plane S hS h0 h1 with rfl | rfl
  · exact graph_faithful i (fun x => hfix _ ⟨x, rfl⟩)
  · exact right_faithful i (fun x => hfix _ ⟨x, rfl⟩)

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.SquareModule
