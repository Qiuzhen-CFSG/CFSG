module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.NaturalGeometry
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.Successive

/-!
# Coordinate transport for the successive residual conjugators

A marking identifies each original natural parabolic with its actual binary
flag stabilizer. Finite-image transport of O², followed by an explicit
one-based to zero-based reindexing, identifies the initial residual joins.
The adjacent basis swap pulls back to the required natural parabolic.

Residual recognition now discharges the model bound in the original
conditional adapters. The final theorems use only the specified marking,
then apply `initialResiduals_conjugator_of_natural`, retaining the original
ambient Sylow, pointwise full action and two-core kernel. Neither ordinary
generation nor terminal residual equality is assumed. The source assembly
owner supplies the marking from `MarkedGeneration`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.10(5), printed p.854 (PDF p.871), `refs/quasithin.pdf`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {m : ℕ}

/-- The original parabolic's embedded residual maps to the residual of its
marked binary coordinate stabilizer, with the subgroup inclusions retained. -/
theorem naturalOrderedResidual_map_coordinates (F : InvariantFlag T V (m + 1))
    (e : MulAut V ≃* LinearGroup (m + 1)) (b : Basis m)
    (hmark : ∀ i : Fin m,
      (F.naturalOrderedParabolic (i.val + 1)).map e.toMonoidHom = minimalParabolic b i)
    (i : Fin m) :
    ((pResidual 2 (F.naturalOrderedParabolic (i.val + 1))).map
      (F.naturalOrderedParabolic (i.val + 1)).subtype).map e.toMonoidHom =
      BinaryLinear.OrderedResidualConjugators.nodeResidual b i := by
  rw [map_embedded_pResidual, hmark]
  rfl

/-- Reindex the source's one-based initial joins by the zero-based coordinate
nodes. The upper bound excludes the extra natural-number flag indices. -/
theorem naturalInitialResiduals_map_coordinates (F : InvariantFlag T V (m + 1))
    (e : MulAut V ≃* LinearGroup (m + 1)) (b : Basis m)
    (hmark : ∀ i : Fin m,
      (F.naturalOrderedParabolic (i.val + 1)).map e.toMonoidHom = minimalParabolic b i)
    (r : ℕ) (hr : r ≤ m) :
    (F.naturalInitialResiduals r).map e.toMonoidHom =
      BinaryLinear.OrderedResidualConjugators.initialResiduals b r := by
  unfold naturalInitialResiduals
  simp only [Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro j
    apply iSup_le
    intro hj
    let i : Fin m := ⟨j - 1, by omega⟩
    have hi : i.val + 1 = j := by dsimp [i]; omega
    rw [← hi, F.naturalOrderedResidual_map_coordinates e b hmark i]
    exact le_iSup_of_le i (le_iSup_of_le (show i.val < r by dsimp [i]; omega) le_rfl)
  · apply iSup_le
    intro i
    apply iSup_le
    intro hi
    rw [← F.naturalOrderedResidual_map_coordinates e b hmark i]
    exact le_iSup_of_le (i.val + 1)
      (le_iSup_of_le (show 1 ≤ i.val + 1 ∧ i.val + 1 ≤ r by omega) le_rfl)

omit [Finite G] in
/-- The explicit adjacent swap pulls back to the required natural parabolic.
Its residual-generation property remains a separate intrinsic calculation. -/
theorem coordinateAdjacentSwap_mem_naturalOrderedParabolic
    (F : InvariantFlag T V (m + 1)) (e : MulAut V ≃* LinearGroup (m + 1)) (b : Basis m)
    (hmark : ∀ i : Fin m,
      (F.naturalOrderedParabolic (i.val + 1)).map e.toMonoidHom = minimalParabolic b i)
    (i : Fin m) :
    e.symm (BinaryLinear.OrderedResidualConjugators.adjacentSwap b i) ∈
      F.naturalOrderedParabolic (i.val + 1) := by
  apply Subgroup.mem_map_equiv.mp
  rw [hmark]
  exact BinaryLinear.OrderedResidualConjugators.adjacentSwap_mem_minimalParabolic b i

/-- The proved model root groups act inside the actual natural residual
joins. This applies the lower-bound calculation to the source stabilizers. -/
theorem naturalInitialResiduals_contains_coordinate_roots
    (F : InvariantFlag T V (m + 1)) (e : MulAut V ≃* LinearGroup (m + 1)) (b : Basis m)
    (hmark : ∀ i : Fin m,
      (F.naturalOrderedParabolic (i.val + 1)).map e.toMonoidHom = minimalParabolic b i)
    (r : ℕ) (hr : r ≤ m) :
    (BinaryLinear.OrderedResidualConjugators.initialRootNodes b r).map e.symm.toMonoidHom ≤
      F.naturalInitialResiduals r := by
  rintro a ⟨g, hg, rfl⟩
  apply (Subgroup.mem_map_equiv (f := e)).mp
  rw [F.naturalInitialResiduals_map_coordinates e b hmark r hr]
  exact BinaryLinear.OrderedResidualConjugators.initialRootNodes_le_initialResiduals b r hg

/-- Once the reverse residual bound is established, the actual marked
natural groups admit successive conjugators. No ordinary or terminal
generation premise, and no conjugator premise, is used. -/
theorem naturalInitialResiduals_successor_of_coordinate_residual_bound
    (F : InvariantFlag T V (m + 1)) (e : MulAut V ≃* LinearGroup (m + 1)) (b : Basis m)
    (hmark : ∀ i : Fin m,
      (F.naturalOrderedParabolic (i.val + 1)).map e.toMonoidHom = minimalParabolic b i)
    (hres : ∀ i : Fin m, BinaryLinear.OrderedResidualConjugators.nodeResidual b i ≤
      BinaryLinear.OrderedResidualConjugators.rootNode b i)
    (j : ℕ) (hj : 1 ≤ j) (hjm : j + 1 < m + 1) :
    ∃ a ∈ F.naturalOrderedParabolic (j + 1), F.naturalInitialResiduals (j + 1) =
      F.naturalInitialResiduals j ⊔ conjugate (F.naturalInitialResiduals j) a := by
  have hlt : j < m := by omega
  let s := BinaryLinear.OrderedResidualConjugators.adjacentSwap b ⟨j, hlt⟩
  let a := e.symm s
  refine ⟨a, F.coordinateAdjacentSwap_mem_naturalOrderedParabolic e b hmark ⟨j, hlt⟩, ?_⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  have hc : (conjugate (F.naturalInitialResiduals j) a).map e.toMonoidHom =
      ((F.naturalInitialResiduals j).map e.toMonoidHom).map
        (MulAut.conj ((e a)⁻¹)).toMonoidHom := by
    simp only [conjugate, Subgroup.map_map]
    congr 1
    ext x
    simp
  rw [Subgroup.map_sup, hc,
    F.naturalInitialResiduals_map_coordinates e b hmark (j + 1) (by omega),
    F.naturalInitialResiduals_map_coordinates e b hmark j (by omega)]
  have ha : e a = s := e.apply_symm_apply s
  rw [ha]
  exact BinaryLinear.OrderedResidualConjugators.initialResiduals_successor_of_nodeResidual_le
    b hres j hj hlt

/-- Lift the coordinate construction to the original ambient group using
its full action and its two-core kernel. Residual recognition remains the
single additional model premise; the source assembly must discharge it. -/
theorem initialResiduals_successor_of_coordinate_residual_bound
    (F : InvariantFlag T V (m + 1)) (e : MulAut V ≃* LinearGroup (m + 1)) (b : Basis m)
    (hmark : ∀ i : Fin m,
      (F.naturalOrderedParabolic (i.val + 1)).map e.toMonoidHom = minimalParabolic b i)
    (hres : ∀ i : Fin m, BinaryLinear.OrderedResidualConjugators.nodeResidual b i ≤
      BinaryLinear.OrderedResidualConjugators.rootNode b i)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (j : ℕ) (hj : 1 ≤ j) (hjm : j + 1 < m + 1) :
    ∃ k ∈ F.orderedParabolic L (j + 1), F.initialResiduals L (j + 1) =
      F.initialResiduals L j ⊔ conjugate (F.initialResiduals L j) k := by
  obtain ⟨a, ha, he⟩ := F.naturalInitialResiduals_successor_of_coordinate_residual_bound
    e b hmark hres j hj hjm
  exact F.initialResiduals_conjugator_of_natural L hL hfull hcore j a ha he

/-- Under the coordinate marking alone, the natural residual joins admit
successive right conjugators. The intrinsic residual bound is proved. -/
theorem naturalInitialResiduals_successor_of_coordinates
    (F : InvariantFlag T V (m + 1)) (e : MulAut V ≃* LinearGroup (m + 1)) (b : Basis m)
    (hmark : ∀ i : Fin m,
      (F.naturalOrderedParabolic (i.val + 1)).map e.toMonoidHom = minimalParabolic b i)
    (j : ℕ) (hj : 1 ≤ j) (hjm : j + 1 < m + 1) :
    ∃ a ∈ F.naturalOrderedParabolic (j + 1), F.naturalInitialResiduals (j + 1) =
      F.naturalInitialResiduals j ⊔ conjugate (F.naturalInitialResiduals j) a :=
  F.naturalInitialResiduals_successor_of_coordinate_residual_bound e b hmark
    (BinaryLinear.OrderedResidualConjugators.nodeResidual_le_rootNode b) j hj hjm

/-- The actual ambient successive-conjugator step of 12.8.10(5), conditional
only on the coordinate marking and the original action and kernel hypotheses.
The source assembly owner supplies the marking; no further model premise remains. -/
theorem initialResiduals_successor_of_coordinates
    (F : InvariantFlag T V (m + 1)) (e : MulAut V ≃* LinearGroup (m + 1)) (b : Basis m)
    (hmark : ∀ i : Fin m,
      (F.naturalOrderedParabolic (i.val + 1)).map e.toMonoidHom = minimalParabolic b i)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (j : ℕ) (hj : 1 ≤ j) (hjm : j + 1 < m + 1) :
    ∃ k ∈ F.orderedParabolic L (j + 1), F.initialResiduals L (j + 1) =
      F.initialResiduals L j ⊔ conjugate (F.initialResiduals L j) k := by
  obtain ⟨a, ha, he⟩ := F.naturalInitialResiduals_successor_of_coordinates e b hmark j hj hjm
  exact F.initialResiduals_conjugator_of_natural L hL hfull hcore j a ha he

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
