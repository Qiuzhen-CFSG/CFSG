module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers.RowTwo.FixedPoints
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.GraphTable

/-!
# The second four-group normalizer preserves the Sylow coloring

Count neighbors in the 26 common fixed points. The resulting signature has
two useful cells, of sizes two and thirty-two. Counts in these two cells,
together with the initial signature, determine the published representative
orbit-size coloring. All three sets are invariant under the full row
normalizer. Thus its elements preserve that coloring, giving access to the
existing colored graph bound without enumerating the normalizer.

Sources: the literal ATLAS degree-2058 graph; GLS3 Table 5.3p;
Aschbacher–Smith 15.3.43, printed p.1140.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers.RowTwo
open Subgroup LocalPairs.SylowGeometry.Calculations InnerNormalizer
open InnerNormalizer.GraphBound NormalizerGraph
open scoped BigOperators

set_option Elab.async false

private def Invariant (f : Fin 2058 → ℕ) : Prop :=
  ∀ g ∈ normalizer (ambient 2 : Set He), ∀ x, f (g • x) = f x

private def neighborCount (S : Finset (Fin 2058)) (x : Fin 2058) : ℕ :=
  ∑ y ∈ S, if Adj x y then 1 else 0

private theorem count_invariant (S : Finset (Fin 2058))
    (hS : ∀ g ∈ normalizer (ambient 2 : Set He), ∀ x, g • x ∈ S ↔ x ∈ S) :
    Invariant (neighborCount S) := by
  intro g hg x
  have hgraph := Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup g.property
  unfold neighborCount
  symm
  apply Finset.sum_bij (fun y _ => g • y)
  · intro y hy
    exact (hS g hg y).mpr hy
  · intro y _ z _ he
    exact (MulAction.injective g) he
  · intro y hy
    refine ⟨g⁻¹ • y, ?_, smul_inv_smul g y⟩
    exact (hS g⁻¹ (inv_mem hg) y).mpr hy
  · intro y _
    simp only [show Adj (g • x) (g • y) ↔ Adj x y from hgraph x y]

private def signature (x : Fin 2058) : ℕ :=
  (if x ∈ fixedSet then 1 else 0) + 2 * neighborCount fixedSet x

private theorem signature_invariant : Invariant signature := by
  intro g hg x
  unfold signature
  simp only [fixedSet_invariant g hg, count_invariant fixedSet fixedSet_invariant g hg]

private def cell0Points : List (Fin 2058) := [480, 1444]

private theorem cell0_nodup : cell0Points.Nodup := by decide +kernel

private def cell0 : Finset (Fin 2058) := ⟨cell0Points, cell0_nodup⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem cell0_spec : ∀ x : Fin 2058,
    x ∈ cell0 ↔ signature x = 19 := by
  simp only [signature, neighborCount, adj_iff_fast]
  apply checked_forall
  decide +kernel

private theorem cell0_invariant
    (g : He) (hg : g ∈ normalizer (ambient 2 : Set He)) (x : Fin 2058) :
    g • x ∈ cell0 ↔ x ∈ cell0 := by
  rw [cell0_spec, cell0_spec, signature_invariant g hg]

private def cell1Points : List (Fin 2058) := [54, 403, 434, 504, 567, 587, 724, 794, 824, 850, 854, 915, 1030, 1091, 1097, 1122, 1144, 1228, 1270, 1414, 1513, 1561, 1628, 1682, 1692, 1706, 1833, 1872, 1956, 1965, 2003, 2056]

private theorem cell1_nodup : cell1Points.Nodup := by decide +kernel

private def cell1 : Finset (Fin 2058) := ⟨cell1Points, cell1_nodup⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem cell1_spec : ∀ x : Fin 2058,
    x ∈ cell1 ↔ signature x = 4 := by
  simp only [signature, neighborCount, adj_iff_fast]
  apply checked_forall
  decide +kernel

private theorem cell1_invariant
    (g : He) (hg : g ∈ normalizer (ambient 2 : Set He)) (x : Fin 2058) :
    g • x ∈ cell1 ↔ x ∈ cell1 := by
  rw [cell1_spec, cell1_spec, signature_invariant g hg]

private def decode (s : ℕ) : ℕ :=
  (if s < 1034 then (if s < 338 then (if s < 51 then 16 else (if s < 272 then 2 else 32)) else (if s < 556 then (if s < 528 then 64 else 64) else (if s < 1032 then 512 else 128))) else (if s < 1099 then (if s < 1036 then 128 else (if s < 1068 then 64 else 32)) else (if s < 1412 then (if s < 1160 then 4 else 256) else (if s < 2060 then 16 else 8))))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem coloring_checked : ∀ x : Fin 2058,
    orbitSizeLabel x = decode (signature x + 32 * neighborCount cell0 x +
      128 * neighborCount cell1 x) := by
  simp only [signature, neighborCount, adj_iff_fast]
  apply checked_forall
  decide +kernel

/-- Every element of the full normalizer preserves the existing Sylow coloring. -/
public theorem normalizer_preserves_coloring (g : He)
    (hg : g ∈ normalizer (ambient 2 : Set He)) (x : Fin 2058) :
    orbitSizeLabel (g • x) = orbitSizeLabel x := by
  rw [coloring_checked, coloring_checked, signature_invariant g hg,
    count_invariant cell0 cell0_invariant g hg, count_invariant cell1 cell1_invariant g hg]

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.FourGroupNormalizers.RowTwo
