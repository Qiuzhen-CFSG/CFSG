/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalPairGeometry.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.CoordinateVectorStabilizer
public import Theory.AtlasPort.OtherSporadic.Conway.GolayPairSemidirect
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalPairGeometry.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def minimumPairPlus (i j : Omega) : leech :=
  ⟨coordinateVector i 4 + coordinateVector j 4,coordinate_pair_mem i j⟩

def minimumPairMinus (i j : Omega) : leech :=
  ⟨coordinateVector i 4 - coordinateVector j 4,difference_mem i j⟩

theorem minimumPairPlus_norm (i j : Omega) (hij : i ≠ j) :
    integerDot (minimumPairPlus i j).val (minimumPairPlus i j).val = 32 := pair_norm i j hij

theorem minimumPairMinus_norm (i j : Omega) (hij : i ≠ j) :
    integerDot (minimumPairMinus i j).val (minimumPairMinus i j).val = 32 := difference_norm i j hij

-- Retain the source's named hypothesis, although this identity also holds when i = j.
set_option linter.unusedVariables false in
theorem minimumPair_orthogonal (i j : Omega) (hij : i ≠ j) :
    integerDot (minimumPairPlus i j).val (minimumPairMinus i j).val = 0 := by
  unfold integerDot
  have he (k : Omega) : (minimumPairPlus i j).val k * (minimumPairMinus i j).val k =
      (if k = i then 16 else 0) - (if k = j then 16 else 0) := by
    simp only [minimumPairPlus,minimumPairMinus,Pi.add_apply,Pi.sub_apply,coordinateVector,Pi.single_apply]
    split_ifs <;> simp_all
  simp_rw [he]
  simp [Finset.sum_sub_distrib]

theorem minimumPair_sum (i j : Omega) :
    minimumPairPlus i j + minimumPairMinus i j = coordinateEight i := by
  apply Subtype.ext; funext k
  change (coordinateVector i 4 k + coordinateVector j 4 k) +
    (coordinateVector i 4 k - coordinateVector j 4 k) = coordinateVector i 8 k
  simp only [coordinateVector,Pi.single_apply]
  split_ifs <;> ring

theorem minimumPair_sub (i j : Omega) :
    minimumPairPlus i j - minimumPairMinus i j = coordinateEight j := by
  apply Subtype.ext; funext k
  change (coordinateVector i 4 k + coordinateVector j 4 k) -
    (coordinateVector i 4 k - coordinateVector j 4 k) = coordinateVector j 8 k
  simp only [coordinateVector,Pi.single_apply]
  split_ifs <;> ring

theorem minimumPair_fixer_mem_monomial (g : LeechIsometryGroup) (i j : Omega)
    (hp : g.val (minimumPairPlus i j) = minimumPairPlus i j)
    (hm : g.val (minimumPairMinus i j) = minimumPairMinus i j) : g ∈ monomialSubgroup :=
  axis_sum_pair_fixer_mem_monomial g i _ _ (minimumPair_sum i j) hp hm

theorem monomial_axis_fixed_iff (m : GolayMonomialGroup) (a : Omega) :
    (monomialEmbedding m).val (coordinateEight a) = coordinateEight a ↔
      m.right.val a = a ∧ m.left.toAdd.val a = 0 := by
  rw [monomial_coordinateEight]
  constructor
  · intro he
    have hh := congrArg (fun x : leech => x.val (m.right.val a)) he
    have hp : m.right.val a = a := by
      by_contra hn
      split_ifs at hh <;> simp [coordinateEight,coordinateVector,hn] at hh
    refine ⟨hp,?_⟩
    rw [hp] at he
    by_contra hn
    simp only [if_neg hn] at he
    have hh := congrArg (fun x : leech => x.val a) he
    norm_num [coordinateEight,coordinateVector] at hh
  · rintro ⟨hp,hc⟩
    simp [hp,hc]

theorem minimumPair_fixed_iff_axes (g : LeechIsometryGroup) (i j : Omega) :
    (g.val (minimumPairPlus i j) = minimumPairPlus i j ∧
      g.val (minimumPairMinus i j) = minimumPairMinus i j) ↔
    (g.val (coordinateEight i) = coordinateEight i ∧
      g.val (coordinateEight j) = coordinateEight j) := by
  constructor
  · rintro ⟨hp,hm⟩
    constructor
    · rw [← minimumPair_sum i j,map_add,hp,hm]
    · rw [← minimumPair_sub i j,map_sub,hp,hm]
  · rintro ⟨hi,hj⟩
    rw [← minimumPair_sum i j,map_add] at hi
    rw [← minimumPair_sub i j,map_sub] at hj
    constructor
    all_goals apply Subtype.ext; funext k
    all_goals have hi' := congrArg (fun x : leech => x.val k) hi
    all_goals have hj' := congrArg (fun x : leech => x.val k) hj
    all_goals change (g.val (minimumPairPlus i j)).val k + (g.val (minimumPairMinus i j)).val k =
      (minimumPairPlus i j).val k + (minimumPairMinus i j).val k at hi'
    all_goals change (g.val (minimumPairPlus i j)).val k - (g.val (minimumPairMinus i j)).val k =
      (minimumPairPlus i j).val k - (minimumPairMinus i j).val k at hj'
    all_goals omega

end Atlas.Conway
