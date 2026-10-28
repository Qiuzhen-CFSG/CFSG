module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order.Bruhat
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order.CellCardinalities.Geometry
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order.CellCardinalities.FixedFamilies
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.SimpleConjugation

/-!
# Exact cardinalities of the sixteen Ree inversion subgroups

The actual root action splits the positive blocks at each Weyl representative
into positive and negative images. The solved fixed coordinates give injective
families with one field parameter per commuting pair and two per B₂ quartet
in both intersections. The intersections are disjoint, so multiplication bounds
the product of their sizes by `|U| = q^12`. The complementary exponents force
the inversion-subgroup size to equal its parameter count.

The sixteen distinct Weyl matrices exhaust the relative Weyl subgroup. Summing
the exact cardinalities gives `(q+1)(q^2+1)(q^3+1)(q^6+1)`, the cell input for
the order formula. Every argument includes `m = 0` and counts the literal fixed
matrix subgroups with left conjugation by the representative.

Source: GLS3 2.3.2–2.3.8 and Table 2.4, `refs/KGroup/GLS3/chapter2.tex`.
Our `q = 2^(2*m+1)` is the square of GLS3's half-integer parameter.
-/

public section
noncomputable section
namespace ReeF4.CentralCovers.OddPrimary.Order.CellCardinalities
open Parabolics Parabolics.Binary.FixedGeometry LocalBlockInput LargeLocalSeeds
open Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
open RadicalCoordinates RadicalCoordinates.FixedCoordinates
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

private theorem simpleWord_conjugation (m : ℕ) (l : List (Fin 4)) (r : F4Chevalley.Root)
    (t : CoefficientField m) :
    simpleWord m l * rootGeneratorInGroup m r t * (simpleWord m l)⁻¹ =
      rootGeneratorInGroup m (typeF4RootPairing.weylGroupToPerm (rootWord l) r) t := by
  rw [rootWord, ← reflectionWord_eq_weylGroupToPerm]
  induction l with
  | nil => simp [simpleWord, reflectionWord]
  | cons i l ih =>
    have hs (r : F4Chevalley.Root) :
        simpleWord m [i] * rootGeneratorInGroup m r t * (simpleWord m [i])⁻¹ =
          rootGeneratorInGroup m (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r) t := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, simpleWord_coe]
      exact PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.simple_conj
        (typeF4RootPairing_baseEquiv i) r t
    have he : simpleWord m (i :: l) = simpleWord m [i] * simpleWord m l := by
      simpa using simpleWord_append m [i] l
    rw [he]
    calc
      _ = simpleWord m [i] * (simpleWord m l * rootGeneratorInGroup m r t *
          (simpleWord m l)⁻¹) * (simpleWord m [i])⁻¹ := by group
      _ = _ := by
        rw [ih, hs]
        simp only [List.map_cons, reflectionWord, typeF4RootPairing_baseEquiv_val]

private theorem pair_conjugation_positive (m : ℕ) (i : Fin 16) (j : Fin 4)
    (hj : j ∈ positivePairs i) (k : Fin 2) (t : CoefficientField m) :
    toSplitGroup m (weylRepresentative m i) *
      rootGeneratorInGroup m ((rootBlocks .positive).roots (.inl (j, k))).val t *
        (toSplitGroup m (weylRepresentative m i))⁻¹ ∈ splitUnipotent m := by
  rw [toSplitGroup_weylRepresentative, simpleWord_conjugation]
  exact Subgroup.subset_closure ⟨_, t, positive_pairs_root i j hj k, rfl⟩

private theorem quartet_conjugation_positive (m : ℕ) (i : Fin 16) (j : Fin 4)
    (hj : j ∈ positiveQuartets i) (k : Fin 4) (t : CoefficientField m) :
    toSplitGroup m (weylRepresentative m i) *
      rootGeneratorInGroup m ((rootBlocks .positive).roots (.inr (j, k))).val t *
        (toSplitGroup m (weylRepresentative m i))⁻¹ ∈ splitUnipotent m := by
  rw [toSplitGroup_weylRepresentative, simpleWord_conjugation]
  exact Subgroup.subset_closure ⟨_, t, positive_quartets_root i j hj k, rfl⟩

private theorem pair_conjugation_negative (m : ℕ) (i : Fin 16) (j : Fin 4)
    (hj : j ∈ (positivePairs i)ᶜ) (k : Fin 2) (t : CoefficientField m) :
    toSplitGroup m (weylRepresentative m i) *
      rootGeneratorInGroup m ((rootBlocks .positive).roots (.inl (j, k))).val t *
        (toSplitGroup m (weylRepresentative m i))⁻¹ ∈ splitNegativeUnipotent m := by
  rw [toSplitGroup_weylRepresentative, simpleWord_conjugation]
  exact Subgroup.subset_closure
    ⟨_, t, negative_pairs_root i j (Finset.mem_compl.mp hj) k, rfl⟩

private theorem quartet_conjugation_negative (m : ℕ) (i : Fin 16) (j : Fin 4)
    (hj : j ∈ (positiveQuartets i)ᶜ) (k : Fin 4) (t : CoefficientField m) :
    toSplitGroup m (weylRepresentative m i) *
      rootGeneratorInGroup m ((rootBlocks .positive).roots (.inr (j, k))).val t *
        (toSplitGroup m (weylRepresentative m i))⁻¹ ∈ splitNegativeUnipotent m := by
  rw [toSplitGroup_weylRepresentative, simpleWord_conjugation]
  exact Subgroup.subset_closure
    ⟨_, t, negative_quartets_root i j (Finset.mem_compl.mp hj) k, rfl⟩

/-- Each actual fixed inversion subgroup has the expected number of field parameters. -/
theorem card_fixedRightUnipotent_representative (m : ℕ) (i : Fin 16) :
    Nat.card (fixedRightUnipotent (weylRepresentative m i)) =
      (2 ^ (2 * m + 1)) ^ cellExponent i := by
  have hu := card_right_mul_le (weylRepresentative m i)
    (intersectionFamily m (positivePairs i) (positiveQuartets i) (weylRepresentative m i)
      (splitUnipotent m) (pair_conjugation_positive m i) (quartet_conjugation_positive m i))
    (intersectionFamily_injective m _ _ _ _ _ _)
  rw [card_selectedParameters] at hu
  have he : (2 ^ (2 * m + 1)) ^ ((positivePairs i).card + 2 * (positiveQuartets i).card) *
      (2 ^ (2 * m + 1)) ^ cellExponent i = (2 ^ (2 * m + 1)) ^ 12 := by
    rw [← pow_add, positive_block_exponents]
  have hupper := Nat.le_of_mul_le_mul_left (hu.trans_eq he.symm) (by positivity)
  have hlower := Nat.card_le_card_of_injective
    (intersectionFamily m (positivePairs i)ᶜ (positiveQuartets i)ᶜ (weylRepresentative m i)
      (splitNegativeUnipotent m) (pair_conjugation_negative m i) (quartet_conjugation_negative m i))
    (intersectionFamily_injective m _ _ _ _ _ _)
  change Nat.card (SelectedParameters m (positivePairs i)ᶜ (positiveQuartets i)ᶜ) ≤
    Nat.card (fixedRightUnipotent (weylRepresentative m i)) at hlower
  rw [card_selectedParameters, negative_block_exponents] at hlower
  exact Nat.le_antisymm hupper hlower

private theorem sum_powers (q : ℕ) :
    ∑ i : Fin 16, q ^ cellExponent i = (q + 1) * (q ^ 2 + 1) * (q ^ 3 + 1) * (q ^ 6 + 1) := by
  simp [Fin.sum_univ_succ, cellExponent]
  ring

end ReeF4.CentralCovers.OddPrimary.Order.CellCardinalities

namespace ReeF4.CentralCovers.OddPrimary.Order
open Parabolics.Binary.FixedGeometry CellCardinalities
local instance (m : ℕ) (H : Subgroup (Model m)) : Fintype H := Fintype.ofFinite _

/-- Exact sum of the cardinalities of the sixteen genuine fixed inversion subgroups.
This discharges the cell-count premise of `card_model_of_torus_and_cells`. -/
theorem sum_card_fixedRightUnipotent (m : ℕ) :
    ∑ w : weylSubgroup m, Nat.card (fixedRightUnipotent w.val) =
      (2 ^ (2 * m + 1) + 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1) *
        ((2 ^ (2 * m + 1)) ^ 3 + 1) * ((2 ^ (2 * m + 1)) ^ 6 + 1) := by
  classical
  rw [← (weylEquiv m).sum_comp (fun w => Nat.card (fixedRightUnipotent w.val))]
  change ∑ i : Fin 16, Nat.card (fixedRightUnipotent (weylRepresentative m i)) = _
  simp only [card_fixedRightUnipotent_representative]
  exact sum_powers _

/-- Applying the exact cell sum to the genuine restricted Bruhat counting identity.
Only the fixed torus cardinality remains in the group-order calculation. -/
theorem card_model_torus_cell_product (m : ℕ) :
    Nat.card (Model m) = (2 ^ (2 * m + 1)) ^ 12 * Nat.card (Parabolics.fixedTorus m) *
      ((2 ^ (2 * m + 1) + 1) * ((2 ^ (2 * m + 1)) ^ 2 + 1) *
        ((2 ^ (2 * m + 1)) ^ 3 + 1) * ((2 ^ (2 * m + 1)) ^ 6 + 1)) := by
  rw [card_model_torus_weyl_sum, sum_card_fixedRightUnipotent]

end ReeF4.CentralCovers.OddPrimary.Order
