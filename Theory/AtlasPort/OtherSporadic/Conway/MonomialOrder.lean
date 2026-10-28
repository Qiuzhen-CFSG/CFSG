/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MonomialOrder.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechVisibleSymmetries
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechCrossAction
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24Order
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/MonomialOrder.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem monomial_order : Nat.card monomialSubgroup = 1002795171840 := by
  rw [← Nat.card_congr monomialSubgroupEquiv.toEquiv,SemidirectProduct.card,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative golay ≃ golay),golay_card,mathieu24_order]

theorem monomial_coordinateEight (g : GolayMonomialGroup) (a : Omega) :
    (monomialEmbedding g).val (coordinateEight a) =
      if g.left.toAdd.val (g.right.val a) = 0 then coordinateEight (g.right.val a)
      else -coordinateEight (g.right.val a) := by
  apply Subtype.ext
  ext i
  by_cases hi : i = g.right.val a
  · subst i
    simp only [monomialEmbedding_apply,coordinateEight,coordinateVector,Pi.single_apply,
      Equiv.symm_apply_apply,ite_true]
    split_ifs <;> simp
  · have ha : g.right.val.symm i ≠ a := by
      intro h
      apply hi
      rw [← h,Equiv.apply_symm_apply]
    simp only [monomialEmbedding_apply,coordinateEight,coordinateVector,Pi.single_apply,ha,ite_false]
    split_ifs <;> simp_all

theorem monomial_fixes_standardCross (g : GolayMonomialGroup) :
    crossAction (monomialEmbedding g) standardCross = standardCross := by
  apply Subtype.ext
  change leechModTwoRepresentation (monomialEmbedding g)
    (leechReduction (coordinateEight ((0,0),0))) = leechReduction (coordinateEight ((0,0),0))
  rw [leechModTwoRepresentation_reduce,monomial_coordinateEight]
  split_ifs
  · exact coordinateEight_class _ _
  · rw [leechReduction_neg]; exact coordinateEight_class _ _

end Atlas.Conway
