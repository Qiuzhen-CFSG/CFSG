/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechLattice.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechDeterminant
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechGenerators

/-!
The integral, even, unimodular Leech lattice and its gluing quotients.
The package assembles proved coordinate, rank, duality, minimum, and generation results.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def evenGluingEquiv :
    (evenGolayLattice ⧸ fourEvenLattice.addSubgroupOf evenGolayLattice) ≃+ golay :=
  (QuotientAddGroup.quotientAddEquivOfEq evenResidue_kernel.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective evenResidue evenResidue_surjective)

def oddGluingEquiv : (leech ⧸ evenGolayLattice.addSubgroupOf leech.toAddSubgroup) ≃+ Bit :=
  (QuotientAddGroup.quotientAddEquivOfEq leechParity_kernel.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective leechParity leechParity_surjective)

theorem rationalForm_positive (x : RationalCoordinates) (hx : x ≠ 0) : 0 < rationalForm x x := by
  have hn : 0 ≤ ∑ i, x i * x i := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  have hz : (∑ i, x i * x i) ≠ 0 := by
    intro h
    apply hx
    ext i
    have hi : x i * x i ≤ ∑ j, x j * x j :=
      Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
    rw [h] at hi
    change x i = 0
    nlinarith
  have hp : 0 < ∑ i, x i * x i := lt_of_le_of_ne hn (Ne.symm hz)
  change 0 < (1/8 : ℚ) * ∑ i, x i * x i
  positivity

structure LatticeConstruction : Prop where
  coordinates : ∀ x, x ∈ leech ↔ LeechCongruences x
  gluing : ∀ a x, x ∈ leechAt a ↔ x ∈ evenGolayLattice ∨ x - oddGlue a ∈ evenGolayLattice
  marking_independent : ∀ a b, leechAt a = leechAt b
  rank : Module.finrank ℤ leech = 24
  finite_module : Module.Finite ℤ leech
  free_module : Module.Free ℤ leech
  full_span : Submodule.span ℚ (rationalLeech : Set RationalCoordinates) = ⊤
  index : leech.toAddSubgroup.index = 2^36
  gram_determinant : ∀ b : Module.Basis Omega ℤ leech, (leechGram b).det = 1
  self_dual : leechDual = rationalLeech
  positive : ∀ x : RationalCoordinates, x ≠ 0 → 0 < rationalForm x x
  integral : ∀ x y : leech, ∃ k : ℤ,
    rationalForm (rationalEmbedding x.val) (rationalEmbedding y.val) = k
  even : ∀ x : leech, ∃ k : ℤ,
    rationalForm (rationalEmbedding x.val) (rationalEmbedding x.val) = 2*k
  minimum : ∀ x : leech, x ≠ 0 →
    4 ≤ rationalForm (rationalEmbedding x.val) (rationalEmbedding x.val)
  attained : ∃ x : leech,
    rationalForm (rationalEmbedding x.val) (rationalEmbedding x.val) = 4
  generated : minimalSpan = leech

theorem leech_lattice_constructed : LatticeConstruction where
  coordinates := mem_leech
  gluing := mem_leechAt
  marking_independent := leechAt_independent
  rank := leech_rank
  finite_module := leech_finitelyGenerated
  free_module := leech_free
  full_span := rationalLeech_full_span
  index := leech_index
  gram_determinant := leech_gram_determinant
  self_dual := leech_selfDual
  positive := rationalForm_positive
  integral := leech_pairing_integral
  even := leech_norm_even
  minimum := leech_minimum
  attained := leech_minimum_attained
  generated := minimal_vectors_span

end Atlas.Lattices
