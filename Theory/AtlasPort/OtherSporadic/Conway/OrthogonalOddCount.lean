/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalOddCount.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalOddOrbit
public import Theory.AtlasPort.OtherSporadic.Conway.GolayOppositeCoordinateFiber
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalOddCount.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem oddMinimumVector_mem (a : Omega) (c : golay) :
    (oddMinimumVector a c).val ∈ oddNoFiveVectors 1 :=
  Finset.mem_image.mpr ⟨(⟨{a},by simp⟩,c),Finset.mem_univ _,rfl⟩

theorem odd_coordinates_orthogonal_iff (i j a : Omega) (c : golay)
    (hai : a ≠ i) (haj : a ≠ j) :
    integerDot (minimumPairPlus i j).val (oddMinimumVector a c).val = 0 ↔ c.val i ≠ c.val j := by
  rw [minimumPairPlus_dot]
  rcases bit_cases (c.val i) with hi | hi <;> rcases bit_cases (c.val j) with hj | hj <;>
    simp [oddMinimumVector,signedOddProfile,signChange,oddProfileBase,hai.symm,haj.symm,hi,hj]

abbrev OrthogonalOddParameters (i j : Omega) := {a : Omega // a ≠ i ∧ a ≠ j} × GolayOppositeCoordinates i j

def OrthogonalOddClass (i j : Omega) :=
  {x : leech // x.val ∈ oddNoFiveVectors 1 ∧ integerDot (minimumPairPlus i j).val x.val = 0}

def orthogonalOddMap (i j : Omega) (p : OrthogonalOddParameters i j) : OrthogonalOddClass i j :=
  ⟨oddMinimumVector p.1.val p.2.val,oddMinimumVector_mem _ _,
    (odd_coordinates_orthogonal_iff i j p.1.val p.2.val p.1.prop.1 p.1.prop.2).mpr p.2.prop⟩

def orthogonalOddEquiv (i j : Omega) (hij : i ≠ j) :
    OrthogonalOddParameters i j ≃ OrthogonalOddClass i j :=
  Equiv.ofBijective (orthogonalOddMap i j) ⟨by
    intro p q h
    have he := congrArg (fun x : OrthogonalOddClass i j => x.val.val) h
    have hp := noFiveVector_injective 1 (a₁ := (⟨{p.1.val},by simp⟩,p.2.val))
      (a₂ := (⟨{q.1.val},by simp⟩,q.2.val)) he
    have ha := congrArg (fun x : NoFiveParameters 1 => x.1.val) hp
    have hc := congrArg (fun x : NoFiveParameters 1 => x.2) hp
    apply Prod.ext
    · apply Subtype.ext
      exact Finset.singleton_injective ha
    · exact Subtype.ext hc,by
    intro x
    obtain ⟨a,c,hc⟩ := odd_minimum_parameterization x.val x.prop.1
    have ho : integerDot (minimumPairPlus i j).val (oddMinimumVector a c).val = 0 := by rw [hc]; exact x.prop.2
    have ha := orthogonal_odd_mark_outside i j a hij c ho
    have hs := (odd_coordinates_orthogonal_iff i j a c ha.1 ha.2).mp ho
    exact ⟨(⟨a,ha⟩,⟨c,hs⟩),Subtype.ext hc⟩⟩

theorem orthogonalOddClass_card (i j : Omega) (hij : i ≠ j) :
    Nat.card (OrthogonalOddClass i j) = 45056 := by
  let : Finite (GolayOppositeCoordinates i j) :=
    inferInstanceAs (Finite {c : golay // c.val i ≠ c.val j})
  have e : {a : Omega // a ≠ i ∧ a ≠ j} ≃ {a // a ∈ (Finset.univ \ {i,j} : Finset Omega)} :=
    Equiv.subtypeEquivRight (fun a => by simp)
  have hc : Nat.card {a : Omega // a ≠ i ∧ a ≠ j} = 22 := by
    rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,
      Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    norm_num [Omega,HexIndex,Finset.card_pair hij]
  rw [← Nat.card_congr (orthogonalOddEquiv i j hij),Nat.card_prod,hc,golayOppositeCoordinates_card i j hij]

end Atlas.Conway
