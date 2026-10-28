module
public import Theory.Mathieu.M24.LocalGeometry.FourNormalizers.Overgroups.Rows
public import Theory.Mathieu.M24.LocalGeometry.EvenCandidates
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineLifts.CodePreservation
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.QuotientConstruction.AffineCoordinates

/-!
# Native permutations for the four-normalizer enlargements

Three explicit permutations provide a transporter from the fixed-octad trio
to the standard trio, an octad-stabilizer witness for rows 1 and 2, and a
trio-stabilizer witness for row 3. Each preserves all twelve Golay rows.
Point comparisons prove that the latter two fail to normalize the indicated
four-groups. The six generators of the existing trio elementary candidate
become pure translations in the standard affine coordinates.

All tables are checked by the Lean kernel. The untrusted discovery program
is retained in `source/inspect.py`; no GAP normalizer order is used.
Source context: Aschbacher--Smith 15.3.43, printed p.1140; GLS3, Table 5.3e.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.FourNormalizers
open Subgroup PairOvergroups PairOvergroups.QuotientConstruction
open scoped Pointwise

/-- A transporter to the standard trio, and two strictness witnesses. -/
def certificatePerm (i : Fin 3) : Equiv.Perm (Fin 24) where
  toFun := (![![20,8,13,19,7,1,10,22,15,6,23,14,18,5,16,0,21,2,11,12,4,9,17,3],![0,1,2,3,4,5,13,22,19,21,20,11,16,6,18,23,12,17,14,8,10,9,7,15],![3,2,1,0,19,6,5,10,21,11,7,9,22,18,17,23,20,14,13,4,16,8,12,15]]) i
  invFun := (![![15,5,17,23,20,13,9,4,1,21,6,18,19,2,11,8,14,22,12,3,0,16,7,10],![0,1,2,3,4,5,13,22,19,21,20,11,16,6,18,23,12,17,14,8,10,9,7,15],![3,2,1,0,19,6,5,10,21,11,7,9,22,18,17,23,20,14,13,4,16,8,12,15]]) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

private def rowMessages : Fin 3 → Fin 12 → Fin 4096 :=
  ![![541,781,3084,1044,133,1550,1560,25,1049,1616,1541,561],![513,898,132,392,272,800,2944,128,256,512,1664,960],![264,404,2178,2193,144,2384,2352,128,2192,3456,2816,272]]

private theorem certificate_rows : ∀ i j,
    m24PermuteMask (certificatePerm i) (m24GolayRow j) = m24GolayCode (rowMessages i j) := by
  decide +kernel

/-- All twelve Golay row images certify each native design automorphism. -/
theorem certificatePerm_mem (i : Fin 3) : certificatePerm i ∈ M24 :=
  AffineLiftConstruction.mem_M24_of_rows _
    (fun j => ⟨rowMessages i j, certificate_rows i j⟩)

/-- Every witness belongs to the actual Witt-design automorphism group. -/
noncomputable def certificateElement (i : Fin 3) : M24 :=
  ⟨certificatePerm i, certificatePerm_mem i⟩

/-- The fixed octads of row 3 are transported to the literal standard trio. -/
theorem transport_geometry :
    certificateElement 0 • rowGeometry 2 = standardTrio.parts := by decide +kernel

theorem octad_witness_mem : certificateElement 1 ∈ octadStabilizer commonOctad := by
  change certificatePerm 1 • commonOctad.val = commonOctad.val
  decide +kernel

theorem trio_witness_mem :
    certificateElement 2 ∈ MulAction.stabilizer M24 (rowGeometry 2) := by
  change certificatePerm 2 • rowGeometry 2 = rowGeometry 2
  decide +kernel

private def testGenerator : Fin 3 → Fin 4 := ![1,1,1]
private def testPoint : Fin 3 → Fin 4 → Fin 24 := ![![1,1,1,1],![1,1,0,0],![0,0,0,0]]

private theorem witness_test : ∀ r k,
    certificatePerm (if r = 2 then 2 else 1)
      (rowPoint r (testGenerator r)
        ((certificatePerm (if r = 2 then 2 else 1)).symm (testPoint r k))) ≠
      rowPoint r k (testPoint r k) := by decide +kernel

/-- A pointwise certificate detects failure to normalize each four-group. -/
theorem witness_not_normalizer (r : Fin 3) :
    certificateElement (if r = 2 then 2 else 1) ∉
      normalizer (EvenCatalogue.ambient (rowNumber r) : Set M24) := by
  intro hn
  have hm := (mem_set_normalizer_iff.mp hn _).mp (rowElement_mem r (testGenerator r))
  obtain ⟨k, hk⟩ := (mem_ambient_row_iff r _).mp hm
  have he := congrArg (fun g : M24 => g.val (testPoint r k)) hk
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_def, rowElement_apply] at he
  exact witness_test r k he.symm

/-- The trio candidate generators preserve this exact fixed-octad geometry. -/
theorem elementary_generator_mem_trio (j : Fin 6) :
    EvenCandidates.generator 0 j ∈ MulAction.stabilizer M24 (rowGeometry 2) := by
  change (rowGeometry 2).image (fun A => A.image ((EvenCandidates.generator 0 j).val)) = _
  have he : ((EvenCandidates.generator 0 j).val : Fin 24 → Fin 24) =
      EvenCandidates.generatorPoint 0 j := funext (EvenCandidates.generator_apply 0 j)
  rw [he]
  clear he
  revert j
  decide +kernel

/-- Translation vectors of the six transported candidate generators. -/
def translationVector : Fin 6 → Fin 3 → Vector :=
  ![![![1,1,1],![1,1,1],![0,0,0]],![![1,1,1],![0,0,0],![1,1,1]],![![0,1,0],![0,1,0],![0,0,0]],![![0,0,0],![1,0,0],![1,0,0]],![![0,1,0],![0,1,1],![0,0,1]],![![0,1,1],![1,1,1],![1,0,0]]]

/-- The actual transported generators have identity linear and octad parts. -/
theorem generator_translation (j : Fin 6) (i : Fin 3) (v : Vector) :
    (certificateElement 0 * EvenCandidates.generator 0 j * (certificateElement 0)⁻¹).val
        (point (i,v)) = point (i, v + translationVector j i) := by
  change certificatePerm 0
    ((EvenCandidates.generator 0 j).val ((certificatePerm 0).symm (point (i,v)))) = _
  rw [EvenCandidates.generator_apply]
  revert j i v
  decide +kernel

end Sporadic.Mathieu.M24LocalGeometry.FourNormalizers
