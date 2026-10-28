module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Realization
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Actual.Checks

/-!
# Realizing the word tables in the actual binary G₂ derived amalgam

The row words are evaluated in the original root generators inside the literal
commutator subgroup of the split-octonion group. The checked matrix columns
separate all 96 rows on each side. The existing parabolic orders therefore
make these row maps bijections, and word induction supplies multiplication.

The 32 common rows have identical matrices in the two actual embeddings.
Their distinctness and the order of the whole intersection give a bijection
onto that intersection. Both inclusion squares commute, and equality in the
ambient group forces equality of the complete packed matrix labels. This
constructs `ConcreteRealization` with no additional hypotheses and discharges
the comparison premise of the finite automorphism sieve.

Source: Aschbacher--Smith F.1.12, printed pp.263--264, and Definition F.4.3,
printed p.274. The original point/line marking is retained. Root coordinates
are from Gerald Höhn and the ATLAS contributors, covered by the ATLAS Research
and Attribution License 1.0 (`LICENSES/ATLAS.txt`); see `Actual.Checks` and
`AmalgamBound.Data` for the finite coordinate comparison.
-/

public section

open Atlas.G2 Atlas.SplitOctonion
open Atlas.G2.BinaryParabolicPair Atlas.G2.BinaryCore Atlas.G2.LieParabolicSetup
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
open Actual

private theorem common_mem_unipotent : commonGenerator ∈ unipotent := by
  have h := unipotentProduct_mem (![0,0,1,0,1,1] : Fin 6 → ZMod 2)
  simpa [unipotentProduct, commonGenerator] using h

private theorem common_mem_derived : commonGenerator ∈ BinaryDerived := by
  change commonGenerator ∈ commutator (Model (ZMod 2))
  rw [commutator_eq_longRootClosure, ← QuotientGroup.eq_one_iff]
  change BinaryException.projection (rootC 1 * rootE 1 * rootF 1) = 1
  rw [map_mul, map_mul, BinaryException.project_E, mul_one,
    BinaryException.project_C_eq_D, BinaryException.project_D_eq_F,
    ← map_mul, rootF_add, show (1 : ZMod 2) + 1 = 0 by decide, rootF_zero, map_one]

private theorem left_mem_iff (g : BinaryDerived) :
    g ∈ BinaryLeft ↔ g.val ∈ firstParabolic := by
  change g.val ∈ parabolic₁ ↔ _
  rw [parabolic₁_binary]

private def leftRow (i : Fin 96) : BinaryLeft :=
  ⟨⟨row leftTable commonGenerator leftGenerator i,
    row_mem leftTable BinaryDerived common_mem_derived cubicActor_mem_derived i⟩,
    (left_mem_iff _).mpr
      (row_mem leftTable firstParabolic
        (unipotent_le_firstParabolic common_mem_unipotent) cubicActor_mem i)⟩

private def rightRow (i : Fin 96) : BinaryRight :=
  ⟨⟨row rightTable commonGenerator rightGenerator i,
    row_mem rightTable BinaryDerived common_mem_derived movingActor_mem_derived i⟩,
    row_mem rightTable secondParabolic
      (unipotent_le_parabolic common_mem_unipotent) movingActor_mem i⟩

private theorem leftRow_injective : Function.Injective leftRow := by
  intro i j h
  exact left_action.row_injective left_valid
    (congrArg (fun g : BinaryLeft => g.val.val) h)

private theorem rightRow_injective : Function.Injective rightRow := by
  intro i j h
  exact right_action.row_injective right_valid
    (congrArg (fun g : BinaryRight => g.val.val) h)

private noncomputable def leftRealization : leftTable.Realization BinaryLeft where
  equiv := Equiv.ofBijective leftRow
    (leftRow_injective.bijective_of_nat_card_le (by rw [card_binaryLeft, Nat.card_fin]))
  one_eq := Subtype.ext (Subtype.ext left_action.row_one)
  mul_eq i j := Subtype.ext (Subtype.ext (left_action.row_mul left_valid i j))

private noncomputable def rightRealization : rightTable.Realization BinaryRight where
  equiv := Equiv.ofBijective rightRow
    (rightRow_injective.bijective_of_nat_card_le (by rw [card_binaryRight, Nat.card_fin]))
  one_eq := Subtype.ext (Subtype.ext right_action.row_one)
  mul_eq i j := Subtype.ext (Subtype.ext (right_action.row_mul right_valid i j))

private theorem overlap_rows (i : Fin 32) :
    (leftRow (leftTable.overlap i)).val = (rightRow (rightTable.overlap i)).val := by
  apply Subtype.ext
  apply model_ext
  intro c
  change (row leftTable commonGenerator leftGenerator _).val (basisVector c) =
    (row rightTable commonGenerator rightGenerator _).val (basisVector c)
  rw [left_action.row_action left_valid, right_action.row_action right_valid]
  funext r
  simp only [column, overlap_labels i]

private def middleRow (i : Fin 32) : binaryOverlap :=
  ⟨(leftRow (leftTable.overlap i)).val,
    (leftRow (leftTable.overlap i)).prop,
    (overlap_rows i).symm ▸ (rightRow (rightTable.overlap i)).prop⟩

private theorem middleRow_injective : Function.Injective middleRow := by
  intro i j h
  apply left_overlap_injective
  apply leftRow_injective
  exact Subtype.ext (congrArg (fun z : binaryOverlap => z.val) h)

private noncomputable def middleEquiv : Fin 32 ≃ binaryOverlap :=
  Equiv.ofBijective middleRow
    (middleRow_injective.bijective_of_nat_card_le (by rw [card_binaryOverlap, Nat.card_fin]))

private theorem actual_left_overlap (i : Fin 32) :
    leftRealization.equiv (leftTable.overlap i) = binaryAmalgam.left (middleEquiv i) := rfl

private theorem actual_right_overlap (i : Fin 32) :
    rightRealization.equiv (rightTable.overlap i) = binaryAmalgam.right (middleEquiv i) :=
  Subtype.ext (overlap_rows i).symm

private theorem labels_of_row_eq (i j : Fin 96)
    (he : row leftTable commonGenerator leftGenerator i =
      row rightTable commonGenerator rightGenerator j) :
    leftTable.label i = rightTable.label j := by
  apply labels_eq (left_label_bound i) (right_label_bound j)
  intro c
  exact (left_action.row_action left_valid i c).symm.trans
    ((congrArg (fun g : Model (ZMod 2) => g.val (basisVector c)) he).trans
      (right_action.row_action right_valid j c))

private theorem left_equiv_val (i : Fin 96) :
    (leftRealization.equiv i).val.val = row leftTable commonGenerator leftGenerator i := rfl

private theorem right_equiv_val (j : Fin 96) :
    (rightRealization.equiv j).val.val = row rightTable commonGenerator rightGenerator j := rfl

private theorem left_inclusion_val (b : binaryOverlap) :
    (binaryAmalgam.left b).val.val = b.val.val := rfl

private theorem right_inclusion_val (b : binaryOverlap) :
    (binaryAmalgam.right b).val.val = b.val.val := rfl

private theorem actual_labels (i j : Fin 96) (b : binaryOverlap)
    (hl : leftRealization.equiv i = binaryAmalgam.left b)
    (hr : rightRealization.equiv j = binaryAmalgam.right b) :
    leftTable.label i = rightTable.label j := by
  apply labels_of_row_eq i j
  exact (left_equiv_val i).symm.trans
    ((congrArg (fun g : BinaryLeft => g.val.val) hl).trans
      ((left_inclusion_val b).trans ((right_inclusion_val b).symm.trans
        ((congrArg (fun g : BinaryRight => g.val.val) hr).symm.trans
          (right_equiv_val j)))))

/-- The published tables realize the two marked derived parabolics and their whole overlap. -/
noncomputable def binaryConcreteRealization : ConcreteRealization where
  left := leftRealization
  right := rightRealization
  middle := middleEquiv
  left_overlap := actual_left_overlap
  right_overlap := actual_right_overlap
  labels := actual_labels

/-- The actual compatible automorphisms embed in the published finite candidate sieve. -/
theorem card_binaryAmalgamAut_le_candidate_actual :
    Nat.card BinaryAmalgamAut ≤ Nat.card Candidate :=
  card_binaryAmalgamAut_le_candidate binaryConcreteRealization

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
