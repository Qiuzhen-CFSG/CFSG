module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.Candidates
public import Theory.AlgebraicGroup.Instance.U
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagRepresentation.Stabilizer

/-!
# Triangular support of the concrete Spin root candidates

The faithful natural action is written in the order
`e0,e1,e2,e3,f3,f2,f1,f0`; the negative sign uses the reversed order.
Four symbolic matrix formulas for the difference and sum roots, and their
negatives, show that the prescribed root groups are unitriangular. Subgroup
generation then gives unitriangularity of the published root-generated
candidates and triangularity after adjoining the coroot torus.

The faithful triangular embedding proves solvability. A uniform power of two
annihilates each unitriangular point, proving unipotence on the actual closed
Clifford subgroup. Comparing upper and lower entries proves opposite
separation. None of these arguments assumes Borel maximality or a regular
inverse to the Spin cover.

Source: GLS3, Theorems 1.11.2 and 1.11.4
(`refs/KGroup/GLS3/Chapter1.tex`), and Steinberg (6.2)(a-b)
(`refs/KGroup/GLS3/Chapter2St2.tex`).
-/

open Theory Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.NaturalCoefficients
open Triality.Standard.PositiveCoordinates
@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.OppositeBorels.BorelCertification
set_option linter.unusedSimpArgs false
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
local instance (S : ClosedSubgroup (groupVariety k)) : AlgebraicGroup S.carrierVariety :=
  S.carrierAlgebraicGroup

def coordinateOrder : Fin 8 ≃ Index :=
  (finSumFinEquiv (m := 4) (n := 4)).symm.trans
    (Equiv.sumCongr (Equiv.refl _) Fin.revPerm)

def signedOrder (negative : Bool) : Fin 8 ≃ Index :=
  if negative then coordinateOrder.trans (Equiv.sumComm _ _) else coordinateOrder

def signedRoot (negative : Bool) (r : RootIndex) : RootIndex :=
  if negative then negativeRoot r else r

def matrix (negative : Bool) : Points k →* Matrix (Fin 8) (Fin 8) k where
  toFun g := (pointMatrix k g).submatrix (signedOrder negative) (signedOrder negative)
  map_one' := by rw [pointMatrix_one]; exact Matrix.submatrix_one_equiv _
  map_mul' g h := by rw [pointMatrix_mul]; exact (Matrix.submatrix_mul_equiv _ _ _ _ _).symm

def linear (negative : Bool) : Points k →* GL (Fin 8) k := (matrix k negative).toHomUnits

lemma matrix_injective (negative : Bool) : Function.Injective (matrix k negative) := by
  intro g h hgh
  apply pointMatrix_injective k
  ext i j
  have h := congrFun (congrFun hgh ((signedOrder negative).symm i))
    ((signedOrder negative).symm j)
  simpa [matrix] using h

lemma root_difference_matrix (i j : Fin 4) (hij : i < j) (a : k) :
    pointMatrix k (rootPoint k (difference i j hij) a) =
      1 + Matrix.single (.inl i) (.inl j) a + Matrix.single (.inr j) (.inr i) a := by
  ext p q
  cases p <;> cases q <;>
    rw [pointMatrix_apply, naturalAction_rootPoint] <;>
    simp only [basis_coord_inl, basis_coord_inr, basis_apply] <;>
    norm_num [difference, sumRoot, negativeRoot,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      Pi.single_apply, ite_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.one_apply, Matrix.single_apply,
      eq_comm, sub_eq_add_neg, CharTwo.neg_eq] <;>
    split_ifs <;> simp_all

lemma root_sum_matrix (i j : Fin 4) (hij : i < j) (a : k) :
    pointMatrix k (rootPoint k (sumRoot i j hij) a) =
      1 + Matrix.single (.inl i) (.inr j) a +
        Matrix.single (.inl j) (.inr i) a := by
  ext p q
  cases p <;> cases q <;>
    rw [pointMatrix_apply, naturalAction_rootPoint] <;>
    simp only [basis_coord_inl, basis_coord_inr, basis_apply] <;>
    norm_num [difference, sumRoot, negativeRoot,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
      Pi.single_apply, ite_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.one_apply, Matrix.single_apply,
      eq_comm, sub_eq_add_neg, CharTwo.neg_eq] <;>
    split_ifs <;> simp_all

lemma root_negative_difference_matrix (i j : Fin 4) (hij : i < j) (a : k) :
    pointMatrix k (rootPoint k (negativeRoot (difference i j hij)) a) =
      1 + Matrix.single (.inl j) (.inl i) a +
        Matrix.single (.inr i) (.inr j) a := by
  ext p q
  cases p <;> cases q <;>
    rw [pointMatrix_apply, naturalAction_rootPoint] <;>
    simp only [basis_coord_inl, basis_coord_inr, basis_apply] <;>
    norm_num [difference, sumRoot, negativeRoot,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      Pi.single_apply, ite_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.one_apply, Matrix.single_apply,
      eq_comm, sub_eq_add_neg, CharTwo.neg_eq] <;>
    split_ifs <;> simp_all

lemma root_negative_sum_matrix (i j : Fin 4) (hij : i < j) (a : k) :
    pointMatrix k (rootPoint k (negativeRoot (sumRoot i j hij)) a) =
      1 + Matrix.single (.inr i) (.inl j) a +
        Matrix.single (.inr j) (.inl i) a := by
  ext p q
  cases p <;> cases q <;>
    rw [pointMatrix_apply, naturalAction_rootPoint] <;>
    simp only [basis_coord_inl, basis_coord_inr, basis_apply] <;>
    norm_num [difference, sumRoot, negativeRoot,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
      Pi.single_apply, ite_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.one_apply, Matrix.single_apply,
      eq_comm, sub_eq_add_neg, CharTwo.neg_eq] <;>
    split_ifs <;> simp_all
omit [IsAlgClosed k] [CharP k 2] in
private lemma two_entries_unitriangular (e : Fin 8 ≃ Index)
    (p q r s : Index) (hpq : e.symm p < e.symm q) (hrs : e.symm r < e.symm s)
    (a : k) :
    uUnipotent 8 ((1 + Matrix.single p q a + Matrix.single r s a).submatrix e e) := by
  have ht : Matrix.BlockTriangular
      (1 + Matrix.single p q a + Matrix.single r s a) e.symm :=
    (Matrix.blockTriangular_one.add (Matrix.blockTriangular_single hpq.le a)).add
      (Matrix.blockTriangular_single hrs.le a)
  refine ⟨?_, ?_⟩
  · intro i j hij
    apply ht
    simpa using hij
  · intro i
    have hpq' : p ≠ q := fun h => (ne_of_lt hpq) (congrArg e.symm h)
    have hrs' : r ≠ s := fun h => (ne_of_lt hrs) (congrArg e.symm h)
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply_eq,
      Matrix.single_apply]
    split_ifs <;> simp_all

lemma root_unitriangular (negative : Bool) (r : Fin 12) (a : k) :
    uUnipotent 8 (matrix k negative (rootPoint k (signedRoot negative (rootIndex r)) a)) := by
  change uUnipotent 8 ((pointMatrix k _).submatrix (signedOrder negative) (signedOrder negative))
  cases negative <;> fin_cases r <;>
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte, rootIndex,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one] <;>
    (first | rw [root_difference_matrix] | rw [root_sum_matrix] |
      rw [root_negative_difference_matrix] | rw [root_negative_sum_matrix]) <;>
    apply two_entries_unitriangular <;> decide
/-- The published positive system or its literal negative. -/
def signedRoots (negative : Bool) : Set (pinnedRootData k).Root :=
  if negative then negativeRoots k else positiveRoots k

/-- The root-generated candidate of the selected sign. -/
abbrev unipotent (negative : Bool) := rootGenerated k (signedRoots k negative)

/-- The torus-and-root candidate of the selected sign. -/
abbrev candidate (negative : Bool) := torusRootGenerated k (signedRoots k negative)

lemma exists_signedRoot (negative : Bool) (r : (pinnedRootData k).Root)
    (hr : r ∈ signedRoots k negative) :
    ∃ i : Fin 12, signedRoot negative (rootIndex i) = r.down := by
  cases negative with
  | false =>
    change r ∈ positiveRoots k at hr
    rw [← range_positiveRoot] at hr
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, congrArg ULift.down hi⟩
  | true =>
    change (pinnedRootData k).neg r ∈ positiveRoots k at hr
    rw [← range_positiveRoot] at hr
    obtain ⟨i, hi⟩ := hr
    rw [show r = pinnedRootIndex k r.down from rfl, pinnedRootData_neg] at hi
    have hi' : rootIndex i = negativeRoot r.down := congrArg ULift.down hi
    exact ⟨i, by change negativeRoot (rootIndex i) = r.down
                 rw [hi', negativeRoot_negativeRoot]⟩

/-- Every element generated by roots of one sign is unitriangular. -/
lemma unipotent_unitriangular (negative : Bool) (g : Points k)
    (hg : g ∈ unipotent k negative) :
    uUnipotent 8 (matrix k negative g) := by
  let U := (uUnipotentGL k 8).comap (linear k negative)
  suffices h : (unipotent k negative).toSubgroup ≤ U from h hg
  change Subgroup.closure _ ≤ U
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨r, hr, hx⟩ := hx
  obtain ⟨a, rfl⟩ := (mem_rootClosedSubgroup_iff k r.down x).mp hx
  obtain ⟨i, hi⟩ := exists_signedRoot k negative r hr
  change uUnipotent 8 (matrix k negative (rootPoint k r.down a))
  rw [← hi]
  exact root_unitriangular k negative i a

/-- The torus has no off-diagonal matrix entries in either ordered basis. -/
lemma torus_matrix_offDiagonal (negative : Bool) (g : Points k)
    (hg : g ∈ CorootTorus.closedSubgroup k) (i j : Fin 8) (hij : i ≠ j) :
    matrix k negative g i j = 0 := by
  obtain ⟨t, rfl⟩ := (CorootTorus.mem_iff_parameter k g).mp hg
  change pointMatrix k (CorootTorus.parameter k t)
    (signedOrder negative i) (signedOrder negative j) = 0
  rw [pointMatrix_apply, CorootTorus.naturalAction_parameter, diagonal_basis]
  have h : signedOrder negative i ≠ signedOrder negative j :=
    (signedOrder negative).injective.ne hij
  simp [Module.Basis.coord_apply, h, Ne.symm h]

/-- All candidate elements are triangular in the basis of the chosen sign. -/
lemma candidate_triangular (negative : Bool) (g : Points k)
    (hg : g ∈ candidate k negative) : tTriangular 8 (matrix k negative g) := by
  obtain ⟨t, v, ht, hv, rfl⟩ :=
    (mem_torusRootGenerated_iff k (signedRoots k negative) g).mp hg
  rw [map_mul]
  exact tTriangular_mul 8
    (fun i j hji => torus_matrix_offDiagonal k negative t ht i j (ne_of_gt hji))
    (unipotent_unitriangular k negative v hv).1

/-- Faithful embedding of the candidate in an ordinary triangular group. -/
def candidateToTriangular (negative : Bool) :
    (candidate k negative).toSubgroup →* tTriangularGL k 8 :=
  ((linear k negative).comp (candidate k negative).toSubgroup.subtype).codRestrict
    (tTriangularGL k 8) (fun g => candidate_triangular k negative g g.property)

lemma candidateToTriangular_injective (negative : Bool) :
    Function.Injective (candidateToTriangular k negative) := by
  intro g h hgh
  apply Subtype.ext
  apply matrix_injective k negative
  exact congrArg (fun A : tTriangularGL k 8 => A.1.1) hgh

/-- The genuine point group of either candidate is solvable. -/
lemma candidate_solvable (negative : Bool) :
    Group.IsSolvable (Variety.Point (candidate k negative).carrierVariety) := by
  let : Group.IsSolvable (tTriangularGL k 8) :=
    BorelGeometricConjugacy.triangularGroup_isSolvable 8
  let : Group.IsSolvable (candidate k negative).toSubgroup :=
    Group.isSolvable_of_isSolvable_injective (candidateToTriangular_injective k negative)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Equiv.mulEquiv (candidate k negative).pointEquiv).toMonoidHom)
    (candidate k negative).pointEquiv.injective

/-- Each unipotent candidate embeds faithfully in the unitriangular group. -/
def unipotentToUnitriangular (negative : Bool) :
    (unipotent k negative).toSubgroup →* uUnipotentGL k 8 :=
  ((linear k negative).comp (unipotent k negative).toSubgroup.subtype).codRestrict
    (uUnipotentGL k 8) (fun g => unipotent_unitriangular k negative g g.property)

lemma unipotentToUnitriangular_injective (negative : Bool) :
    Function.Injective (unipotentToUnitriangular k negative) := by
  intro g h hgh
  apply Subtype.ext
  apply matrix_injective k negative
  exact congrArg (fun A : uUnipotentGL k 8 => A.1.1) hgh

/-- A uniform power of two kills every point of either root-generated group. -/
lemma unipotent_pow (negative : Bool) (g : (unipotent k negative).toSubgroup) :
    g ^ 2 ^ 8 = 1 := by
  let f := unipotentToUnitriangular k negative
  let e := Equiv.mulEquiv (uPointEquiv k 8)
  apply unipotentToUnitriangular_injective k negative
  change f (g ^ 2 ^ 8) = f 1
  rw [map_pow, map_one]
  have h := congrArg e (uPoint_pow_primePower_eq_one 2 8 (e.symm (f g)))
  simpa only [map_pow, map_one, MulEquiv.apply_symm_apply] using h

/-- Unipotence is proved on the actual Clifford closed subgroup. -/
lemma unipotent_isUnipotent (negative : Bool) :
    IsUnipotentAlgebraicGroup (unipotent k negative).carrierVariety := by
  intro x
  apply pPowerOrder_implies_unipotent x 2 8
  let e := Equiv.mulEquiv (unipotent k negative).pointEquiv
  apply e.injective
  simpa only [map_pow, map_one] using unipotent_pow k negative (e x)

/-- The signed orders are opposite orders on the same hyperbolic basis. -/
lemma signedOrder_reverse (i : Fin 8) : signedOrder true i = signedOrder false (Fin.rev i) := by
  fin_cases i <;> rfl

/-- The lower candidate has no nonidentity element in the upper root group. -/
lemma opposite_disjoint :
    Disjoint (positiveUnipotent k).toSubgroup (negativeCandidate k).toSubgroup := by
  rw [Subgroup.disjoint_def]
  intro g hu hb
  have hU := unipotent_unitriangular k false g hu
  have hB := candidate_triangular k true g hb
  apply matrix_injective k false
  rw [map_one]
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · have h := hB (i := Fin.rev i) (j := Fin.rev j) (by simpa using hij)
    simpa [matrix, signedOrder_reverse, Matrix.one_apply, ne_of_lt hij] using h
  · simpa using hU.2 i
  · simpa [Matrix.one_apply, ne_of_gt hji] using hU.1 hji
end Triality.SimplyConnected.OppositeBorels.BorelCertification
