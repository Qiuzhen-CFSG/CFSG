module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120.Code
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Trace

/-!
# The native code adjoint in 120 coordinates

Conjugation by the actual eleven-dimensional code action preserves trace.
Off-diagonal matrix units, followed by E_ii − E_10,10, form the certified
coordinate basis of its trace kernel. Over the binary field these differences
are the sums specified by the source comparison.

Source: James, J. Algebra 27 (1973), 57–111; GM02, Proposition 5.1.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120
open Sporadic.Mathieu
open scoped BigOperators

abbrev CodeMat := Matrix (Fin 11) (Fin 11) (ZMod 2)

def nativeCodeMatrix (g : M24) : CodeMat :=
  LinearMap.toMatrix' (coordinateCodeRepresentation g)

lemma nativeCodeMatrix_one : nativeCodeMatrix 1 = 1 := by
  simp [nativeCodeMatrix]

lemma nativeCodeMatrix_mul (g h : M24) :
    nativeCodeMatrix (g * h) = nativeCodeMatrix g * nativeCodeMatrix h := by
  simp [nativeCodeMatrix, LinearMap.toMatrix'_mul]

def conjugation : Representation (ZMod 2) M24 CodeMat where
  toFun g :=
    { toFun X := nativeCodeMatrix g * X * nativeCodeMatrix g⁻¹
      map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' c X := by simp }
  map_one' := by ext X i j; simp [nativeCodeMatrix_one]
  map_mul' g h := by
    ext X i j
    change (nativeCodeMatrix (g * h) * X * nativeCodeMatrix (g * h)⁻¹) i j =
      (nativeCodeMatrix g * (nativeCodeMatrix h * X * nativeCodeMatrix h⁻¹) *
        nativeCodeMatrix g⁻¹) i j
    simp [nativeCodeMatrix_mul, _root_.mul_inv_rev, Matrix.mul_assoc]

/-- The actual trace-zero invariant subspace of the native code endomorphisms. -/
def traceZero : Subrepresentation conjugation where
  toSubmodule := (Matrix.traceLinearMap (Fin 11) (ZMod 2) (ZMod 2)).ker
  apply_mem_toSubmodule g X hX := by
    change Matrix.trace (nativeCodeMatrix g * X * nativeCodeMatrix g⁻¹) = 0
    rw [Matrix.trace_mul_cycle, ← nativeCodeMatrix_mul, inv_mul_cancel,
      nativeCodeMatrix_one, Matrix.one_mul]
    exact hX

abbrev TraceZeroSpace := (Matrix.traceLinearMap (Fin 11) (ZMod 2) (ZMod 2)).ker
abbrev traceZeroRepresentation : Representation (ZMod 2) M24 TraceZeroSpace :=
  traceZero.toRepresentation

theorem finrank_traceZeroSpace : Module.finrank (ZMod 2) TraceZeroSpace = 120 := by
  have hs : Function.Surjective (Matrix.traceLinearMap (Fin 11) (ZMod 2) (ZMod 2)) := by
    intro c
    exact ⟨Matrix.single 0 0 c, by simp⟩
  have hh := (Matrix.traceLinearMap (Fin 11) (ZMod 2) (ZMod 2)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self] at hh
  have hm : Module.finrank (ZMod 2) CodeMat = 121 := by
    simp [CodeMat, Module.finrank_matrix]
  change 1 + Module.finrank (ZMod 2) TraceZeroSpace = Module.finrank (ZMod 2) CodeMat at hh
  omega

/-- Off-diagonal entries in lexicographic order, then the first ten diagonal entries. -/
def position : Fin 120 → Fin 11 × Fin 11 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10),
    (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10),
    (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10),
    (3, 0), (3, 1), (3, 2), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10),
    (4, 0), (4, 1), (4, 2), (4, 3), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10),
    (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10),
    (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 7), (6, 8), (6, 9), (6, 10),
    (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9), (7, 10),
    (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 9), (8, 10),
    (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 10),
    (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9),
    (0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9)]

/-- The inverse slot formula also certifies the ordering of the basis. -/
def positionSlot (p : Fin 11 × Fin 11) : ℕ :=
  if p.1 = p.2 then 110 + p.1.val
  else 10 * p.1.val + (if p.2 < p.1 then p.2.val else p.2.val - 1)

lemma positionSlot_position : ∀ j : Fin 120, positionSlot (position j) = j.val := by
  decide +kernel

lemma position_injective : Function.Injective position := by
  intro i j h
  apply Fin.ext
  simpa only [positionSlot_position] using congrArg positionSlot h

lemma position_ne_corner : ∀ j : Fin 120, position j ≠ (10, 10) := by
  decide +kernel

def traceZeroMatrix (j : Fin 120) : CodeMat :=
  Matrix.single (position j).1 (position j).2 1 -
    if (position j).1 = (position j).2 then Matrix.single 10 10 1 else 0

lemma trace_traceZeroMatrix (j : Fin 120) : Matrix.trace (traceZeroMatrix j) = 0 := by
  by_cases h : (position j).1 = (position j).2
  · simp [traceZeroMatrix, h]
  · simp [traceZeroMatrix, h, Matrix.trace_single_eq_of_ne _ _ _ h]

def traceZeroVector (j : Fin 120) : TraceZeroSpace :=
  ⟨traceZeroMatrix j, trace_traceZeroMatrix j⟩

def adjointCoordinates : TraceZeroSpace →ₗ[ZMod 2] (Fin 120 → ZMod 2) where
  toFun X i := X.val (position i).1 (position i).2
  map_add' X Y := by rfl
  map_smul' c X := by rfl

lemma adjointCoordinates_vector (j : Fin 120) :
    adjointCoordinates (traceZeroVector j) = Pi.single j 1 := by
  ext i
  have he : ((position j).1 = (position i).1 ∧ (position j).2 = (position i).2) ↔ j = i := by
    rw [← Prod.ext_iff, position_injective.eq_iff]
  have hc : ¬ ((10 : Fin 11) = (position i).1 ∧ (10 : Fin 11) = (position i).2) := by
    intro h
    exact position_ne_corner i (Prod.ext h.1.symm h.2.symm)
  change traceZeroMatrix j (position i).1 (position i).2 = (Pi.single j 1 : Fin 120 → ZMod 2) i
  unfold traceZeroMatrix
  split_ifs <;> simp only [Matrix.sub_apply, Matrix.single, Matrix.of_apply, he, hc,
    if_false, sub_zero, Matrix.zero_apply, Pi.single_apply, eq_comm]

def adjointSection : (Fin 120 → ZMod 2) →ₗ[ZMod 2] TraceZeroSpace :=
  ∑ j, (LinearMap.proj j).smulRight (traceZeroVector j)

lemma adjointSection_single (j : Fin 120) :
    adjointSection (Pi.single j 1) = traceZeroVector j := by
  simp [adjointSection, Pi.single_apply]

lemma adjointCoordinates_section : adjointCoordinates.comp adjointSection = LinearMap.id := by
  apply pi_ext_one
  intro j
  simp only [LinearMap.comp_apply, adjointSection_single, adjointCoordinates_vector,
    LinearMap.id_apply]

lemma adjointCoordinates_surjective : Function.Surjective adjointCoordinates := by
  intro v
  exact ⟨adjointSection v, LinearMap.congr_fun adjointCoordinates_section v⟩

/-- The specified matrix units form a basis, rather than only a dimension match. -/
def adjointEquiv : TraceZeroSpace ≃ₗ[ZMod 2] (Fin 120 → ZMod 2) :=
  LinearEquiv.ofBijective adjointCoordinates ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_traceZeroSpace]; simp)).mpr adjointCoordinates_surjective,
    adjointCoordinates_surjective⟩

lemma adjointEquiv_symm_single (j : Fin 120) :
    adjointEquiv.symm (Pi.single j 1) = traceZeroVector j := by
  apply adjointEquiv.injective
  simp only [LinearEquiv.apply_symm_apply]
  exact (adjointCoordinates_vector j).symm

def adjointBasis : Module.Basis (Fin 120) (ZMod 2) TraceZeroSpace :=
  Module.Basis.ofEquivFun adjointEquiv

lemma adjointBasis_apply (j : Fin 120) : adjointBasis j = traceZeroVector j :=
  by simpa only [adjointBasis, Module.Basis.coe_ofEquivFun] using adjointEquiv_symm_single j

/-- A lawful native M24 representation, independent of any group presentation. -/
def adjointRepresentation : Representation (ZMod 2) M24 (Fin 120 → ZMod 2) :=
  adjointEquiv.conjRingEquiv.toMonoidHom.comp traceZeroRepresentation

lemma adjointRepresentation_single (g : M24) (j i : Fin 120) :
    adjointRepresentation g (Pi.single j 1) i =
      (nativeCodeMatrix g * traceZeroMatrix j * nativeCodeMatrix g⁻¹)
        (position i).1 (position i).2 := by
  change adjointEquiv (traceZeroRepresentation g (adjointEquiv.symm (Pi.single j 1))) i = _
  rw [adjointEquiv_symm_single]
  rfl

/-- The represented endomorphism is precisely conjugation by the code action. -/
lemma conjugation_toLin (g : M24) (X : CodeMat) :
    Matrix.toLin' (conjugation g X) =
      ((coordinateCodeRepresentation g).comp (Matrix.toLin' X)).comp
        (coordinateCodeRepresentation g⁻¹) := by
  change Matrix.toLin' (nativeCodeMatrix g * X * nativeCodeMatrix g⁻¹) = _
  simp only [Matrix.toLin'_mul, nativeCodeMatrix, Matrix.toLin'_toMatrix']

lemma codeMatrix_mul_inverse (a : Fin 2) : codeMatrix a * codeInverseMatrix a = 1 := by
  ext i j
  dsimp only [Matrix.mul_apply, codeMatrix, codeInverseMatrix, packedMatrix, Matrix.one_apply]
  revert a i j
  decide +kernel

lemma nativeCodeMatrix_actor (a : Fin 2) : nativeCodeMatrix (actor a) = codeMatrix a :=
  coordinateCodeRepresentation_actor a

lemma nativeCodeMatrix_actor_inv (a : Fin 2) :
    nativeCodeMatrix (actor a)⁻¹ = codeInverseMatrix a := by
  have hn : codeMatrix a * nativeCodeMatrix (actor a)⁻¹ = 1 := by
    rw [← nativeCodeMatrix_actor, ← nativeCodeMatrix_mul, mul_inv_cancel, nativeCodeMatrix_one]
  have hc := _root_.mul_eq_one_comm.mp (codeMatrix_mul_inverse a)
  calc
    nativeCodeMatrix (actor a)⁻¹ = 1 * nativeCodeMatrix (actor a)⁻¹ := (Matrix.one_mul _).symm
    _ = (codeInverseMatrix a * codeMatrix a) * nativeCodeMatrix (actor a)⁻¹ := by rw [hc]
    _ = codeInverseMatrix a * (codeMatrix a * nativeCodeMatrix (actor a)⁻¹) := Matrix.mul_assoc ..
    _ = codeInverseMatrix a := by rw [hn, Matrix.mul_one]

private lemma conjugate_single_entry (A B : CodeMat) (k l i j : Fin 11) :
    (A * Matrix.single k l 1 * B : CodeMat) i j = A i k * B l j := by
  simp [Matrix.mul_apply, Matrix.single, ite_and]

/-- A rank-one formula avoids expanding two eleven-dimensional matrix products
for every one of the 14,400 output entries. -/
def adjointEntry (a : Fin 2) (i j : Fin 120) : ZMod 2 :=
  codeMatrix a (position i).1 (position j).1 *
      codeInverseMatrix a (position j).2 (position i).2 -
    if (position j).1 = (position j).2 then
      codeMatrix a (position i).1 10 * codeInverseMatrix a 10 (position i).2 else 0

lemma adjointRepresentation_actor_entry (a : Fin 2) (i j : Fin 120) :
    LinearMap.toMatrix' (adjointRepresentation (actor a)) i j = adjointEntry a i j := by
  rw [LinearMap.toMatrix'_apply, adjointRepresentation_single,
    nativeCodeMatrix_actor, nativeCodeMatrix_actor_inv]
  by_cases h : (position j).1 = (position j).2
  · simp only [traceZeroMatrix, if_pos h, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.sub_apply, conjugate_single_entry, adjointEntry]
  · simp only [traceZeroMatrix, if_neg h, sub_zero, conjugate_single_entry, adjointEntry]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120
