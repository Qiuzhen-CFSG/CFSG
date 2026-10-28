module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Remaining
import Mathlib.Tactic.FinCases

/-!
# Common fixed spaces in the SL₃ adjoint graph centralizer

The eight coordinates are the six off-diagonal entries and two diagonal
entries of the literal trace-zero endomorphism space. Matrix identities
identify the graph operator with Gram-conjugate transpose and the root
operator with upper-transvection conjugation. A graph-fixed vector is
determined by five coordinates; a further nonzero root parameter leaves
only three. The parameter field and graph bit also give the actor rank
bound. These inequalities prove the strict binary common-fixed-space
estimate, including fields of order two and four.

`GraphForm` records actual operator coordinates. Its construction from an
arbitrary Schur-linear outer actor is a separate structural obligation;
no normalizer coverage is asserted in this module.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
step 3A, author manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
The coordinate convention extends
`Theory.Representation.PSL3Two.IrreducibleCatalogue.Coordinates`.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint
section Coordinates
variable (F : Type*) [Field F] [CharP F 2]
abbrev Eight := Fin 8 → F

def matrixOf (v : Eight F) : Matrix (Fin 3) (Fin 3) F :=
  !![v 6, v 0, v 1; v 2, v 7, v 3; v 4, v 5, v 6 + v 7]

def readMatrix (a : Matrix (Fin 3) (Fin 3) F) : Eight F :=
  ![a 0 1, a 0 2, a 1 0, a 1 2, a 2 0, a 2 1, a 0 0, a 1 1]

private theorem matrixOf_trace (v : Eight F) : (matrixOf F v).trace = 0 := by
  simp [matrixOf, Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

private theorem matrixOf_readMatrix (a : Matrix (Fin 3) (Fin 3) F)
    (ha : a.trace = 0) : matrixOf F (readMatrix F a) = a := by
  have hdiag : a 0 0 + a 1 1 = a 2 2 := by
    have he : a 0 0 + a 1 1 + a 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_three] using ha
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using
      congrArg (fun x => x + a 2 2) he
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixOf, readMatrix, hdiag]

def coordinates : AdjointSpace F ≃ₗ[F] Eight F where
  toFun f := readMatrix F (LinearMap.toMatrix' f.val)
  invFun v := ⟨(matrixOf F v).toLin', by
    change (LinearMap.trace F (Fin 3 → F)) (matrixOf F v).toLin' = 0
    rw [Matrix.trace_toLin'_eq]
    exact matrixOf_trace F v⟩
  left_inv f := by
    apply Subtype.ext
    change (matrixOf F (readMatrix F (LinearMap.toMatrix' f.val))).toLin' = f.val
    rw [matrixOf_readMatrix, Matrix.toLin'_toMatrix']
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
    exact f.property
  right_inv v := by
    change readMatrix F (LinearMap.toMatrix' (matrixOf F v).toLin') = v
    rw [LinearMap.toMatrix'_toLin']
    funext i
    fin_cases i <;> rfl
  map_add' f h := by
    change readMatrix F (LinearMap.toMatrix' (f.val + h.val)) = _
    rw [map_add]
    funext i
    fin_cases i <;> rfl
  map_smul' c f := by
    change readMatrix F (LinearMap.toMatrix' (c • f.val)) = _
    rw [map_smul]
    funext i
    fin_cases i <;> rfl

theorem matrixOf_coordinates (x : AdjointSpace F) :
    matrixOf F (coordinates F x) = LinearMap.toMatrix' x.val := by
  apply matrixOf_readMatrix
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  exact x.property

/-- The Gram matrix with a symplectic plane and a nonsingular line. -/
def gram : Matrix (Fin 3) (Fin 3) F := !![0,1,0; 1,0,0; 0,0,1]

def unipotent (a : F) : Matrix (Fin 3) (Fin 3) F := !![1,a,0; 0,1,0; 0,0,1]

/-- Conjugation by the Gram matrix after transpose, in actual adjoint coordinates. -/
def graphCoordinates (v : Eight F) : Eight F :=
  ![v 0, v 5, v 2, v 4, v 3, v 1, v 7, v 6]

/-- Conjugation by the upper transvection with parameter a. -/
def shearCoordinates (a : F) (v : Eight F) : Eight F :=
  ![v 0 + a * (v 6 + v 7) + a^2 * v 2, v 1 + a * v 3,
    v 2, v 3, v 4, v 5 + a * v 4, v 6 + a * v 2, v 7 + a * v 2]

omit [CharP F 2] in
theorem matrixOf_graphCoordinates (v : Eight F) :
    matrixOf F (graphCoordinates F v) = gram F * (matrixOf F v).transpose * gram F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOf, graphCoordinates, gram, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, add_comm]

theorem matrixOf_shearCoordinates (a : F) (v : Eight F) :
    matrixOf F (shearCoordinates F a v) = unipotent F a * matrixOf F v * unipotent F a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOf, shearCoordinates, unipotent, Matrix.mul_apply, Fin.sum_univ_three,
      pow_two, mul_add, add_mul, mul_assoc, add_assoc, CharTwo.add_self_eq_zero] <;> ring_nf
  simp [CharTwo.two_eq_zero]

omit [CharP F 2] in
@[simp] theorem shearCoordinates_zero (v : Eight F) : shearCoordinates F 0 v = v := by
  funext i
  fin_cases i <;> simp [shearCoordinates]

end Coordinates

variable (B : BinaryField) {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G)

/-- Coordinates for an elementary actor containing the graph involution, after
conjugating its inner part into the upper root group of the graph centralizer.
These are actual operator identities; no dimension or rank bound is a field. -/
structure GraphForm where
  equiv : V ≃ₗ[ZMod 2] Eight B.Carrier
  parameter : A →* Multiplicative (B.Carrier × ZMod 2)
  injective : Function.Injective parameter
  graph_mem : ∃ t : A, (parameter t).toAdd = (0,1)
  action : ∀ (t : A) (v : V), equiv (ρ t.val v) =
    shearCoordinates B.Carrier (parameter t).toAdd.1
      (if (parameter t).toAdd.2 = 0 then equiv v
       else graphCoordinates B.Carrier (equiv v))



namespace GraphForm
variable {B ρ A} (C : GraphForm B ρ A)

private theorem field_finrank : Module.finrank (ZMod 2) B.Carrier = B.degree := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := B.Carrier)
  rw [Nat.card_zmod, B.card_eq] at hc
  exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm

include C

/-- The graph centralizer's root parameter and graph bit bound the actor rank. -/
theorem rank_le : rank A ≤ B.degree + 1 := by
  have hc := Nat.card_le_card_of_injective C.parameter C.injective
  have hp : Nat.card (Multiplicative (B.Carrier × ZMod 2)) = 2 ^ (B.degree + 1) := by
    change Nat.card (B.Carrier × ZMod 2) = _
    rw [Nat.card_prod, Nat.card_zmod, B.card_eq, pow_succ]
  rw [hp] at hc
  exact (Nat.log_mono_right hc).trans_eq (Nat.log_pow (by decide : 1 < 2) _)

private theorem graph_fixed (v : fixedSpace ρ A) :
    graphCoordinates B.Carrier (C.equiv v) = C.equiv v := by
  obtain ⟨t, ht⟩ := C.graph_mem
  have hv := congrArg C.equiv (v.property t)
  change C.equiv (ρ t.val v) = C.equiv v at hv
  rw [C.action] at hv
  simpa [ht] using hv

private theorem shear_fixed (t : A) (v : fixedSpace ρ A) :
    shearCoordinates B.Carrier (C.parameter t).toAdd.1 (C.equiv v) = C.equiv v := by
  have hv := congrArg C.equiv (v.property t)
  change C.equiv (ρ t.val v) = C.equiv v at hv
  rw [C.action] at hv
  split_ifs at hv with h
  · exact hv
  · rwa [C.graph_fixed v] at hv

/-- Five coordinates determine a graph-fixed trace-zero endomorphism. -/
theorem fixed_finrank_le_five [FiniteDimensional (ZMod 2) V] :
    Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 5 * B.degree := by
  let f : fixedSpace ρ A →ₗ[ZMod 2] (Fin 5 → B.Carrier) :=
    LinearMap.pi (fun i => (LinearMap.proj (![0,1,2,3,6] i)).comp
      (C.equiv.toLinearMap.comp (fixedSpace ρ A).subtype))
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro v hv
    have h0 : C.equiv v 0 = 0 := congrFun hv 0
    have h1 : C.equiv v 1 = 0 := congrFun hv 1
    have h2 : C.equiv v 2 = 0 := congrFun hv 2
    have h3 : C.equiv v 3 = 0 := congrFun hv 3
    have h6 : C.equiv v 6 = 0 := congrFun hv 4
    have h5 := congrFun (C.graph_fixed v) 1
    have h4 := congrFun (C.graph_fixed v) 3
    have h7 := congrFun (C.graph_fixed v) 6
    simp [graphCoordinates] at h5 h4 h7
    apply Subtype.ext
    apply C.equiv.injective
    change C.equiv (v : V) = C.equiv (0 : V)
    rw [map_zero]
    funext i
    fin_cases i <;> simp_all
  have h := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_pi_fintype, field_finrank] using h

/-- A nonzero root parameter cuts the common fixed space down to three
coordinates, including over the fields of order two and four. -/
theorem fixed_finrank_le_three [FiniteDimensional (ZMod 2) V]
    (t : A) (ht : (C.parameter t).toAdd.1 ≠ 0) :
    Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 3 * B.degree := by
  let f : fixedSpace ρ A →ₗ[ZMod 2] (Fin 3 → B.Carrier) :=
    LinearMap.pi (fun i => (LinearMap.proj (![0,1,6] i)).comp
      (C.equiv.toLinearMap.comp (fixedSpace ρ A).subtype))
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro v hv
    have h0 : C.equiv v 0 = 0 := congrFun hv 0
    have h1 : C.equiv v 1 = 0 := congrFun hv 1
    have h6 : C.equiv v 6 = 0 := congrFun hv 2
    have h5 := congrFun (C.graph_fixed v) 1
    have h4 := congrFun (C.graph_fixed v) 3
    have h7 := congrFun (C.graph_fixed v) 6
    simp [graphCoordinates] at h5 h4 h7
    have h2 := congrFun (C.shear_fixed t v) 6
    have h3 := congrFun (C.shear_fixed t v) 1
    simp [shearCoordinates] at h2 h3
    have h2z : C.equiv v 2 = 0 := h2.resolve_left ht
    have h3z : C.equiv v 3 = 0 := h3.resolve_left ht
    apply Subtype.ext
    apply C.equiv.injective
    change C.equiv (v : V) = C.equiv (0 : V)
    rw [map_zero]
    funext i
    fin_cases i <;> simp_all
  have h := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_pi_fintype, field_finrank] using h

/-- The concrete graph/root normal form excludes every elementary offender
of ratio at most two, with the literal common fixed space. -/
theorem estimate [FiniteDimensional (ZMod 2) V] :
    2 * rank A < fixedCodim ρ A := by
  have hd : Module.finrank (ZMod 2) V = 8 * B.degree := by
    rw [C.equiv.finrank_eq]
    simp [Eight, Module.finrank_pi_fintype, field_finrank]
  have hsum := fixedCodim_add_finrank ρ A
  rw [hd] at hsum
  by_cases ht : ∃ t : A, (C.parameter t).toAdd.1 ≠ 0
  · obtain ⟨t, ht⟩ := ht
    have hfixed := C.fixed_finrank_le_three t ht
    have hr := C.rank_le
    have hp := B.degree_pos
    omega
  · push Not at ht
    have hi : Function.Injective (fun t : A => (C.parameter t).toAdd.2) := by
      intro x y he
      apply C.injective
      change (C.parameter x).toAdd = (C.parameter y).toAdd
      apply Prod.ext
      · rw [ht x, ht y]
      · exact he
    have hc := Nat.card_le_card_of_injective _ hi
    rw [Nat.card_zmod] at hc
    have hr : rank A ≤ 1 := by
      exact (Nat.log_mono_right hc).trans_eq (by decide : Nat.log 2 2 = 1)
    have hfixed := C.fixed_finrank_le_five
    have hp := B.degree_pos
    omega
end GraphForm

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint
