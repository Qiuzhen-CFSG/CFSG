module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Construction
public import Theory.GroupAction.AutomorphismFixedResidualTransport

/-!
# The explicit graph-field representative on Sp₄

The exterior-square graph automorphism squares to entrywise Frobenius.
Consequently its `(2m+1)`st power has square one over a field of order
`2^(2m+1)`, and its fixed matrices satisfy `graphMatrix g = theta(g)` with
`theta(x) = x^(2^(m+1))`. The representative is nontrivial, as detected on a
long-root matrix. These calculations use the genuine matrix automorphism.

Restriction to the characteristic commutator subgroup gives the action on
Sp₄(2)′ needed in the binary exception. Entrywise field transport commutes
with the action and gives a compatible equivalence of fixed groups. The
coordinate reindexing at the end fixes the matrix comparison convention for
the Suzuki generators: the symplectic pairs become `(0,3)` and `(1,2)`.

This module does not identify the fixed matrices with the Suzuki generated
subgroup or compute their two-residuals.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 16.1.4(7), printed p.1171, and the Sylow-index use
in 16.1.8, printed p.1173. The exceptional automorphism itself is constructed
in `ExceptionalGraph.Construction` from the GLS3 exterior-square formula.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual
open ExceptionalGraph
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem field_pow (σ : F ≃+* F) (k : ℕ) :
    (fieldAutomorphism σ) ^ k = fieldAutomorphism (σ ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    rfl

/-- Even powers of the graph automorphism are the specified field maps. -/
theorem graphAut_even (k : ℕ) :
    graphAut (F := F) ^ (2 * k) =
      fieldAutomorphism (iterateFrobeniusEquiv F 2 k) := by
  rw [pow_mul, graphAut_square, field_pow, iterateFrobeniusEquiv_eq_pow]

/-- The explicit odd graph power whose fixed group is to be identified. -/
def graphFieldAut (m : ℕ) : MulAut (Sp F) := graphAut ^ (2 * m + 1)

/-- Entrywise formula for the graph-field representative. -/
theorem graphFieldAut_apply (m : ℕ) (g : Sp F) :
    (graphFieldAut m g).val =
      (graphMatrix g.val).map (iterateFrobeniusEquiv F 2 m) := by
  change ((graphAut ^ (2 * m + 1)) g).val = _
  rw [pow_succ, MulAut.mul_apply, graphAut_even]
  rfl

private theorem field_period {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    fieldAutomorphism (iterateFrobeniusEquiv F 2 n) = 1 := by
  let := Fintype.ofFinite F
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  ext i j
  change (g.val i j) ^ (2 ^ n) = g.val i j
  rw [← hF, Nat.card_eq_fintype_card, FiniteField.pow_card]

/-- The field-size hypothesis makes the representative involutory. -/
theorem graphFieldAut_sq (m : ℕ) (hF : Nat.card F = 2 ^ (2 * m + 1)) :
    (graphFieldAut (F := F) m) ^ 2 = 1 := by
  change (graphAut ^ (2 * m + 1)) ^ 2 = _
  rw [← pow_mul, Nat.mul_comm (2 * m + 1), graphAut_even, field_period hF]

/-- The exact fixed-matrix equation, without any group-family identification. -/
theorem mem_fixed_iff (m : ℕ) (g : Sp F) :
    g ∈ (graphFieldAut m).fixedSubgroup ↔
      graphMatrix g.val = g.val.map (iterateFrobeniusEquiv F 2 (m + 1)) := by
  rw [MulAut.mem_fixedSubgroup]
  have he : graphAut (F := F) * graphFieldAut m =
      fieldAutomorphism (iterateFrobeniusEquiv F 2 (m + 1)) := by
    change graphAut * graphAut ^ (2 * m + 1) = _
    rw [← pow_succ']
    convert graphAut_even (F := F) (m + 1) using 1
    congr 1
  constructor
  · intro hg
    have hh := congrArg graphAut hg
    rw [← MulAut.mul_apply, he] at hh
    exact (congrArg Subtype.val hh).symm
  · intro hg
    apply graphAut.injective
    rw [← MulAut.mul_apply, he]
    exact Subtype.ext hg.symm

open Representation.OneCohomology.SymplecticFour in
/-- A long-root matrix witnesses nontriviality of every odd graph power. -/
theorem graphFieldAut_ne_one (m : ℕ) : graphFieldAut (F := F) m ≠ 1 := by
  intro he
  have h := congrArg (fun a : MulAut (Sp F) =>
    (a (rootElement 0 1)).val (Sum.inl 0) (Sum.inr 0)) he
  rw [graphFieldAut_apply] at h
  simp [graphMatrix, minor, first, second, rootElement, rootMatrix,
    Matrix.map_apply, Matrix.fromBlocks, Matrix.single] at h

/-- Restriction of the same genuine action to the literal derived carrier. -/
def derivedGraphFieldAut (m : ℕ) : MulAut (commutator (Sp F)) :=
  restrict (graphFieldAut m) (commutator (Sp F))
    (Subgroup.characteristic_iff_map_eq.mp inferInstance _)

@[simp] theorem derivedGraphFieldAut_coe (m : ℕ) (g : commutator (Sp F)) :
    (derivedGraphFieldAut m g : Sp F) = graphFieldAut m g := rfl

/-- The restricted action also squares to the identity. -/
theorem derivedGraphFieldAut_sq (m : ℕ)
    (hF : Nat.card F = 2 ^ (2 * m + 1)) :
    (derivedGraphFieldAut (F := F) m) ^ 2 = 1 := by
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  change graphFieldAut m (graphFieldAut m (g : Sp F)) = g
  have he := congrArg (fun a : MulAut (Sp F) => a g) (graphFieldAut_sq m hF)
  exact he

/-- Fixed points of the restriction are the fixed points lying in the commutator. -/
theorem mem_derived_fixed_iff (m : ℕ) (g : commutator (Sp F)) :
    g ∈ (derivedGraphFieldAut m).fixedSubgroup ↔
      (g : Sp F) ∈ (graphFieldAut m).fixedSubgroup := by
  simp only [MulAut.mem_fixedSubgroup, Subtype.ext_iff, derivedGraphFieldAut_coe]

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- Entrywise field identifications intertwine the actual graph-field actions. -/
theorem graphFieldAut_fieldEquiv (m : ℕ) (e : F ≃+* K) (g : Sp F) :
    Binary.fieldEquivSp e (graphFieldAut m g) =
      graphFieldAut m (Binary.fieldEquivSp e g) := by
  apply Subtype.ext
  ext i j
  simp [Binary.fieldEquivSp_apply, graphFieldAut_apply, Matrix.map_apply,
    iterateFrobenius_def, graphMatrix, minor]

/-- Compatible transport of the full fixed subgroup along a field equivalence. -/
def fixedFieldEquiv (m : ℕ) (e : F ≃+* K) :
    (graphFieldAut (F := F) m).fixedSubgroup ≃*
      (graphFieldAut (F := K) m).fixedSubgroup :=
  MulAut.fixedSubgroupEquivOfCompatible (Binary.fieldEquivSp e) _ _
    (graphFieldAut_fieldEquiv m e)

@[simp] theorem fixedFieldEquiv_coe (m : ℕ) (e : F ≃+* K)
    (g : (graphFieldAut (F := F) m).fixedSubgroup) :
    (fixedFieldEquiv m e g : Sp K) = Binary.fieldEquivSp e g := by
  exact MulAut.fixedSubgroupEquivOfCompatible_apply _ _ _ _ _

/-- The standard Suzuki basis has symplectic pairs `(0,3)` and `(1,2)`. -/
def suzukiIndex : (Fin 2 ⊕ Fin 2) ≃ Fin 4 where
  toFun := Sum.elim ![0, 1] ![3, 2]
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 0]
  left_inv i := by rcases i with i | i <;> fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The actual symplectic matrix in Suzuki's coordinates, with a specified
coefficient-field identification. -/
def matrixCoordinates (e : F ≃+* K) (g : Sp F) : Matrix (Fin 4) (Fin 4) K :=
  (g.val.map e).submatrix suzukiIndex.symm suzukiIndex.symm

omit [Finite F] [CharP F 2] [Finite K] [CharP K 2] in
theorem matrixCoordinates_injective (e : F ≃+* K) :
    Function.Injective (matrixCoordinates e) := by
  intro g h he
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) K =>
    M (suzukiIndex i) (suzukiIndex j)) he
  simp only [matrixCoordinates, Matrix.submatrix_apply, Matrix.map_apply,
    Equiv.symm_apply_apply] at hh
  exact e.injective hh

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual
