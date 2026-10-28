module

public import Theory.Representation.SymplecticNatural
public import Theory.Representation.FirstCohomology
public import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# A nonprincipal cocycle for the natural derived symplectic four-space

For the split quadratic form `q(x) = x₀x₂ + x₁x₃`, preservation of its
polar form gives
`q(xg) = q(x) + ∑ i, xᵢ² q(rowᵢ(g))`.
Taking the inverse Frobenius of the row defects therefore defines a crossed
homomorphism into the natural column representation. Restriction gives a
cocycle for the actual derived subgroup, including over the binary field.

Three explicit commutators of binary transvections prove nonprincipality.
Their matrices are checked by kernel reduction over `ZMod 2`, then mapped to
any characteristic-two field. The equations for a hypothetical principal
vector force both its first coordinate to be one and to be zero.

This supplies the nonzero class in the calculation of Aschbacher--Smith,
*The Classification of Quasithin Groups*, Lemma I.1.6(5), printed p.408
(PDF p.419). The upper bound on first cohomology is a separate calculation.
-/

@[expose] public section

open Matrix
open scoped commutatorElement
namespace Representation.OneCohomology.SymplecticFour
variable {K : Type*} [Field K] [CharP K 2]
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

/-- The split quadratic form whose polar form is the characteristic-two `J`. -/
def rowQuadratic (x : (Fin 2 ⊕ Fin 2) → K) : K := x a * x c + x b * x d

private lemma pairing_rows (g : Matrix.symplecticGroup (Fin 2) K) (i j : Fin 2 ⊕ Fin 2) :
    g.val i a * g.val j c + g.val i b * g.val j d +
      g.val i c * g.val j a + g.val i d * g.val j b = Matrix.J (Fin 2) K i j := by
  have h := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => M i j) g.property
  simpa [Matrix.mul_apply, Matrix.J, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks, Matrix.one_apply, Matrix.transpose_apply, CharTwo.neg_eq,
    add_assoc, add_comm, add_left_comm] using h

/-- The quadratic defect of a symplectic matrix is diagonal. -/
lemma rowQuadratic_vecMul (g : Matrix.symplecticGroup (Fin 2) K)
    (x : (Fin 2 ⊕ Fin 2) → K) :
    rowQuadratic (Matrix.vecMul x g.val) = rowQuadratic x +
      ∑ j, x j ^ 2 * rowQuadratic (g.val j) := by
  have hab := pairing_rows g a b
  have hac := pairing_rows g a c
  have had := pairing_rows g a d
  have hbc := pairing_rows g b c
  have hbd := pairing_rows g b d
  have hcd := pairing_rows g c d
  norm_num [Matrix.J, Matrix.fromBlocks, Matrix.of_apply, CharTwo.neg_eq] at hab hac had hbc hbd hcd
  simp only [rowQuadratic, Matrix.vecMul, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_two]
  linear_combination x a * x b * hab + x a * x c * hac + x a * x d * had +
    x b * x c * hbc + x b * x d * hbd + x c * x d * hcd

variable [Finite K]

/-- The square roots of the row defects form a natural-module cocycle. -/
noncomputable def quadraticCocycle : cocycles (symplecticNatural (k := K) 2) :=
  ⟨fun g i => (frobeniusEquiv K 2).symm (rowQuadratic (g.val i)), by
    intro g h
    funext i
    apply CharTwo.sq_injective (R := K)
    change ((frobeniusEquiv K 2).symm (rowQuadratic ((g * h).val i))) ^ 2 =
      (Matrix.mulVec g.val (fun j => (frobeniusEquiv K 2).symm (rowQuadratic (h.val j))) i +
        (frobeniusEquiv K 2).symm (rowQuadratic (g.val i))) ^ 2
    simp only [CharTwo.add_sq, frobeniusEquiv_symm_pow_p, Matrix.mulVec, dotProduct,
      CharTwo.sum_sq, mul_pow]
    exact (rowQuadratic_vecMul h (g.val i)).trans (add_comm _ _)⟩

/-- Restriction of the quadratic-defect cocycle to the actual derived group. -/
noncomputable def derivedQuadraticCocycle : cocycles (symplecticDerivedNatural (k := K) 2) :=
  ⟨fun g => (quadraticCocycle (K := K)).val g.val, fun g h =>
    (quadraticCocycle (K := K)).property g.val h.val⟩

/-- Coordinate formula for the cocycle on the derived subgroup. -/
lemma derivedQuadraticCocycle_apply
    (g : commutator (Matrix.symplecticGroup (Fin 2) K)) (i : Fin 2 ⊕ Fin 2) :
    (derivedQuadraticCocycle (K := K)).val g i =
      (frobeniusEquiv K 2).symm (rowQuadratic (g.val.val i)) := rfl

/-- Squaring a cocycle coordinate recovers the corresponding row defect. -/
lemma derivedQuadraticCocycle_apply_sq
    (g : commutator (Matrix.symplecticGroup (Fin 2) K)) (i : Fin 2 ⊕ Fin 2) :
    (derivedQuadraticCocycle (K := K)).val g i ^ 2 = rowQuadratic (g.val.val i) :=
  frobeniusEquiv_symm_pow_p K 2 _

private def binaryMap : Matrix.symplecticGroup (Fin 2) (ZMod 2) →*
    Matrix.symplecticGroup (Fin 2) K where
  toFun g := ⟨g.val.map (ZMod.castHom (dvd_refl 2) K),
    SymplecticGroup.map_mem g.property (ZMod.castHom (dvd_refl 2) K)⟩
  map_one' := Subtype.ext (Matrix.map_one _ (map_zero _) (map_one _))
  map_mul' _ _ := Subtype.ext Matrix.map_mul

private def binaryTransvection (v : (Fin 2 ⊕ Fin 2) → ZMod 2) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  1 + Matrix.of (fun i j => v i * (Sum.elim (fun k => v (Sum.inr k))
    (fun k => v (Sum.inl k)) j))

private def binaryT (v : (Fin 2 ⊕ Fin 2) → ZMod 2) :
    Matrix.symplecticGroup (Fin 2) (ZMod 2) :=
  ⟨binaryTransvection v, by
    have h : ∀ v : (Fin 2 ⊕ Fin 2) → ZMod 2,
      binaryTransvection v * Matrix.J (Fin 2) (ZMod 2) * (binaryTransvection v)ᵀ =
        Matrix.J (Fin 2) (ZMod 2) := by decide
    exact h v⟩

private def binaryWitness (j : Fin 3) : Matrix.symplecticGroup (Fin 2) (ZMod 2) :=
  let u : (Fin 2 ⊕ Fin 2) → ZMod 2 :=
    if j = 1 then Sum.elim ![0, 0] ![1, 0] else Sum.elim ![0, 0] ![0, 1]
  let v : (Fin 2 ⊕ Fin 2) → ZMod 2 :=
    if j = 0 then Sum.elim ![0, 1] ![0, 0]
    else if j = 1 then Sum.elim ![1, 0] ![0, 0]
    else Sum.elim ![0, 1] ![1, 0]
  ⁅binaryT u, binaryT v⁆

private lemma binaryWitness_mem (j : Fin 3) :
    binaryWitness j ∈ commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) := by
  rw [commutator_def]
  unfold binaryWitness
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private def witness (j : Fin 3) : commutator (Matrix.symplecticGroup (Fin 2) K) :=
  ⟨binaryMap (K := K) (binaryWitness j), by
    have hle : (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))).map
        (binaryMap (K := K)) ≤ commutator (Matrix.symplecticGroup (Fin 2) K) := by
      rw [map_commutator_eq, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact hle (Subgroup.mem_map.mpr ⟨_, binaryWitness_mem j, rfl⟩)⟩

private def witnessMatrix (R : Type*) [Zero R] [One R] (j : Fin 3) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  ![Matrix.fromBlocks !![1, 0; 0, 0] !![0, 0; 0, 1]
      !![0, 0; 0, 1] !![1, 0; 0, 1],
    Matrix.fromBlocks !![0, 0; 0, 1] !![1, 0; 0, 0]
      !![1, 0; 0, 0] !![1, 0; 0, 1],
    Matrix.fromBlocks !![1, 0; 1, 0] !![0, 0; 0, 1]
      !![1, 1; 0, 1] !![1, 1; 0, 1]] j

private lemma binaryWitness_matrix (j : Fin 3) :
    (binaryWitness j).val = witnessMatrix (ZMod 2) j := by
  have h : ∀ j, (binaryWitness j).val = witnessMatrix (ZMod 2) j := by decide
  exact h j

omit [Finite K] in
private lemma witness_matrix (j : Fin 3) :
    (witness (K := K) j).val.val = witnessMatrix K j := by
  change (binaryWitness j).val.map (ZMod.castHom (dvd_refl 2) K) = _
  rw [binaryWitness_matrix]
  ext i k
  rcases i with i | i <;> rcases k with k | k <;>
    fin_cases i <;> fin_cases k <;> fin_cases j <;>
    simp [witnessMatrix, Matrix.map_apply, Matrix.fromBlocks]

/-- The quadratic-defect class stays nonzero on the derived subgroup, even over `F₂`. -/
lemma derivedQuadraticCocycle_not_principal :
    ¬ ∃ v, principal (symplecticDerivedNatural (k := K) 2) v =
      derivedQuadraticCocycle := by
  rintro ⟨v, hv⟩
  have he (j : Fin 3) (i : Fin 2 ⊕ Fin 2) :=
    congrArg (fun f : cocycles (symplecticDerivedNatural (k := K) 2) =>
      f.val (witness j) i) hv
  have he' (j : Fin 3) (i : Fin 2 ⊕ Fin 2) :
      Matrix.mulVec (witnessMatrix K j) v i - v i =
      (frobeniusEquiv K 2).symm (rowQuadratic (witnessMatrix K j i)) := by
    have h := he j i
    change Matrix.mulVec (witness j).val.val v i - v i =
      (frobeniusEquiv K 2).symm (rowQuadratic ((witness j).val.val i)) at h
    simpa only [witness_matrix] using h
  have h0b := he' 0 b
  have h1c := he' 1 c
  have h2b := he' 2 b
  dsimp [witnessMatrix] at h0b h1c h2b
  norm_num [witnessMatrix, Matrix.mulVec, dotProduct, rowQuadratic,
    Fintype.sum_sum_type, Fin.sum_univ_two] at h0b h1c h2b
  exact one_ne_zero (by linear_combination h2b - h0b - h1c)

end Representation.OneCohomology.SymplecticFour
