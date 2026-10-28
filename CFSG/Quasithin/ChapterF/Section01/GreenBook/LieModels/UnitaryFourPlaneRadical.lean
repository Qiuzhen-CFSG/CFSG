module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical.TwoCore
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneBlock.Defs
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Finite Hermitian coordinates for the unitary-four plane kernel

The field identification between GF(2^(n*2)) and GF(2^(2*n)) is an actual ring
isomorphism and intertwines the specified Frobenius involutions. Entrywise
transport therefore identifies the additive Hermitian matrices and the SL₂
congruence action with the existing finite minus-type module. The exhaustive
unipotent parametrization identifies both matrix and projective restriction
kernels with this additive group, proving elementary abelianness and order
(2^n)^4 for every positive n, including n=1.

Source: Aschbacher--Smith F.1.12(I)(6), printed pp.263–264. The identification
with the actual two-core, the quotient, and the literal local conjugation action
remain separate obligations; the kernels here are defined by restriction.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Matrix
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneRadical
open Representation.OrthogonalFourMinus

/-- The two index conventions for the same quadratic extension are identified as fields. -/
def planeFieldEquiv (n : ℕ) : MatrixField n ≃+* FiniteModel.Field n :=
  let congr : ∀ a b : ℕ, a = b → (GaloisField 2 a ≃+* GaloisField 2 b) := by
    intro a b h
    subst b
    exact RingEquiv.refl _
  congr (n * 2) (2 * n) (Nat.mul_comm n 2)

/-- This field identification preserves the specified halfway Frobenius. -/
theorem planeFieldEquiv_conj (n : ℕ) (x : MatrixField n) :
    planeFieldEquiv n (fieldConj n x) = FiniteModel.conjugation n (planeFieldEquiv n x) := by
  change planeFieldEquiv n (x ^ (2 ^ n)) = (planeFieldEquiv n x) ^ (2 ^ n)
  exact map_pow _ _ _

theorem planeFieldEquiv_symm_conj (n : ℕ) (x : FiniteModel.Field n) :
    (planeFieldEquiv n).symm (FiniteModel.conjugation n x) = fieldConj n ((planeFieldEquiv n).symm x) := by
  apply (planeFieldEquiv n).injective
  simp [planeFieldEquiv_conj]

/-- Entrywise transport identifies the actual Hermitian additive groups. -/
def planeHermitianEquiv (n : ℕ) [NeZero n] :
    hermitianMatrices (MatrixField n) (fieldConj n) ≃+ FiniteModel.Space n where
  toFun X := ⟨X.val.map (planeFieldEquiv n), by
    ext i j
    change FiniteModel.conjugation n (planeFieldEquiv n (X.val j i)) = planeFieldEquiv n (X.val i j)
    rw [← planeFieldEquiv_conj]
    exact congrArg (planeFieldEquiv n) (congrFun (congrFun X.property i) j)⟩
  invFun X := ⟨X.val.map (planeFieldEquiv n).symm, by
    ext i j
    change fieldConj n ((planeFieldEquiv n).symm (X.val j i)) = (planeFieldEquiv n).symm (X.val i j)
    rw [← planeFieldEquiv_symm_conj]
    exact congrArg (planeFieldEquiv n).symm (congrFun (congrFun X.property i) j)⟩
  left_inv X := by apply Subtype.ext; ext i j; exact (planeFieldEquiv n).symm_apply_apply _
  right_inv X := by apply Subtype.ext; ext i j; exact (planeFieldEquiv n).apply_symm_apply _
  map_add' X Y := by apply Subtype.ext; ext i j; exact map_add (planeFieldEquiv n) _ _

/-- SL₂ is identified by the same entrywise field isomorphism. -/
def planeSL2Equiv (n : ℕ) :
    SpecialLinearGroup (Fin 2) (MatrixField n) ≃* SpecialLinearGroup (Fin 2) (FiniteModel.Field n) where
  toFun := SpecialLinearGroup.map (planeFieldEquiv n).toRingHom
  invFun := SpecialLinearGroup.map (planeFieldEquiv n).symm.toRingHom
  left_inv A := by apply Subtype.ext; ext i j; exact (planeFieldEquiv n).symm_apply_apply _
  right_inv A := by apply Subtype.ext; ext i j; exact (planeFieldEquiv n).apply_symm_apply _
  map_mul' := (SpecialLinearGroup.map (planeFieldEquiv n).toRingHom).map_mul

/-- Coefficient transport preserves the literal congruence action. -/
theorem planeHermitianEquiv_action_val (n : ℕ) [NeZero n]
    (A : SpecialLinearGroup (Fin 2) (MatrixField n))
    (X : hermitianMatrices (MatrixField n) (fieldConj n)) :
    (FiniteModel.action n (planeSL2Equiv n A) (planeHermitianEquiv n X)).val =
      (A.val * X.val * adjoint (fieldConj n) A.val).map (planeFieldEquiv n) := by
  rw [FiniteModel.action_apply]
  change A.val.map (planeFieldEquiv n) * X.val.map (planeFieldEquiv n) *
    adjoint (FiniteModel.conjugation n) (A.val.map (planeFieldEquiv n)) = _
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 1
  ext i j
  exact (planeFieldEquiv_conj n (A.val j i)).symm

variable (n : ℕ) (hn : 1 ≤ n)

/-- The actual kernel, before its identification with the two-core. -/
abbrev L2MatrixRadical : Subgroup (L2Matrix n hn) := (L2MatrixRestriction n hn).ker

/-- Its projective counterpart uses the transported restriction homomorphism. -/
abbrev L2Radical : Subgroup (L2 n hn) := (L2Restriction n hn).ker

/-- Matrix and projective restriction kernels are compatibly identified. -/
def L2RadicalProjectIso : L2MatrixRadical n hn ≃* L2Radical n hn where
  toFun g := ⟨L2ProjectIso n hn g.val, by
    change L2Restriction n hn (L2ProjectIso n hn g.val) = 1
    rw [L2Restriction_project]
    exact g.property⟩
  invFun g := ⟨(L2ProjectIso n hn).symm g.val, g.property⟩
  left_inv g := by apply Subtype.ext; exact (L2ProjectIso n hn).symm_apply_apply g.val
  right_inv g := by apply Subtype.ext; exact (L2ProjectIso n hn).apply_symm_apply g.val
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

@[simp] theorem L2RadicalProjectIso_apply (g : L2MatrixRadical n hn) :
    (L2RadicalProjectIso n hn g).val = L2ProjectIso n hn g.val := rfl

/-- The Hermitian group parametrizes the full matrix restriction kernel. -/
def L2MatrixRadicalEquiv [NeZero n] : Multiplicative (FiniteModel.Space n) ≃* L2MatrixRadical n hn :=
  (planeHermitianEquiv n).symm.toMultiplicative.trans
    (radicalEquiv (MatrixField n) (fieldConj n) (fieldConj_involutive n hn))

/-- The equivalence uses the literal unipotent matrix in the original matrix field. -/
@[simp] theorem L2MatrixRadicalEquiv_val [NeZero n] (X : Multiplicative (FiniteModel.Space n)) :
    (L2MatrixRadicalEquiv n hn X).val.val.val.val =
      unipotentMatrix (MatrixField n) (X.toAdd.val.map (planeFieldEquiv n).symm) := rfl

/-- Compatible parametrization of the kernel in the actual projective group. -/
def L2RadicalEquiv [NeZero n] : Multiplicative (FiniteModel.Space n) ≃* L2Radical n hn :=
  (L2MatrixRadicalEquiv n hn).trans (L2RadicalProjectIso n hn)

@[simp] theorem L2RadicalEquiv_project [NeZero n] (X : Multiplicative (FiniteModel.Space n)) :
    (L2RadicalEquiv n hn X).val = L2ProjectIso n hn (L2MatrixRadicalEquiv n hn X).val := rfl

/-- Exact order of the matrix kernel, including `n = 1`. -/
theorem L2MatrixRadical_card : Nat.card (L2MatrixRadical n hn) = (2 ^ n) ^ 4 := by
  let : NeZero n := ⟨by omega⟩
  rw [← Nat.card_congr (L2MatrixRadicalEquiv n hn).toEquiv]
  change Nat.card (FiniteModel.Space n) = _
  rw [Module.natCard_eq_pow_finrank (K := FiniteModel.fixedField n), FiniteModel.finrank_space, FiniteModel.card_fixedField]

theorem L2Radical_card : Nat.card (L2Radical n hn) = (2 ^ n) ^ 4 := by
  rw [← Nat.card_congr (L2RadicalProjectIso n hn).toEquiv, L2MatrixRadical_card]

instance L2MatrixRadical_elementaryAbelian : IsElementaryAbelian 2 (L2MatrixRadical n hn) :=
  radical_elementaryAbelian (MatrixField n) (fieldConj n) (fieldConj_involutive n hn)

instance L2Radical_elementaryAbelian : IsElementaryAbelian 2 (L2Radical n hn) where
  is_comm.comm g h := by
    obtain ⟨g,rfl⟩ := (L2RadicalProjectIso n hn).surjective g
    obtain ⟨h,rfl⟩ := (L2RadicalProjectIso n hn).surjective h
    rw [← map_mul, ← map_mul]
    exact congrArg (L2RadicalProjectIso n hn)
      (radical_mul_comm (MatrixField n) (fieldConj n) (fieldConj_involutive n hn) g h)
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro g
    obtain ⟨g,rfl⟩ := (L2RadicalProjectIso n hn).surjective g
    rw [← map_pow]
    exact (congrArg (L2RadicalProjectIso n hn)
      (radical_sq (MatrixField n) (fieldConj n) (fieldConj_involutive n hn) g)).trans
        (map_one _))

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
