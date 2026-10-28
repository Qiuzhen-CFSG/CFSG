module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.Quaternion
public import Theory.SpecificGroups.SL2.BinaryTetrahedralQuotient
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The binary tetrahedral group on the unitary plane over Nine

The existing Q₈ representation and an explicitly chosen cubic matrix realize
its exact `q8C3Action` as conjugation. The resulting semidirect-product map
is faithful and exhausts SU₂(3): a unitary matrix is determined by its first
column and determinant, and all 24 unit first columns occur. Only these small
finite calculations are checked by kernel reduction.

The scalar elements are precisely the two central signs. Conjugation by any
GU₂(3) element preserves the image because it preserves determinant one.
The consumer in `BinaryModel.Pair` uses two such coordinate planes and the
literal SU₄-to-PSU₄ projection.

The quaternion representation and first-column argument adapt the existing
`RepresentativeCore/Quaternion` and `RepresentativeBound/UnitaryTwo` modules.
Sources: GLS3, chapter 2, §2.7 (unitary conventions) and chapter 6, §6.1;
this supplies local model data for Aschbacher–Smith I.1.4(5), printed p.408
of `refs/quasithin.pdf`, without assuming its multiplier conclusion.
-/

open Matrix
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
open GLS3.Chapter5.SchurPresentation
@[expose] public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.BinaryModel
abbrev F := FiniteField.Nine
abbrev U₂ := Matrix.unitaryGroup (Fin 2) F
abbrev SU₂ := Matrix.specialUnitaryGroup (Fin 2) F
abbrev B := BinaryTetrahedral
private instance binaryFintype : Fintype B :=
  Fintype.ofEquiv (QuaternionGroup 2 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm

def quaternionUnitary : QuaternionGroup 2 →* U₂ :=
  quaternionMatrixHom.codRestrict _ (fun q =>
    Matrix.mem_unitaryGroup_iff'.mpr (quaternionMatrix_unitary q))

def binaryCubic : Mat₂ := !![⟨1,2⟩, ⟨1,1⟩; ⟨2,1⟩, ⟨1,1⟩]
def binaryCubicUnitary : U₂ := ⟨binaryCubic, by
  rw [Matrix.mem_unitaryGroup_iff']; decide⟩
def cubicUnitaryHom : Multiplicative (ZMod 3) →* U₂ where
  toFun k := binaryCubicUnitary ^ (Multiplicative.toAdd k).val
  map_one' := by decide
  map_mul' := by
    intro x y
    change ZMod 3 at x y
    fin_cases x <;> fin_cases y <;> apply Subtype.ext <;> decide +kernel

private theorem action_compat (k : Multiplicative (ZMod 3)) (q : QuaternionGroup 2) :
    quaternionUnitary (q8C3Action k q) =
      cubicUnitaryHom k * quaternionUnitary q * (cubicUnitaryHom k)⁻¹ := by
  change ZMod 3 at k
  fin_cases k <;> rcases q with i | i <;> fin_cases i <;> apply Subtype.ext <;> decide +kernel

/-- The binary tetrahedral group on the identity Hermitian plane. -/
def binaryUnitary : B →* U₂ :=
  SemidirectProduct.lift quaternionUnitary cubicUnitaryHom (by
    intro k; apply MonoidHom.ext; intro q; exact action_compat k q)

def binaryMatrix : B →* Mat₂ := (Matrix.unitaryGroup (Fin 2) F).subtype.comp binaryUnitary

theorem binaryMatrix_unitary (b : B) : (binaryMatrix b).conjTranspose * binaryMatrix b = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (binaryUnitary b).property

theorem binaryMatrix_det (b : B) : (binaryMatrix b).det = 1 := by
  exact (by decide +kernel : ∀ b : B, (binaryMatrix b).det = 1) b

def binarySpecial : B →* SU₂ := binaryMatrix.codRestrict _ (fun b =>
  ⟨(binaryUnitary b).property, binaryMatrix_det b⟩)

theorem binaryMatrix_injective : Function.Injective binaryMatrix := by
  exact (by decide +kernel : ∀ x y : B, binaryMatrix x = binaryMatrix y → x = y)

abbrev UnitColumn := {v : F × F // star v.1 * v.1 + star v.2 * v.2 = 1}

/-- A unitary two-by-two matrix is determined by its first column and determinant. -/
theorem unitary_ext_of_column_det (A D : U₂)
    (hc : A.val 0 0 = D.val 0 0 ∧ A.val 1 0 = D.val 1 0)
    (hd : A.val.det = D.val.det) : A = D := by
  have second (A : U₂) :
      A.val 0 1 = -A.val.det * star (A.val 1 0) ∧
      A.val 1 1 = A.val.det * star (A.val 0 0) := by
    have hn : star (A.val 0 0) * A.val 0 0 + star (A.val 1 0) * A.val 1 0 = 1 := by
      have h := congrArg (fun M : Mat₂ => M 0 0)
        (Matrix.mem_unitaryGroup_iff'.mp A.property)
      simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] using h
    have ho : star (A.val 0 0) * A.val 0 1 + star (A.val 1 0) * A.val 1 1 = 0 := by
      have h := congrArg (fun M : Mat₂ => M 0 1)
        (Matrix.mem_unitaryGroup_iff'.mp A.property)
      simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] using h
    constructor
    · symm
      rw [Matrix.det_fin_two]
      linear_combination (A.val 0 1) * hn - (A.val 0 0) * ho
    · symm
      rw [Matrix.det_fin_two]
      linear_combination (A.val 1 1) * hn - (A.val 1 0) * ho
  apply Subtype.ext
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j
  · exact hc.1
  · change A.val 0 1 = D.val 0 1
    rw [(second A).1, (second D).1, hd, hc.2]
  · exact hc.2
  · change A.val 1 1 = D.val 1 1
    rw [(second A).2, (second D).2, hd, hc.1]

private theorem column_covered : ∀ v : UnitColumn, ∃ b : B,
    (binaryMatrix b 0 0, binaryMatrix b 1 0) = v.val := by decide +kernel

theorem binarySpecial_surjective : Function.Surjective binarySpecial := by
  intro A
  let u : U₂ := ⟨A.val, A.property.1⟩
  have hn : star (A.val 0 0) * A.val 0 0 + star (A.val 1 0) * A.val 1 0 = 1 := by
    have h := congrArg (fun M : Mat₂ => M 0 0)
      (Matrix.mem_unitaryGroup_iff'.mp A.property.1)
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] using h
  obtain ⟨b,hb⟩ := column_covered ⟨(A.val 0 0, A.val 1 0), hn⟩
  refine ⟨b, Subtype.ext ?_⟩
  exact congrArg (fun X : U₂ => X.val) (unitary_ext_of_column_det (binaryUnitary b) u
    ⟨congrArg Prod.fst hb, congrArg Prod.snd hb⟩
    ((binaryMatrix_det b).trans A.property.2.symm))

/-- This is an actual isomorphism with SU₂(3), including its central sign. -/
noncomputable def binaryEquivSpecial : B ≃* SU₂ :=
  MulEquiv.ofBijective binarySpecial ⟨fun _ _ h =>
    binaryMatrix_injective (congrArg (fun X : SU₂ => X.val) h), binarySpecial_surjective⟩

theorem specialTwo_card : Nat.card SU₂ = 24 := by
  rw [← Nat.card_congr binaryEquivSpecial.toEquiv]
  exact binaryTetrahedral_card

abbrev binarySign : B := SemidirectProduct.inl (QuaternionGroup.a 2)

theorem binaryMatrix_scalar (b : B) (u : F)
    (h : binaryMatrix b = Matrix.scalar (Fin 2) u) :
    (b = 1 ∧ u = 1) ∨ (b = binarySign ∧ u = -1) := by
  exact (by decide +kernel : ∀ (b : B) (u : F),
    binaryMatrix b = Matrix.scalar (Fin 2) u →
      (b = 1 ∧ u = 1) ∨ (b = binarySign ∧ u = -1)) b u h

/-- Conjugating a determinant-one block by an arbitrary unitary block stays in the model. -/
theorem unitary_normalizes_binary (A : U₂) (b : B) :
    ∃ c : B, A.val * binaryMatrix b = binaryMatrix c * A.val := by
  let D : U₂ := A * binaryUnitary b * A⁻¹
  have hd : D.val.det = 1 := by
    change ((A.val * binaryMatrix b) * (A⁻¹).val).det = 1
    rw [Matrix.det_mul, Matrix.det_mul, binaryMatrix_det, mul_one, ← Matrix.det_mul]
    have he : A.val * (A⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel A)
    rw [he, Matrix.det_one]
  obtain ⟨c,hc⟩ := binarySpecial_surjective ⟨D.val, D.property, hd⟩
  refine ⟨c, ?_⟩
  have he : binaryUnitary c = D := Subtype.ext (congrArg (fun X : SU₂ => X.val) hc)
  have h := congrArg (fun X : U₂ => (X * A).val) he
  change (A * binaryUnitary b).val = (binaryUnitary c * A).val
  simpa only [D, inv_mul_cancel_right] using h.symm
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary.BinaryModel
