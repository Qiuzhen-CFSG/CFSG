module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups.SubfieldReduction
public import GorensteinWalter.PGL2DeterminantSquare

/-!
# Prime-subfield normalizers in square-field PGL₂

For an odd field of square order, the normalizer of the literal coefficient-field
PGL₂ image lies in the canonical PSL₂ image. Conjugate the upper unipotent U by a
matrix A representing a normalizer element. The resulting matrix C is projectively
defined over the subfield; its trace 2 makes the projective scalar belong to the
subfield as well. The equation CA = AU gives
`C₀₁ det A = A₀₀²` and `-C₁₀ det A = A₁₀²`. One entry in the first column of A
is nonzero, and every subfield element is a square upstairs, so det A is a square.

Applying the marked-subfield adapter excludes Dickson's PGL₂(p) inner intersection
for any subgroup containing an ambient Sylow two-subgroup. In particular the
argument includes p = 3 and p = 5, and does not require maximality.

Source: Huppert II.8.27; the auxiliary square-field calculation for
Aschbacher--Smith A.2.3(2), E.1.14(6), printed pp.33 and 214, the latter citing
Aschbacher (1982), Lemma 4.10.
-/

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups

open Matrix GorensteinWalter
open PrimeGeometry.Diagonal.MaximalOvergroups
open scoped MatrixGroups

private theorem subfield_element_isSquare {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hpodd : Odd p) (hFcard : Nat.card F = p ^ 2)
    (K : Subfield F) (hKcard : Nat.card K = p) (x : K) : IsSquare (x : F) := by
  classical
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K
  have hchar : ringChar F ≠ 2 := by
    intro h
    have he := FiniteField.even_card_of_char_two h
    rw [← Nat.card_eq_fintype_card, hFcard] at he
    have ho := Nat.odd_iff.mp (hpodd.pow (n := 2))
    omega
  by_cases hx : x = 0
  · simp [hx]
  have hxn : (x : F) ≠ 0 := by exact_mod_cast hx
  apply (FiniteField.isSquare_iff hchar hxn).mpr
  have hxpow : (x : F) ^ (p - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one x hx
    rw [← Nat.card_eq_fintype_card, hKcard] at h
    exact_mod_cast h
  rw [← Nat.card_eq_fintype_card, hFcard]
  obtain ⟨k, hk⟩ := hpodd
  have he : p ^ 2 / 2 = (p - 1) * (k + 1) := by
    have heq : p ^ 2 = 2 * ((p - 1) * (k + 1)) + 1 := by
      rw [hk]
      simp only [Nat.add_sub_cancel]
      ring
    omega
  rw [he, pow_mul, hxpow, one_pow]

private def upper (F : Type*) [Field F] : SL(2, F) :=
  ⟨!![1, 1; 0, 1], by simp⟩

private theorem det_square_of_upper_conj
    {F : Type*} [Field F] (K : Subfield F)
    (hKsq : ∀ x : K, IsSquare (x : F)) (h2 : (2 : F) ≠ 0)
    (A : GL (Fin 2) F)
    (hA : Matrix.ProjGenLinGroup.mk A ∈ Subgroup.normalizer
      ((Glauberman.Dickson.h826_pglMap K.subtype).range : Set (PGL2 F))) :
    IsSquare (A.det : F) := by
  let U : GL (Fin 2) F := Matrix.GeneralLinearGroup.map K.subtype
    (Matrix.SpecialLinearGroup.toGL (upper K))
  have hU : Matrix.ProjGenLinGroup.mk U ∈
      (Glauberman.Dickson.h826_pglMap K.subtype).range := by
    exact ⟨Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (upper K)),
      Glauberman.Dickson.h826_pglMap_mk _ _⟩
  have hconj := (Subgroup.mem_normalizer_iff.mp hA)
    (Matrix.ProjGenLinGroup.mk U)
  have hm : Matrix.ProjGenLinGroup.mk (A * U * A⁻¹) ∈
      (Glauberman.Dickson.h826_pglMap K.subtype).range := by
    simpa only [map_mul, map_inv] using hconj.mp hU
  obtain ⟨b, hb⟩ := hm
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective b
  rw [Glauberman.Dickson.h826_pglMap_mk] at hb
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hb
  have ht : (2 : F) = ((B 0 0 : F) + (B 1 1 : F)) * (u : F) := by
    have h := congrArg
      (fun X : GL (Fin 2) F => Matrix.trace (X : Matrix (Fin 2) (Fin 2) F)) hu
    simp only [Matrix.GeneralLinearGroup.coe_mul] at h
    rw [Matrix.trace_units_conj] at h
    simpa [U, upper, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.SpecialLinearGroup.toGL, add_mul, one_add_one_eq_two] using h.symm
  have htn : ((B 0 0 : F) + (B 1 1 : F)) ≠ 0 := by
    intro h
    rw [h, zero_mul] at ht
    exact h2 ht
  have huK : (u : F) ∈ K := by
    have he : (u : F) = 2 / ((B 0 0 : F) + (B 1 1 : F)) := by
      apply (eq_div_iff htn).mpr
      simpa only [mul_comm] using ht.symm
    rw [he]
    exact K.div_mem (by simp) (K.add_mem (B 0 0).property (B 1 1).property)
  let C := Matrix.GeneralLinearGroup.map K.subtype B *
    Matrix.GeneralLinearGroup.scalar (Fin 2) u
  have hCA : C * A = A * U := by
    dsimp [C]
    rw [hu]
    group
  have hC (i j : Fin 2) : C i j ∈ K := by
    have he : C i j = (B i j : F) * (u : F) := by
      simp [C, Matrix.mul_apply, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar, Matrix.diagonal_apply]
    rw [he]
    exact K.mul_mem (B i j).property huK
  have h00 := congrArg (fun X : GL (Fin 2) F => X 0 0) hCA
  have h01 := congrArg (fun X : GL (Fin 2) F => X 0 1) hCA
  have h10 := congrArg (fun X : GL (Fin 2) F => X 1 0) hCA
  have h11 := congrArg (fun X : GL (Fin 2) F => X 1 1) hCA
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  simp [U, upper, Matrix.SpecialLinearGroup.toGL] at h00 h01 h10 h11
  have he01 : C 0 1 * (A.det : F) = (A 0 0) ^ 2 := by
    change C 0 1 * Matrix.det (A : Matrix (Fin 2) (Fin 2) F) = _
    rw [Matrix.det_fin_two]
    linear_combination A 0 0 * h01 - A 0 1 * h00
  have he10 : -(C 1 0) * (A.det : F) = (A 1 0) ^ 2 := by
    change -(C 1 0) * Matrix.det (A : Matrix (Fin 2) (Fin 2) F) = _
    rw [Matrix.det_fin_two]
    linear_combination A 1 0 * h11 - A 1 1 * h10
  by_cases ha : A 0 0 = 0
  · have hc : A 1 0 ≠ 0 := by
      intro hc
      apply A.det_ne_zero
      simp [Matrix.det_fin_two, ha, hc]
    have hcn : -(C 1 0) ≠ 0 := by
      intro h
      rw [h, zero_mul] at he10
      exact hc (sq_eq_zero_iff.mp he10.symm)
    have he : (A.det : F) = (A 1 0) ^ 2 / -(C 1 0) := by
      apply (eq_div_iff hcn).mpr
      simpa only [mul_comm] using he10
    rw [he]
    exact (IsSquare.sq _).div (hKsq ⟨-(C 1 0), K.neg_mem (hC 1 0)⟩)
  · have hcn : C 0 1 ≠ 0 := by
      intro h
      rw [h, zero_mul] at he01
      exact ha (sq_eq_zero_iff.mp he01.symm)
    have he : (A.det : F) = (A 0 0) ^ 2 / C 0 1 := by
      apply (eq_div_iff hcn).mpr
      simpa only [mul_comm] using he01
    rw [he]
    exact (IsSquare.sq _).div (hKsq ⟨C 0 1, hC 0 1⟩)

/-- The normalizer of the literal subfield PGL₂ image is inner in odd square
field degree. This also applies to the prime subfields of orders 3 and 5. -/
public theorem prime_subfield_normalizer_le_inner
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hpodd : Odd p) (hFcard : Nat.card F = p ^ 2)
    (K : Subfield F) (hKcard : Nat.card K = p) :
    Subgroup.normalizer
      ((Glauberman.Dickson.h826_pglMap K.subtype).range : Set (PGL2 F)) ≤
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  classical
  let := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    have he := FiniteField.even_card_of_char_two h
    rw [← Nat.card_eq_fintype_card, hFcard] at he
    have ho := Nat.odd_iff.mp (hpodd.pow (n := 2))
    omega
  intro g hg
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  apply (pgl2_mk_mem_psl2_range_iff_det_isSquare A).mpr
  exact det_square_of_upper_conj K
    (subfield_element_isSquare hpodd hFcard K hKcard) (Ring.two_ne_zero hchar) A hg

variable {F : Type*} [Field F] [Finite F]

local instance finitePGL : Finite (PGL2 F) := Finite.of_surjective
  Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- Dickson's marked PGL₂(p) inner intersection is impossible in an odd
prime-square field for a subgroup containing an ambient Sylow two-subgroup.
The equivalence and conjugacy witness are the actual Dickson data. -/
public theorem no_subfield_case {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hFcard : Nat.card F = p ^ 2)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hTM : (T : Subgroup _) ≤ M)
    (e : inner M ≃* PGL2 (GaloisField p 1))
    (w : Glauberman.Dickson.SubfieldConjugacyWitness p 1 (inner M)) : False := by
  apply no_subfield_case_of_normalizer_le_inner hpodd hFcard T M hTM ?_ e w
  intro K hKcard
  exact prime_subfield_normalizer_le_inner hpodd hFcard K hKcard

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups
