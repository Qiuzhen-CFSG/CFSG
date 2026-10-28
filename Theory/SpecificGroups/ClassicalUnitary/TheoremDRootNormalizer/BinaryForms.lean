module

public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Theory.FieldTheory.QuadraticFrobeniusFixed
public import BenderSuzuki.MatrixGroups.SpecialUnitaryFixedEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
import Mathlib.Tactic

/-!
# Binary Hermitian form transport and the PSU₂ comparison

The specified Frobenius on a field of order (2^n)² has fixed field of order
2^n. The Hermitian orthonormal-basis theorem therefore transports every form
admitted by the classical unitary model to identity Gram, retaining its stored
involution. No choice of a standard marking is assumed.

In dimension two, a trace-one element t gives the basis matrix
[[1,t],[1,t+1]]. Its Gram matrix is the alternating matrix in characteristic
two. The existing determinant calculation identifies SU with SL₂ of the
actual fixed field. Both scalar projective kernels are trivial, so this
is an actual PSU₂–PSL₂ equivalence at the original field parameter.

Source: Huppert II.10.4 for Hermitian bases; the classical rank-one comparison
used in Aschbacher–Smith A.2.18 (printed p.40) and Theorem D/14.8.2(1)
(printed pp.1078–1079). The consumer is LieTypeBranch.UnitaryRank.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram
namespace Theory.SpecificGroups.UnitaryRootNormalizer
variable {F : Type*} [Field F]

/-- The actual fixed subfield has the unitary parameter as its cardinality. -/
theorem fixed_card_binary [Finite F] {d n : ℕ} (J : HermitianForm d F) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    Nat.card {x : F // J.conj x = x} = 2 ^ n := by
  classical
  let K := GaloisField 2 (2 * n)
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul]
    congr 1
    omega
  let e : F ≃+* K := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcard.trans hK.symm)
  let σ := iterateFrobeniusEquiv K 2 n
  have he (x : F) : J.conj x = x ↔ σ (e x) = e x := by
    rw [hconj, iterateFrobeniusEquiv_def, ← map_pow]
    exact e.injective.eq_iff.symm
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv he)).trans
    (GaloisField.card_fixedBy_quadraticFrobenius 2 n (by omega))

/-- The coefficient field of every positive binary unitary parameter has characteristic two. -/
theorem charP_binary [Finite F] {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  apply ringChar.of_eq
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, hcard]
  have he : Even (2 ^ n) := even_two.pow_of_ne_zero (by omega)
  exact Nat.mod_eq_zero_of_dvd
    (even_iff_two_dvd.mp (he.pow_of_ne_zero (by decide : (2 : ℕ) ≠ 0)))

/-- Actual matrix basis change for every admitted binary Hermitian form. -/
theorem exists_binary_identity_basis [Finite F] {d n : ℕ} (J : HermitianForm d F)
    (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    ∃ C : GL (Fin d) F, J.conjTranspose C.val * J.form * C.val = 1 :=
  BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis d J (2 ^ n)
    hcard (fixed_card_binary J hn hcard hconj)

/-- Trace-one coordinates give a hyperbolic basis in characteristic two. -/
theorem exists_binary_skew_basis [CharP F 2] (J : HermitianForm 2 F)
    (hJ : J.form = 1) (t : F) (ht : t + J.conj t = 1) :
    ∃ C : GL (Fin 2) F,
      J.conjTranspose C.val * J.form * C.val = (1 : F) • !![0, 1; -1, 0] := by
  let M : Matrix (Fin 2) (Fin 2) F := !![1, t; 1, t + 1]
  have hdet : M.det ≠ 0 := by simp [M, det_fin_two]
  refine ⟨GeneralLinearGroup.mkOfDetNeZero M hdet, ?_⟩
  change J.conjTranspose M * J.form * M = _
  rw [hJ, mul_one, one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_two,
      CharTwo.neg_eq, ← add_assoc, CharTwo.add_self_eq_zero]
  calc
    J.conj t * t + (J.conj t + 1) * (t + 1) =
        (J.conj t * t + J.conj t * t) + (t + J.conj t) + 1 := by ring
    _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_add, ht, CharTwo.add_self_eq_zero]

/-- The actual projection in dimension two. -/
def projectTwo (J : HermitianForm 2 F) :
    J.specialSubgroup →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (ProjGenLinGroup.mk.comp J.specialSubgroup.subtype).codRestrict _
    (fun a => ⟨a.val, a.property, rfl⟩)

theorem projectTwo_surjective (J : HermitianForm 2 F) :
    Function.Surjective (projectTwo J) := by
  rintro ⟨x, A, hA, rfl⟩
  exact ⟨⟨A, hA⟩, rfl⟩

/-- In characteristic two a scalar determinant-one two-matrix is the identity. -/
theorem projectTwo_injective [CharP F 2] (J : HermitianForm 2 F) :
    Function.Injective (projectTwo J) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h : ProjGenLinGroup.mk A.val = 1 := congrArg Subtype.val hA
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  have hd := (J.mem_specialSubgroup_iff A.val).mp A.property |>.2
  rw [← hu, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hd
  have hsq : (u : F) ^ 2 = 1 := congrArg Units.val hd
  have hu1 : (u : F) = 1 := by
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  have huu : u = 1 := Units.ext hu1
  apply Subtype.ext
  rw [← hu, huu, map_one]
  rfl

/-- Every actual PSU2 in characteristic two is PSL2 over its fixed field. -/
theorem nonempty_projectiveTwoEquiv [Finite F] [CharP F 2]
    (J : HermitianForm 2 F) {q : ℕ}
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃*
      ProjectiveSpecialLinearGroup (Fin 2) (FixedBy.subfield F J.conj)) := by
  obtain ⟨C, hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    2 J q hcard hfixed
  let I := identityGram J
  obtain ⟨t, ht⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective
    I q hcard hfixed 1 (by simp)
  obtain ⟨D, hD⟩ := exists_binary_skew_basis I rfl t ht
  let e := I.specialUnitaryEquivFixed D 1 one_ne_zero hD
  let ep := MulEquiv.ofBijective (projectTwo I)
    ⟨projectTwo_injective I, projectTwo_surjective I⟩
  exact ⟨((projectiveEquiv J C hC).trans ep.symm).trans
    (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL)⟩

end Theory.SpecificGroups.UnitaryRootNormalizer
