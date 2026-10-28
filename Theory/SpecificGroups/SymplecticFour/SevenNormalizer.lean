module

public import Theory.SpecificGroups.SymplecticFour.Flag
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Seven-element normalizers in symplectic four-space

Over an algebraic closure, an element of order seven has a nonidentity
seventh root as an eigenvalue. Squaring conjugacy would close its spectrum
under squaring; symplectic duality closes it under inversion. Together these
operations give all six nonidentity seventh roots, impossible in dimension
four. If every eigenvalue were one, Cayley–Hamilton and characteristic two
would give fourth power one, contradicting order seven.

The coefficient embedding into the algebraic closure is injective and
preserves the actual symplectic form. Thus the result holds over every field
of characteristic two, with no finiteness or automorphism-classification input.

This spectral argument supplies the symplectic case of the inspection in
Aschbacher–Smith, *The Classification of Quasithin Groups*, E.6.18, printed
p.252; the relevant family is Theorem C and Remark A.2.4, printed p.33.
-/

open Matrix Polynomial
namespace Theory.SpecificGroups.SymplecticFour.SevenNormalizer
variable {K : Type*} [Field K] [CharP K 2] [IsAlgClosed K]
local notation "I" => Fin 2 ⊕ Fin 2
local notation "M" => Matrix I I K

private theorem exists_nontrivial_spectrum (A : M) (h7 : A ^ 7 = 1) (hne : A ≠ 1) :
    ∃ r : K, r ∈ spectrum K A ∧ r ≠ 1 := by
  let : CharP M 2 := ⟨fun k => by
    simp only [← Matrix.diagonal_natCast, ← Matrix.diagonal_zero,
      Matrix.diagonal_eq_diagonal_iff, CharP.cast_eq_zero_iff K 2 k, forall_const]⟩
  by_contra! h
  have hrs : A.charpoly.roots = Multiset.replicate 4 1 := by
    have hcard : A.charpoly.roots.card = 4 := by
      rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
        charpoly_natDegree_eq_dim]
      simp
    rw [← hcard]
    apply Multiset.eq_replicate_card.mpr
    intro r hr
    exact h r (mem_spectrum_iff_isRoot_charpoly.mpr
      ((Polynomial.mem_roots A.charpoly_monic.ne_zero).mp hr))
  have hpoly : A.charpoly = (X - 1) ^ 4 := by
    rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic, hrs]
    simp only [Multiset.map_replicate, Multiset.prod_replicate, C_1]
  have h4 : A ^ 4 = 1 := by
    have he := A.aeval_self_charpoly
    rw [hpoly] at he
    simp only [map_pow, map_sub, aeval_X, map_one] at he
    have hh := sub_pow_char_pow_of_commute 2 2 (Commute.one_right A)
    norm_num at hh
    rw [hh] at he
    exact sub_eq_zero.mp he
  apply hne
  calc
    A = A ^ 8 * (A ^ 7)⁻¹ := by rw [pow_succ, h7]; simp
    _ = 1 := by rw [show (8 : ℕ) = 4 * 2 by decide, pow_mul, h4, h7]; simp

end Theory.SpecificGroups.SymplecticFour.SevenNormalizer

namespace Theory.SpecificGroups.SymplecticFour.SevenNormalizer
open Theory.SpecificGroups.SymplecticFour
variable {K : Type*} [Field K] [CharP K 2] [IsAlgClosed K]
local notation "I" => Fin 2 ⊕ Fin 2
local notation "M" => Matrix I I K

omit [CharP K 2] [IsAlgClosed K] in
private theorem inv_charpoly (a : Sp K) : (a⁻¹).val.charpoly = a.val.charpoly := by
  rw [SymplecticGroup.coe_inv, charpoly_mul_comm, ← Matrix.mul_assoc]
  simp [Matrix.J_squared]

omit [CharP K 2] [IsAlgClosed K] in
private theorem square_charpoly (a b : Sp K) (h : b * a * b⁻¹ = a ^ 2) :
    (a.val ^ 2).charpoly = a.val.charpoly := by
  have hm := congrArg (fun g : Sp K => g.val.charpoly) h
  change (b.val * a.val * (b⁻¹).val).charpoly = (a.val ^ 2).charpoly at hm
  rw [charpoly_mul_comm, ← Matrix.mul_assoc] at hm
  have hb : (b⁻¹).val * b.val = 1 := congrArg Subtype.val (inv_mul_cancel b)
  rw [hb, one_mul] at hm
  exact hm.symm

omit [CharP K 2] [IsAlgClosed K] in
private theorem spectrum_square (A : M) (hsq : (A ^ 2).charpoly = A.charpoly)
    (r : K) (hr : r ∈ spectrum K A) : r ^ 2 ∈ spectrum K A := by
  have he := mem_spectrum_iff_isRoot_charpoly.mp (spectrum.pow_mem_pow A 2 hr)
  rw [hsq] at he
  exact mem_spectrum_iff_isRoot_charpoly.mpr he

omit [CharP K 2] [IsAlgClosed K] in
private theorem spectrum_inv (a : Sp K) (hi : (a⁻¹).val.charpoly = a.val.charpoly)
    (r : K) (hr : r ∈ spectrum K a.val) : r⁻¹ ∈ spectrum K a.val := by
  let u : Mˣ :=
    { val := a.val
      inv := (a⁻¹).val
      val_inv := congrArg Subtype.val (mul_inv_cancel a)
      inv_val := congrArg Subtype.val (inv_mul_cancel a) }
  have he := mem_spectrum_iff_isRoot_charpoly.mp
    (spectrum.inv₀_mem_inv (a := u) hr)
  change (a⁻¹).val.charpoly.IsRoot r⁻¹ at he
  rw [hi] at he
  exact mem_spectrum_iff_isRoot_charpoly.mpr he
end Theory.SpecificGroups.SymplecticFour.SevenNormalizer

namespace Theory.SpecificGroups.SymplecticFour.SevenNormalizer
open Theory.SpecificGroups.SymplecticFour
variable {K : Type*} [Field K] [CharP K 2] [IsAlgClosed K]
local notation "I" => Fin 2 ⊕ Fin 2
local notation "M" => Matrix I I K

private theorem six_eigenvalues (A : M) (h7 : A ^ 7 = 1) (hne : A ≠ 1)
    (hsq : ∀ r ∈ spectrum K A, r ^ 2 ∈ spectrum K A)
    (hinv : ∀ r ∈ spectrum K A, r⁻¹ ∈ spectrum K A) : False := by
  classical
  obtain ⟨r, hr, hrne⟩ := exists_nontrivial_spectrum A h7 hne
  have hr7 : r ^ 7 = 1 := by
    have he := spectrum.pow_mem_pow A 7 hr
    rwa [h7, spectrum.one_eq, Set.mem_singleton_iff] at he
  have hord : orderOf r = 7 := @orderOf_eq_prime K _ r 7 ⟨by decide⟩ hr7 hrne
  have h2 := hsq r hr
  have h4 : r ^ 4 ∈ spectrum K A := by simpa only [← pow_mul] using hsq (r ^ 2) h2
  have h6 : r ^ 6 ∈ spectrum K A := by
    have he : r⁻¹ = r ^ 6 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hr7])
    simpa only [he] using hinv r hr
  have h5 : r ^ 5 ∈ spectrum K A := by
    have he : (r ^ 2)⁻¹ = r ^ 5 := inv_eq_of_mul_eq_one_right (by rw [← pow_add, hr7])
    simpa only [he] using hinv _ h2
  have h3 : r ^ 3 ∈ spectrum K A := by
    have he : (r ^ 4)⁻¹ = r ^ 3 := inv_eq_of_mul_eq_one_right (by rw [← pow_add, hr7])
    simpa only [he] using hinv _ h4
  have hmem : ∀ k ∈ Finset.Icc 1 6, r ^ k ∈ A.charpoly.roots.toFinset := by
    intro k hk
    rw [Multiset.mem_toFinset, Polynomial.mem_roots A.charpoly_monic.ne_zero,
      ← mem_spectrum_iff_isRoot_charpoly]
    obtain ⟨hk1, hk6⟩ := Finset.mem_Icc.mp hk
    interval_cases k
    · simpa using hr
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
  have hi : Set.InjOn (fun k : ℕ => r ^ k) (Finset.Icc 1 6 : Finset ℕ) := by
    intro i hi j hj he
    apply pow_injOn_Iio_orderOf (x := r) _ _ he
    · rw [Set.mem_Iio, hord]
      have := Finset.mem_Icc.mp hi
      omega
    · rw [Set.mem_Iio, hord]
      have := Finset.mem_Icc.mp hj
      omega
  have hb := (Finset.card_le_card_of_injOn _ hmem hi).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' A.charpoly))
  rw [charpoly_natDegree_eq_dim] at hb
  norm_num at hb

private theorem no_square_conjugate_closed (a b : Sp K) (h7 : a ^ 7 = 1) (hne : a ≠ 1)
    (h : b * a * b⁻¹ = a ^ 2) : False := by
  apply six_eigenvalues a.val
  · exact congrArg Subtype.val h7
  · exact fun he => hne (Subtype.ext he)
  · exact spectrum_square _ (square_charpoly a b h)
  · exact spectrum_inv a (inv_charpoly a)
end Theory.SpecificGroups.SymplecticFour.SevenNormalizer

namespace Theory.SpecificGroups.SymplecticFour.SevenNormalizer
open Theory.SpecificGroups.SymplecticFour
variable {K : Type*} [Field K] [CharP K 2]
/-- A nonidentity seven-element in the actual symplectic four-space group is
never conjugate to its square in characteristic two. -/
public theorem seven_not_conjugate_square (a b : Sp K) (h7 : a ^ 7 = 1) (hne : a ≠ 1) :
    b * a * b⁻¹ ≠ a ^ 2 := by
  intro h
  let R := AlgebraicClosure K
  let f : Sp K →* Sp R :=
    { toFun g := ⟨g.val.map (algebraMap K R), SymplecticGroup.map_mem g.property _⟩
      map_one' := by apply Subtype.ext; exact (algebraMap K R).mapMatrix.map_one
      map_mul' g j := by apply Subtype.ext; exact (algebraMap K R).mapMatrix.map_mul g.val j.val }
  have hfi : Function.Injective f := by
    intro g j he
    apply Subtype.ext
    ext i k
    exact (algebraMap K R).injective (congrArg (fun u : Sp R => u.val i k) he)
  apply no_square_conjugate_closed (f a) (f b)
  · rw [← map_pow, h7, map_one]
  · exact fun he => hne (hfi (he.trans f.map_one.symm))
  · simpa only [map_mul, map_inv, map_pow] using congrArg f h
end Theory.SpecificGroups.SymplecticFour.SevenNormalizer
