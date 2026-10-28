module

public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A uniform bound for central commutators of linear automorphisms

If `C = [A,B]` commutes with `A` and `B`, its eigenspaces are invariant under
both maps. On a `d`-dimensional eigenspace with eigenvalue `μ`, taking determinants
in `AB = CBA` gives `μ^d = 1`. Thus every eigenvalue has order dividing `n!`,
where `n` is the ambient dimension. Factorization of the characteristic polynomial
and Cayley–Hamilton give `(C^(n!) - 1)^n = 0`. In characteristic two, raising to
`2^n` gives the uniform exponent `n! * 2^n`.

This is the finite-dimensional ingredient for the algebraic-group bound. The
unipotent power argument is Borel, *Linear Algebraic Groups*, §4.1(a), in
`refs/KGroup/Bor1/Chapter1.tex`; no Jordan decomposition is needed here.
-/

open Module Polynomial
open scoped commutatorElement

namespace LinearMap.GeneralLinearGroup

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

private lemma eigenvalue_pow_finrank (A B C : Module.End k V)
    (hAi : Function.Injective A) (hBi : Function.Injective B)
    (hCA : Commute C A) (hCB : Commute C B)
    (hAB : A * B = C * (B * A)) (μ : k) :
    μ ^ Module.finrank k (C.eigenspace μ) = 1 := by
  let E := C.eigenspace μ
  have hA : ∀ v ∈ E, A v ∈ E := C.mapsTo_genEigenspace_of_comm hCA μ 1
  have hB : ∀ v ∈ E, B v ∈ E := C.mapsTo_genEigenspace_of_comm hCB μ 1
  let a : Module.End k E := A.restrict hA
  let b : Module.End k E := B.restrict hB
  have hai : Function.Injective a := by
    intro u v huv
    apply Subtype.ext
    exact hAi (congrArg Subtype.val huv)
  have hbi : Function.Injective b := by
    intro u v huv
    apply Subtype.ext
    exact hBi (congrArg Subtype.val huv)
  have hda : a.det ≠ 0 := by
    intro hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hai)
  have hdb : b.det ≠ 0 := by
    intro hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hbi)
  have hab : a * b = μ • (b * a) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change A (B v.val) = μ • B (A v.val)
    rw [← Module.End.mul_apply, hAB, Module.End.mul_apply]
    exact Module.End.mem_eigenspace_iff.mp (hB _ (hA _ v.property))
  have hd := congrArg LinearMap.det hab
  simp only [map_mul, LinearMap.det_smul] at hd
  apply mul_right_cancel₀ (mul_ne_zero hdb hda)
  calc
    μ ^ Module.finrank k E * (b.det * a.det) = a.det * b.det := hd.symm
    _ = 1 * (b.det * a.det) := by ring


private lemma eigenvalue_pow_factorial (A B C : Module.End k V)
    (hAi : Function.Injective A) (hBi : Function.Injective B)
    (hCA : Commute C A) (hCB : Commute C B)
    (hAB : A * B = C * (B * A)) {μ : k} (hμ : C.HasEigenvalue μ) :
    μ ^ (Module.finrank k V).factorial = 1 := by
  have hd : 0 < Module.finrank k (C.eigenspace μ) := by
    exact Nat.pos_of_ne_zero (fun hz => hμ (Submodule.finrank_eq_zero.mp hz))
  obtain ⟨r, hr⟩ := Nat.dvd_factorial hd (C.eigenspace μ).finrank_le
  rw [hr, pow_mul, eigenvalue_pow_finrank A B C hAi hBi hCA hCB hAB μ, one_pow]

private lemma pow_factorial_sub_one_pow_finrank [IsAlgClosed k] (A B C : Module.End k V)
    (hAi : Function.Injective A) (hBi : Function.Injective B)
    (hCA : Commute C A) (hCB : Commute C B)
    (hAB : A * B = C * (B * A)) :
    (C ^ (Module.finrank k V).factorial - 1) ^ Module.finrank k V = 0 := by
  let n := Module.finrank k V
  let q : k[X] := X ^ n.factorial - 1
  have hs := IsAlgClosed.splits C.charpoly
  have hc : C.charpoly.roots.card = n := by
    rw [← hs.natDegree_eq_card_roots, C.charpoly_natDegree]
  have hd : C.charpoly ∣ q ^ n := by
    rw [hs.eq_prod_roots, C.charpoly_monic.leadingCoeff, Polynomial.C_1, one_mul]
    have hdiv := Multiset.prod_dvd_prod_of_dvd
      (S := C.charpoly.roots) (fun μ : k => X - Polynomial.C μ) (fun _ => q) (by
        intro μ hμ
        apply Polynomial.dvd_iff_isRoot.mpr
        have hev : C.HasEigenvalue μ :=
          (Module.End.hasEigenvalue_iff_isRoot_charpoly C μ).mpr
            ((Polynomial.mem_roots C.charpoly_monic.ne_zero).mp hμ)
        simp only [Polynomial.IsRoot, q, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_one]
        exact sub_eq_zero.mpr (eigenvalue_pow_factorial A B C hAi hBi hCA hCB hAB hev))
    simpa [Multiset.map_const', hc] using hdiv
  have hz := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hd C.aeval_self_charpoly
  simpa [q, n] using hz

private lemma end_pow_factorial_mul_two_pow [IsAlgClosed k] [CharP k 2]
    (A B C : Module.End k V)
    (hAi : Function.Injective A) (hBi : Function.Injective B)
    (hCA : Commute C A) (hCB : Commute C B)
    (hAB : A * B = C * (B * A)) :
    C ^ ((Module.finrank k V).factorial * 2 ^ Module.finrank k V) = 1 := by
  nontriviality V
  let : ExpChar (Module.End k V) 2 :=
    expChar_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective k (Module.End k V)) 2
  have hz := pow_eq_zero_of_le
    (Nat.le_of_lt (Nat.lt_two_pow_self (n := Module.finrank k V)))
    (pow_factorial_sub_one_pow_finrank A B C hAi hBi hCA hCB hAB)
  rw [sub_pow_expChar_pow_of_commute 2 _ (Commute.one_right _), one_pow,
    sub_eq_zero] at hz
  simpa only [pow_mul] using hz

/-- In dimension `n` over an algebraically closed field of characteristic two,
a commutator centralizing both its entries has order dividing `n! * 2^n`.
The statement includes the zero-dimensional space. -/
public theorem centralCommutator_pow_factorial_mul_two_pow_finrank [IsAlgClosed k] [CharP k 2]
    (A B : LinearMap.GeneralLinearGroup k V)
    (hCA : Commute ⁅A, B⁆ A) (hCB : Commute ⁅A, B⁆ B) :
    ⁅A, B⁆ ^ ((Module.finrank k V).factorial * 2 ^ Module.finrank k V) = 1 := by
  apply Units.ext
  change (↑⁅A, B⁆ : Module.End k V) ^
    ((Module.finrank k V).factorial * 2 ^ Module.finrank k V) = 1
  apply end_pow_factorial_mul_two_pow (A : Module.End k V) (B : Module.End k V)
    (↑⁅A, B⁆ : Module.End k V) A.toLinearEquiv.injective B.toLinearEquiv.injective
    (hCA.map (Units.coeHom _)) (hCB.map (Units.coeHom _))
  have hAB : A * B = ⁅A, B⁆ * (B * A) := by
    simp [commutatorElement_def, mul_assoc]
  exact congrArg Units.val hAB

end LinearMap.GeneralLinearGroup
