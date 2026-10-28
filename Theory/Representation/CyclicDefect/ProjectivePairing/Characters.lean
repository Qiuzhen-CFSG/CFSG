module

public import Theory.Representation.CyclicRootBrauerCharacter
public import Theory.LinearAlgebra.CharpolySubquotient
public import Theory.Representation.Quotient
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RepresentationTheory.Submodule


/-!
# Operations on cyclic-root Brauer characters

Root powers give a multiplicative correspondence on the chosen cyclic group.
Characteristic polynomials factor over an invariant subspace and quotient,
so the lifted values add with their natural multiplicities. On elements whose
orders divide the root order, semisimplicity gives an eigenbasis. Tensoring
these bases proves multiplicativity; the dual basis gives complex conjugation
and the linear-Hom formula.

This is the eigenvalue argument used in Feit, *The Representation Theory of
Finite Groups*, IV.2–3, in particular in the projective reciprocity proof IV.3.3.
It uses the actual `CyclicRootLift` and is independent of the characteristic-two
Brauer-character interfaces.
-/

public section

noncomputable section
open scoped BigOperators TensorProduct
open Representation
namespace Representation.CyclicRootLift
variable {K : Type*} [Field K] {m : ℕ} (L : CyclicRootLift K m)

theorem eigenvalue_pow_nat (j : ℕ) :
    L.eigenvalue (L.modularRoot ^ j) = L.complexRoot ^ j := by
  have hm : NeZero m := ⟨L.positive.ne'⟩
  have hK : L.modularRoot ^ j = L.modularRoot ^ (j % m) := by
    conv_lhs => rw [← Nat.mod_add_div j m, pow_add, pow_mul,
      L.modular_primitive.pow_eq_one, one_pow, mul_one]
  have hC : L.complexRoot ^ j = L.complexRoot ^ (j % m) := by
    conv_lhs => rw [← Nat.mod_add_div j m, pow_add, pow_mul,
      L.complex_primitive.pow_eq_one, one_pow, mul_one]
  rw [hK, L.eigenvalue_pow (⟨j % m, Nat.mod_lt _ L.positive⟩ : Fin m), ← hC]

theorem eigenvalue_mul {x y : K} (hx : x ^ m = 1) (hy : y ^ m = 1) :
    L.eigenvalue (x * y) = L.eigenvalue x * L.eigenvalue y := by
  let : NeZero m := ⟨L.positive.ne'⟩
  obtain ⟨i, _, rfl⟩ := L.modular_primitive.eq_pow_of_pow_eq_one hx
  obtain ⟨j, _, rfl⟩ := L.modular_primitive.eq_pow_of_pow_eq_one hy
  rw [← pow_add, L.eigenvalue_pow_nat, L.eigenvalue_pow_nat,
    L.eigenvalue_pow_nat, pow_add]

variable {G V : Type*} [Monoid G] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem value_subquotient (ρ : Representation K G V) (S : Subrepresentation ρ) (g : G) :
    L.value ρ g = L.value S.toRepresentation g +
      L.value (ρ.quotient S.toSubmodule S.apply_mem_toSubmodule) g := by
  unfold value
  change ((ρ g).charpoly.roots.map L.eigenvalue).sum =
    (((ρ g).restrict (S.apply_mem_toSubmodule g)).charpoly.roots.map L.eigenvalue).sum +
    ((S.toSubmodule.mapQ S.toSubmodule (ρ g)
      (S.apply_mem_toSubmodule g)).charpoly.roots.map L.eigenvalue).sum
  rw [LinearMap.charpoly_eq_charpoly_mul_charpoly S.toSubmodule (ρ g)
    (S.apply_mem_toSubmodule g),
    Polynomial.roots_mul (mul_ne_zero (LinearMap.charpoly_monic _).ne_zero
      (LinearMap.charpoly_monic _).ne_zero), Multiset.map_add, Multiset.sum_add]

private theorem exists_eigenbasis [IsAlgClosed K] (f : Module.End K V)
    (hf : f.IsSemisimple) :
    ∃ (b : Module.Basis (Fin (Module.finrank K V)) K V)
      (a : Fin (Module.finrank K V) → K), ∀ i, f (b i) = a i • b i := by
  classical
  let E : f.Eigenvalues → Submodule K V := fun a => f.eigenspace a
  have htop : iSup E = ⊤ := by
    apply top_unique
    rw [← hf.iSup_eigenspace_eq_top]
    apply iSup_le
    intro a
    by_cases ha : f.HasEigenvalue a
    · exact le_iSup E ⟨a, ha⟩
    · rw [show f.eigenspace a = ⊥ from not_not.mp ha]
      exact bot_le
  let h : DirectSum.IsInternal E :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (f.eigenspaces_iSupIndep.comp Subtype.coe_injective) htop
  let b := h.collectedBasis (fun a => Module.finBasis K (E a))
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  refine ⟨b.reindex e, fun i => ((e.symm i).1 : K), fun i => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact Module.End.mem_eigenspace_iff.mp (h.collectedBasis_mem _ (e.symm i))

private theorem value_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι]
    (ρ : Representation K G V) (g : G) (b : Module.Basis ι K V) (a : ι → K)
    (ha : ∀ i, ρ g (b i) = a i • b i) :
    L.value ρ g = ∑ i, L.eigenvalue (a i) := by
  classical
  have hmat : LinearMap.toMatrix b b (ρ g) = Matrix.diagonal a := by
    ext i j
    simp only [LinearMap.toMatrix_apply, ha, map_smul, Module.Basis.repr_self,
      Finsupp.smul_single, smul_eq_mul, mul_one, Matrix.diagonal_apply, Finsupp.single_apply]
    split_ifs <;> simp_all
  rw [value, ← LinearMap.charpoly_toMatrix (ρ g) b, hmat, Matrix.charpoly_diagonal]
  have he : (∏ i, (Polynomial.X - Polynomial.C (a i))).roots = Finset.univ.val.map a := by
    rw [Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr
      (fun i _ => Polynomial.X_sub_C_ne_zero _))]
    simp
  rw [he, Multiset.map_map]
  rfl

omit [FiniteDimensional K V] in
include L in
private theorem semisimple_of_pow (ρ : Representation K G V) (g : G) (hg : g ^ m = 1) :
    Module.End.IsSemisimple (ρ g) := by
  let : NeZero m := ⟨L.positive.ne'⟩
  let : NeZero (m : K) := L.modular_primitive.neZero'
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (Polynomial.X : Polynomial K) ^ m - 1)
  · exact (Polynomial.X_pow_sub_one_separable_iff.mpr (NeZero.ne (m : K))).squarefree
  · simp only [map_sub, map_pow, Polynomial.aeval_X, map_one]
    rw [← map_pow, hg, map_one, sub_self]

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem value_tensor [IsAlgClosed K] (ρ : Representation K G V)
    (σ : Representation K G W) (g : G) (hg : g ^ m = 1) :
    L.value (ρ.tprod σ) g = L.value ρ g * L.value σ g := by
  obtain ⟨b, a, ha⟩ := exists_eigenbasis (ρ g) (L.semisimple_of_pow ρ g hg)
  obtain ⟨c, z, hz⟩ := exists_eigenbasis (σ g) (L.semisimple_of_pow σ g hg)
  have hroot (i) : a i ^ m = 1 := by
    apply root_pow_eq_one ρ g hg
    apply (Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).mpr
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (ha i), b.ne_zero i⟩)
  have zroot (i) : z i ^ m = 1 := by
    apply root_pow_eq_one σ g hg
    apply (Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).mpr
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (hz i), c.ne_zero i⟩)
  rw [L.value_eq_sum_of_eigenbasis (ρ.tprod σ) g (b.tensorProduct c)
    (fun ij => a ij.1 * z ij.2) (by
      intro ⟨i,j⟩
      simp [ha, hz, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, mul_comm]),
    L.value_eq_sum_of_eigenbasis ρ g b a ha,
    L.value_eq_sum_of_eigenbasis σ g c z hz]
  simp_rw [Fintype.sum_prod_type, L.eigenvalue_mul (hroot _) (zroot _)]
  rw [Finset.sum_mul_sum]


theorem eigenvalue_inv {x : K} (hx : x ^ m = 1) :
    L.eigenvalue x⁻¹ = star (L.eigenvalue x) := by
  have hx0 : x ≠ 0 := by
    intro he
    simp [he, L.positive.ne'] at hx
  have hi : x⁻¹ ^ m = 1 := by rw [inv_pow, hx, inv_one]
  have hm : L.eigenvalue x * L.eigenvalue x⁻¹ = 1 := by
    rw [← L.eigenvalue_mul hx hi, mul_inv_cancel₀ hx0, L.eigenvalue_one]
  have hn : ‖L.eigenvalue x‖ = 1 := by
    let : NeZero m := ⟨L.positive.ne'⟩
    obtain ⟨j, _, rfl⟩ := L.modular_primitive.eq_pow_of_pow_eq_one hx
    rw [L.eigenvalue_pow_nat, norm_pow, L.complex_primitive.norm'_eq_one L.positive.ne', one_pow]
  exact (eq_inv_of_mul_eq_one_right hm).trans (Complex.inv_eq_conj hn)

section Group
variable {H : Type*} [Group H]

theorem value_dual [IsAlgClosed K] (ρ : Representation K H V)
    (g : H) (hg : g ^ m = 1) : L.value ρ.dual g = star (L.value ρ g) := by
  obtain ⟨b, a, ha⟩ := exists_eigenbasis (ρ g) (L.semisimple_of_pow ρ g hg)
  have hroot (i) : a i ^ m = 1 := by
    apply root_pow_eq_one ρ g hg
    apply (Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).mpr
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (ha i), b.ne_zero i⟩)
  have ha0 (i) : a i ≠ 0 := by
    intro h
    simpa [h, L.positive.ne'] using hroot i
  have hi (i) : ρ g⁻¹ (b i) = (a i)⁻¹ • b i := by
    apply (ρ.apply_bijective g).injective
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    simp only [Module.End.one_apply, map_smul, ha, smul_smul, inv_mul_cancel₀ (ha0 i), one_smul]
  have hd (i) : ρ.dual g (b.dualBasis i) = (a i)⁻¹ • b.dualBasis i := by
    apply b.ext
    intro j
    change b.dualBasis i (ρ g⁻¹ (b j)) = ((a i)⁻¹ • b.dualBasis i) (b j)
    rw [hi]
    simp only [map_smul,
      LinearMap.smul_apply, Module.Basis.dualBasis_apply_self, smul_eq_mul]
    split_ifs <;> simp_all
  rw [L.value_eq_sum_of_eigenbasis ρ.dual g b.dualBasis _ hd,
    L.value_eq_sum_of_eigenbasis ρ g b a ha, star_sum]
  exact Finset.sum_congr rfl fun i _ => L.eigenvalue_inv (hroot i)

theorem value_linHom [IsAlgClosed K] (ρ : Representation K H V)
    (σ : Representation K H W) (g : H) (hg : g ^ m = 1) :
    L.value (linHom ρ σ) g = star (L.value ρ g) * L.value σ g := by
  rw [← L.value_equiv (G := H) (V := Module.Dual K V ⊗[K] W) (W := V →ₗ[K] W) (ρ := ρ.dual.tprod σ) (σ := linHom ρ σ) (Equiv.dualTensorHom ρ σ) g,
    L.value_tensor ρ.dual σ g hg, L.value_dual ρ g hg]

end Group

end Representation.CyclicRootLift
