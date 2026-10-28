module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Analysis.Complex.Basic

/-!
# Brauer eigenvalue sums with a chosen root correspondence

A pair of primitive roots of the same positive order identifies their powers.
Lifting the roots of a representation's characteristic polynomial through this
correspondence, with their algebraic multiplicities, defines its Brauer value
on elements whose orders divide that root order. The definition retains natural
dimensions, unlike the trace in the coefficient field. It is independent of
coordinates and has the dimension as its value at the identity.

This is the eigenvalue definition of Brauer characters (Feit, *The
Representation Theory of Finite Groups*, Chapter I). The root order should be
prime to the coefficient characteristic in modular applications. No modular
place, decomposition theorem, or existence of an irreducible is assumed here.
-/

public section
noncomputable section

open scoped Classical

namespace Representation

/-- A chosen correspondence between roots in a coefficient field and in `ℂ`. -/
structure CyclicRootLift (K : Type*) [Field K] (m : ℕ) where
  positive : 0 < m
  modularRoot : K
  complexRoot : ℂ
  modular_primitive : IsPrimitiveRoot modularRoot m
  complex_primitive : IsPrimitiveRoot complexRoot m

namespace CyclicRootLift

variable {K : Type*} [Field K] {m : ℕ} (L : CyclicRootLift K m)

/-- Lift a power of the chosen root, and assign zero off that cyclic subgroup. -/
@[expose] def eigenvalue (x : K) : ℂ :=
  if h : ∃ j : Fin m, L.modularRoot ^ (j : ℕ) = x then
    L.complexRoot ^ (h.choose : ℕ)
  else 0

theorem eigenvalue_pow (j : Fin m) :
    L.eigenvalue (L.modularRoot ^ (j : ℕ)) = L.complexRoot ^ (j : ℕ) := by
  have h : ∃ k : Fin m, L.modularRoot ^ (k : ℕ) = L.modularRoot ^ (j : ℕ) :=
    ⟨j, rfl⟩
  rw [eigenvalue, dif_pos h]
  exact congrArg (L.complexRoot ^ ·)
    (L.modular_primitive.pow_inj h.choose.isLt j.isLt h.choose_spec)

@[simp] theorem eigenvalue_one : L.eigenvalue 1 = 1 := by
  simpa using L.eigenvalue_pow (⟨0, L.positive⟩ : Fin m)

/-- The lift preserves every root-order relation on its domain. -/
theorem eigenvalue_pow_eq_one {x : K} (hx : x ^ m = 1) {n : ℕ}
    (hn : x ^ n = 1) : L.eigenvalue x ^ n = 1 := by
  let : NeZero m := ⟨L.positive.ne'⟩
  obtain ⟨j, hj, rfl⟩ := L.modular_primitive.eq_pow_of_pow_eq_one hx
  rw [L.eigenvalue_pow (⟨j, hj⟩ : Fin m), ← pow_mul]
  apply (L.complex_primitive.pow_eq_one_iff_dvd _).mpr
  exact (L.modular_primitive.pow_eq_one_iff_dvd _).mp (by simpa [pow_mul] using hn)

variable {G V : Type*} [Monoid G] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Lift eigenvalues individually, retaining algebraic multiplicity. On elements
of order dividing `m`, this is the Brauer value for the chosen root pair. -/
@[expose] def value (ρ : Representation K G V) (g : G) : ℂ :=
  ((ρ g).charpoly.roots.map L.eigenvalue).sum

/-- Eigenvalues of a finite-order action lie in the expected root subgroup. -/
theorem root_pow_eq_one (ρ : Representation K G V) (g : G) {n : ℕ}
    (hg : g ^ n = 1) {x : K} (hx : x ∈ (ρ g).charpoly.roots) : x ^ n = 1 := by
  have heigen := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
    ((Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hx)
  obtain ⟨v, hv⟩ := heigen.exists_hasEigenvector
  have hpower := hv.pow_apply n
  rw [← map_pow, hg, map_one] at hpower
  exact (smul_left_injective K hv.2)
    (by simpa only [one_smul, Module.End.one_apply] using hpower.symm)

@[simp] theorem value_one (ρ : Representation K G V) :
    L.value ρ 1 = (Module.finrank K V : ℂ) := by
  simp only [value, map_one, LinearMap.charpoly_one]
  rw [show (1 : Polynomial K) = Polynomial.C 1 from rfl, Polynomial.roots_pow,
    Polynomial.roots_X_sub_C, Multiset.nsmul_singleton, Multiset.map_replicate,
    Multiset.sum_replicate, L.eigenvalue_one]
  simp

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The lifted value is invariant under an actual intertwining equivalence. -/
theorem value_equiv {ρ : Representation K G V} {σ : Representation K G W}
    (e : ρ.Equiv σ) (g : G) : L.value ρ g = L.value σ g := by
  have heq := e.toLinearEquiv.charpoly_conj (ρ g)
  rw [Representation.Equiv.conj_apply_self] at heq
  simp only [value, heq]

end CyclicRootLift
end Representation
