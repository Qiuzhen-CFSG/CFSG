module

public import Theory.Representation.EndFieldRep

/-!
# Prime-dimensional faithful representations over finite fields

Schur's endomorphism field has degree dividing the dimension. If that
dimension is prime, a nonscalar endomorphism field makes the representation
one-dimensional over the larger field. All acting operators would then
commute, contrary to faithfulness and noncommutativity of the group.

This is the absolute-irreducibility step used for the eleven-dimensional
Mathieu modules in Aschbacher–Smith, H.13.2, printed p.395 of the combined
1 March 2004 manuscript.
-/

public section

open scoped MonoidAlgebra
namespace Representation

/-- A faithful irreducible representation of prime dimension over a finite field
is absolutely irreducible whenever the acting group is nonabelian. -/
theorem isAbsolutelyIrreducible_of_prime_finrank_of_faithful
    {F G V : Type*} [Field F] [Finite F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (hprime : (Module.finrank F V).Prime)
    (hnonab : ¬ IsMulCommutative G) : ρ.IsAbsolutelyIrreducible := by
  let E := Module.End F[G] ρ.asModule
  have ht := Module.finrank_mul_finrank F E ρ.asModule
  rw [ρ.asModuleEquiv.finrank_eq] at ht
  have hdiv : Module.finrank F E ∣ Module.finrank F V := ⟨_, ht.symm⟩
  rcases (Nat.dvd_prime hprime).mp hdiv with hE | hE
  · apply (isAbsolutelyIrreducible_iff_surjective ρ).mpr
    apply (algebraMap_surj_iff_surj ρ).mp
    exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hE).2
  · have hdim : Module.finrank E ρ.asModule = 1 := by
      rw [hE] at ht
      exact Nat.eq_of_mul_eq_mul_left hprime.pos (by simpa using ht)
    exfalso
    apply hnonab
    refine ⟨⟨fun a b => hf ?_⟩⟩
    have hc : ρ.endFieldRep a * ρ.endFieldRep b =
        ρ.endFieldRep b * ρ.endFieldRep a := by
      obtain ⟨x, hx, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
        hdim (ρ.endFieldRep a)
      obtain ⟨y, hy, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
        hdim (ρ.endFieldRep b)
      rw [hx, hy]
      simp [smul_smul, mul_comm]
    rw [map_mul, map_mul]
    apply LinearMap.ext
    intro v
    exact congrArg ρ.asModuleEquiv (DFunLike.congr_fun hc (ρ.asModuleEquiv.symm v))


end Representation
