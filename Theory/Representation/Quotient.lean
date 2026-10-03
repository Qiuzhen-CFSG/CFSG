module

public import Theory.Representation.SubrepresentationLattice
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.CharP.Reduced

/-!
# Inflation and descent of simple representations

Pullback along a surjective group homomorphism leaves the invariant-subspace
lattice unchanged and is fully faithful on representation isomorphisms.
A representation whose kernel contains a normal subgroup therefore descends,
on the same vector space, and irreducibility is preserved in both directions.

For finite-dimensional simple representations over an algebraically closed
field of characteristic `p`, a central `p`-subgroup lies in the kernel:
Schur's lemma makes each central element scalar, and injectivity of Frobenius
forces a scalar of `p`-power order to be one. This gives the representation
correspondence underlying the central quotient in modular block theory
(cf. Feit, *The Representation Theory of Finite Groups*, III.2.13).
Block membership and Cartan invariants require additional comparisons.
-/

public section

namespace Representation

variable {F G Q V W : Type*} [Field F] [Group G] [Group Q]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Surjective pullback does not change the invariant subspaces. -/
@[expose] def inflationSubrepresentationOrderIso
    (π : G →* Q) (hπ : Function.Surjective π) (ρ : Representation F Q V) :
    Subrepresentation (ρ.comp π) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun q v hv => by
    obtain ⟨g, rfl⟩ := hπ q
    exact S.apply_mem_toSubmodule g hv⟩
  invFun S := ⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (π g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem irreducible_comp_surjective_iff
    (π : G →* Q) (hπ : Function.Surjective π) (ρ : Representation F Q V) :
    IsIrreducible (ρ.comp π) ↔ IsIrreducible ρ :=
  (inflationSubrepresentationOrderIso π hπ ρ).isSimpleOrder_iff

/-- Inflation is fully faithful on representation isomorphisms. -/
@[expose] def inflationEquiv
    (π : G →* Q) (hπ : Function.Surjective π)
    (ρ : Representation F Q V) (σ : Representation F Q W) :
    Representation.Equiv (ρ.comp π) (σ.comp π) ≃ ρ.Equiv σ where
  toFun e := .mk e.toLinearEquiv (fun q => by
    obtain ⟨g, rfl⟩ := hπ q
    exact e.isIntertwining' g)
  invFun e := .mk e.toLinearEquiv (fun g => e.isIntertwining' (π g))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Descent on the same vector space when the specified normal subgroup acts trivially. -/
@[expose] def quotientOfLEKer (ρ : Representation F G V) (N : Subgroup G) [N.Normal]
    (hN : N ≤ ρ.ker) : Representation F (G ⧸ N) V :=
  QuotientGroup.lift N ρ hN

@[simp] theorem quotientOfLEKer_apply (ρ : Representation F G V)
    (N : Subgroup G) [N.Normal] (hN : N ≤ ρ.ker) (g : G) :
    quotientOfLEKer ρ N hN (QuotientGroup.mk' N g) = ρ g := rfl

@[simp] theorem quotientOfLEKer_comp (ρ : Representation F G V)
    (N : Subgroup G) [N.Normal] (hN : N ≤ ρ.ker) :
    (quotientOfLEKer ρ N hN).comp (QuotientGroup.mk' N) = ρ := rfl

theorem quotientOfLEKer_irreducible_iff (ρ : Representation F G V)
    (N : Subgroup G) [N.Normal] (hN : N ≤ ρ.ker) :
    IsIrreducible (quotientOfLEKer ρ N hN) ↔ IsIrreducible ρ :=
  (irreducible_comp_surjective_iff (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (quotientOfLEKer ρ N hN)).symm

/-- Central p-subgroups act trivially on simple modules in characteristic p. -/
theorem central_pSubgroup_le_ker
    [IsAlgClosed F] [FiniteDimensional F V]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (ρ : Representation F G V) [IsIrreducible ρ]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) (hp : IsPGroup p Z) :
    Z ≤ ρ.ker := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  intro z hz
  let f := IntertwiningMap.centralMul (ρ := ρ) z (hZ hz)
  obtain ⟨a, ha⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective f
  have hscalar : ρ z = a • (1 : Module.End F V) := by
    have h := congrArg IntertwiningMap.toLinearMap ha
    exact h.symm
  obtain ⟨n, hn⟩ := hp.exists_pow_pow_eq_one (⟨z, hz⟩ : Z)
  have hzpow : z ^ p ^ n = 1 := congrArg Subtype.val hn
  have hpow : a ^ p ^ n = 1 := by
    apply (FaithfulSMul.algebraMap_injective F (Module.End F V))
    rw [map_one, Algebra.algebraMap_eq_smul_one]
    calc
      _ = (ρ z) ^ p ^ n := by rw [hscalar, smul_pow, one_pow]
      _ = 1 := by rw [← map_pow, hzpow, map_one]
  have haone : a = 1 := by
    simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff p n 1 a).mp (by simpa using hpow)
  rw [MonoidHom.mem_ker, hscalar, haone, one_smul]

/-- Inflation acts on a group-algebra element through its image in the quotient. -/
theorem comp_asAlgebraHom_mapDomain
    (ρ : Representation F Q V) (f : G →* Q) (a : MonoidAlgebra F G) :
    Representation.asAlgebraHom (ρ.comp f) a =
      ρ.asAlgebraHom (MonoidAlgebra.mapDomainRingHom F f a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => simp [asAlgebraHom_single]

end Representation
