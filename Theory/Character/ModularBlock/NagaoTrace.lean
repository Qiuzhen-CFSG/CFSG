module

public import Theory.Character.ModularBlock.TwoElementSpecialization
public import Theory.Character.ModularBlock.IdempotentRestriction

/-!
# Nagao Trace

An odd finite-order endomorphism of a finite projective module over an
order-two group algebra has scalar trace zero after multiplication by the
nonidentity group element, when the coefficient ring is local and two is a
nonunit. The group algebra is local, hence the projective module is free.
The trace is the difference of the trivial and sign matrix specializations;
odd-order rigidity makes those traces equal.

The representation interfaces transport this calculation along the exact
restricted-module equivalence. In particular, if a representation restricts
projectively to the cyclic subgroup of an involution, every commuting
odd-order element has trace zero after multiplication by that involution.
These are the Nagao trace inputs to the Z* block argument.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/NagaoTrace.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators
open Module

namespace ModularBlock.NagaoTrace

universe u v

attribute [local instance] Fintype.ofFinite

/-- An odd finite-order `R[C₂]`-linear endomorphism has trace zero after
multiplication by the nonidentity element of `C₂`. -/
theorem trace_lsmul_comp_eq_zero_of_odd_order
    {R C M : Type*} [CommRing R] [IsLocalRing R]
    [CommGroup C] [Finite C]
    [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R C) M]
    [IsScalarTower R (MonoidAlgebra R C) M]
    [Module.Free (MonoidAlgebra R C) M]
    [Module.Finite (MonoidAlgebra R C) M]
    (h2 : ¬ IsUnit (2 : R))
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hC : Nat.card C = 2)
    (f : M →ₗ[MonoidAlgebra R C] M) {n : ℕ} (hn : Odd n)
    (hf : f ^ n = 1) :
    LinearMap.trace R M
        (((LinearMap.lsmul (MonoidAlgebra R C) M
          (MonoidAlgebra.of R C c)).comp f).restrictScalars R) = 0 := by
  classical
  obtain ⟨d, hd, hd_unique⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hC
  have hcd : c = d := hd_unique c hc
  have hall (g : C) : g = 1 ∨ g = c := by
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr ((hd_unique g hg).trans hcd.symm)
  let bM := Module.Free.chooseBasis (MonoidAlgebra R C) M
  let F := LinearMap.toMatrix bM bM f
  have hF : F ^ n = 1 := by
    dsimp [F]
    rw [LinearMap.toMatrix_pow, hf, LinearMap.toMatrix_one]
  rw [trace_lsmul_comp_eq_evalPlus_sub_evalMinus
    bM c hc hc2 hC hall f]
  have heq := matrix_trace_evalPlus_eq_evalMinus_of_odd_order
    h2 c hc hc2 hall hn hF
  rw [heq, sub_self]

/-- Projective version of `trace_lsmul_comp_eq_zero_of_odd_order`.  The
order-two group algebra is local, so finite projective modules are free. -/
theorem trace_lsmul_comp_eq_zero_of_projective_odd_order
    {R C M : Type*} [CommRing R] [IsLocalRing R]
    [CommGroup C] [Finite C]
    [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R C) M]
    [IsScalarTower R (MonoidAlgebra R C) M]
    [Module.Projective (MonoidAlgebra R C) M]
    [Module.Finite (MonoidAlgebra R C) M]
    (h2 : ¬ IsUnit (2 : R))
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hC : Nat.card C = 2)
    (f : M →ₗ[MonoidAlgebra R C] M) {n : ℕ} (hn : Odd n)
    (hf : f ^ n = 1) :
    LinearMap.trace R M
        (((LinearMap.lsmul (MonoidAlgebra R C) M
          (MonoidAlgebra.of R C c)).comp f).restrictScalars R) = 0 := by
  let : IsLocalRing (MonoidAlgebra R C) :=
    CentralIdempotentSupport.isLocalRing_monoidAlgebra_of_card_two h2 hC
  let : Module.Free (MonoidAlgebra R C) M :=
    Module.free_of_flat_of_isLocalRing
  exact trace_lsmul_comp_eq_zero_of_odd_order
    h2 c hc hc2 hC f hn hf

/-- Representation-theoretic form of the projective odd-order trace theorem.

If the restriction of `rho` along a two-element subgroup `C` is finite
projective over `R[C]`, then every odd-order element centralizing that subgroup
has trace zero on the coset of its nonidentity element. -/
theorem trace_mul_eq_zero_of_projective_restriction_of_odd_order
    {R C G V : Type*} [CommRing R] [IsLocalRing R]
    [CommGroup C] [Finite C] [Group G]
    [AddCommGroup V] [Module R V]
    (rho : Representation R G V) (phi : C →* G)
    [Module.Projective (MonoidAlgebra R C)
      (Representation.asModule (rho.comp phi : Representation R C V))]
    [Module.Finite (MonoidAlgebra R C)
      (Representation.asModule (rho.comp phi : Representation R C V))]
    (h2 : ¬ IsUnit (2 : R))
    (c : C) (hc : c ≠ 1) (hc2 : c * c = 1)
    (hC : Nat.card C = 2)
    (x : G) (hcomm : ∀ g : C, x * phi g = phi g * x)
    {n : ℕ} (hn : Odd n) (hxpow : x ^ n = 1) :
    LinearMap.trace R V (rho (phi c * x)) = 0 := by
  let sigma : Representation R C V := rho.comp phi
  let T : sigma.IntertwiningMap sigma :=
    (rho x).intertwiningMap_of_isIntertwiningMap sigma sigma (by
      intro g v
      change rho x (rho (phi g) v) = rho (phi g) (rho x v)
      change (rho x * rho (phi g)) v = (rho (phi g) * rho x) v
      rw [← map_mul, hcomm, map_mul])
  let f : Module.End (MonoidAlgebra R C) sigma.asModule :=
    Representation.IntertwiningMap.equivAlgEnd sigma T
  have hTcoe (k : ℕ) : (T ^ k).toLinearMap = (rho x) ^ k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, pow_succ,
        Representation.IntertwiningMap.coe_mul, ih]
      rfl
  have hTpow : T ^ n = 1 := by
    apply Representation.IntertwiningMap.ext
    rw [hTcoe]
    change (rho x) ^ n = 1
    rw [← map_pow, hxpow, map_one]
  have hfpow : f ^ n = 1 := by
    dsimp [f]
    rw [← map_pow, hTpow, map_one]
  have hzero := trace_lsmul_comp_eq_zero_of_projective_odd_order
    (R := R) (C := C) (M := sigma.asModule)
    h2 c hc hc2 hC f hn hfpow
  let L : Module.End R sigma.asModule :=
    (((LinearMap.lsmul (MonoidAlgebra R C) sigma.asModule
      (MonoidAlgebra.of R C c)).comp f).restrictScalars R)
  have hconj : sigma.asModuleEquiv.conj L = rho (phi c * x) := by
    ext v
    change sigma.asModuleEquiv
        (MonoidAlgebra.of R C c • f (sigma.asModuleEquiv.symm v)) =
      rho (phi c * x) v
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
    change rho (phi c) (rho x v) = rho (phi c * x) v
    rw [map_mul]
    rfl
  calc
    LinearMap.trace R V (rho (phi c * x)) =
        LinearMap.trace R V (sigma.asModuleEquiv.conj L) := by rw [hconj]
    _ = LinearMap.trace R sigma.asModule L :=
      LinearMap.trace_conj' L sigma.asModuleEquiv
    _ = 0 := hzero

/-- The same theorem with the cyclic subgroup generated by an involution as
the source of the restriction.  This formulation is convenient in section
arguments: the caller only supplies the projectivity of the restricted module
and commutation with the involution. -/
theorem trace_z_mul_eq_zero_of_projective_zpowers_restriction_of_odd_order
    {R G V : Type*} [CommRing R] [IsLocalRing R]
    [Group G] [AddCommGroup V] [Module R V]
    (rho : Representation R G V) (z : G)
    [Module.Projective (MonoidAlgebra R (Subgroup.zpowers z))
      (Representation.asModule
        (rho.comp (Subgroup.zpowers z).subtype :
          Representation R (Subgroup.zpowers z) V))]
    [Module.Finite (MonoidAlgebra R (Subgroup.zpowers z))
      (Representation.asModule
        (rho.comp (Subgroup.zpowers z).subtype :
          Representation R (Subgroup.zpowers z) V))]
    (h2 : ¬ IsUnit (2 : R))
    (hz : z ≠ 1) (hz2 : z ^ 2 = 1)
    (x : G) (hxz : Commute x z) (hxodd : Odd (orderOf x)) :
    LinearMap.trace R V (rho (z * x)) = 0 := by
  -- A cyclic subgroup carries its canonical commutative-group structure.
  let : CommGroup (Subgroup.zpowers z) := IsCyclic.commGroup
  let c : Subgroup.zpowers z := ⟨z, Subgroup.mem_zpowers z⟩
  have hc : c ≠ 1 := by
    intro h
    exact hz (congrArg Subtype.val h)
  have hc2 : c * c = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hz2
  have hzOrder : orderOf z = 2 := orderOf_eq_prime hz2 hz
  have hC : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hzOrder]
  let : Finite (Subgroup.zpowers z) :=
    Nat.finite_of_card_ne_zero (by omega)
  have hcomm : ∀ g : Subgroup.zpowers z,
      x * (Subgroup.zpowers z).subtype g =
        (Subgroup.zpowers z).subtype g * x := by
    rw [Subgroup.forall_zpowers]
    intro m
    exact (hxz.zpow_right m).eq
  simpa [c] using
    trace_mul_eq_zero_of_projective_restriction_of_odd_order
      rho (Subgroup.zpowers z).subtype h2 c hc hc2 hC x hcomm hxodd
        (pow_orderOf_eq_one x)

end ModularBlock.NagaoTrace

