module

public import Theory.Representation.BinaryPrimeDegree
public import Theory.Representation.BinaryCoprimeDegree.HyperplaneOrbit
public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds
public import Theory.Representation.ExtraspecialFixedPoints
public import Theory.Representation.EndFieldTrace
public import Theory.FieldTheory.SpanningFrobeniusPeriod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic

/-!
# Binary degrees for extraspecial and elementary abelian groups

For an odd prime `p`, a faithful irreducible binary representation of an
extraspecial group of order `p³` has degree `p * orderOf (2 : ZMod p)`.
Over the Schur endomorphism field its scalar extension is absolutely
irreducible of degree `p`. The character vanishes off the center, and its
central values are `p`th roots of unity. Since these traces span the Schur
field, their Frobenius period gives its exact binary degree.

Maschke decomposition then proves the faithful lower bound and, when the
central fixed space vanishes, divisibility by the exact irreducible degree.
The latter assertion is essential: a lower bound alone does not give the
order-27 divisibility used for the triple cover of A₇.

For an elementary abelian subgroup, the imported character-space decomposition
and orbit count give the degree bound and equality clause for any lower bound
on hyperplane orbit lengths. The minimum-orbit formulation below uses an
attained minimum: the existence of its hyperplane already forces the subgroup
to be nontrivial. The hyperplane-orbit module proves existence of this minimum
for every nontrivial finite elementary abelian subgroup.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, G.7.1(2),(3), printed p.347, and the A₇-cover argument
on printed p.349.
-/

public section

open scoped MonoidAlgebra TensorProduct DirectSum

namespace Representation.BinaryCoprimeDegree

/-- The attained minimum normalizer-orbit length gives the binary degree bound
and its full fixed-space equality clause. Attainment supplies nontriviality of
the elementary abelian subgroup, so no separate nontriviality input is needed. -/
theorem hyperplane_orbit_degree_of_minimum
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Subgroup G) [IsElementaryAbelian p P] {n : ℕ}
    (hn : IsMinimumHyperplaneOrbit p P n) :
    n * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V ∧
      (Module.finrank (ZMod 2) V = n * orderOf (2 : ZMod p) →
        ∀ H : Subgroup P, H.index = p →
          invariants (ρ.comp (P.subtype.comp H.subtype)) ≠ ⊥ →
          Module.finrank (ZMod 2)
            (invariants (ρ.comp (P.subtype.comp H.subtype))) = orderOf (2 : ZMod p)) := by
  have hP : P ≠ ⊥ := by
    intro hP
    subst P
    obtain ⟨H, hH, _⟩ := hn.1
    have htop : H = ⊤ := Subsingleton.elim _ _
    exact (Fact.out : p.Prime).ne_one (hH.symm.trans (Subgroup.index_eq_one.mpr htop))
  exact hyperplane_orbit_degree ρ hρ hp2 P hP n hn.2

private theorem traceField_degree {p : ℕ} (hp : p.Prime)
    {E : Type*} [Field E] [Finite E] [Algebra (ZMod 2) E]
    {ι : Type*} (τ : ι → E)
    (hspan : Submodule.span (ZMod 2) (Set.range τ) = ⊤)
    (hτ : ∀ i, τ i = 0 ∨ τ i ^ p = 1)
    (hnt : ∃ i, τ i ≠ 0 ∧ τ i ≠ 1) :
    Module.finrank (ZMod 2) E = orderOf (2 : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Module.Finite (ZMod 2) E := Module.Finite.of_finite
  have hdmod : 2 ^ orderOf (2 : ZMod p) ≡ 1 [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ p).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      pow_orderOf_eq_one (2 : ZMod p)
  apply Nat.dvd_antisymm
  · apply (FiniteField.forall_pow_eq_self_iff_finrank_dvd_of_span 2 τ hspan _).mp
    intro i
    rcases hτ i with hi | hi
    · simp [hi]
    · simpa only [pow_one] using pow_eq_pow_of_modEq hdmod hi
  · obtain ⟨i, hi0, hi1⟩ := hnt
    have horder : orderOf (τ i) = p := orderOf_eq_prime ((hτ i).resolve_left hi0) hi1
    have hfixed := (FiniteField.forall_pow_eq_self_iff_finrank_dvd_of_span 2 τ hspan
      (Module.finrank (ZMod 2) E)).mpr (dvd_refl _) i
    have hmod : 2 ^ Module.finrank (ZMod 2) E ≡ 1 [MOD p] := by
      rw [← horder]
      exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos,
        (hτ i).resolve_left hi0⟩).pow_eq_pow_iff_modEq.mp (by simpa using hfixed)
    apply orderOf_dvd_of_pow_eq_one
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff _ _ p).mpr hmod

/-- The exact binary degree of every faithful irreducible representation of
an extraspecial group of order `p³`, for odd `p`. -/
theorem extraspecial_irreducible_finrank {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {P V : Type*} [Group P] [Finite P] [IsExtraspecial p P]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) P V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (hcard : Nat.card P = p ^ 3) :
    Module.finrank (ZMod 2) V = p * orderOf (2 : ZMod p) := by
  let E := Module.End (ZMod 2)[P] ρ.asModule
  let F := AlgebraicClosure E
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let σ := extendScalars F ρ.endFieldRep
  let : IsIrreducible σ := IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep F
  have hendfaith : Function.Injective ρ.endFieldRep := by
    intro x y hxy
    apply hρ
    ext v
    have h := congrArg (fun f => ρ.asModuleEquiv (f (ρ.asModuleEquiv.symm v))) hxy
    simpa only [endFieldRep_apply, LinearEquiv.apply_symm_apply] using h
  have hσ : Function.Injective σ :=
    (extendScalars_faithful_iff F ρ.endFieldRep).1 hendfaith
  have hcF : ringChar F = 2 :=
    (Algebra.ringChar_eq E F).symm.trans
      ((Algebra.ringChar_eq (ZMod 2) E).symm.trans (ZMod.ringChar_zmod_n 2))
  have hp : p.Prime := Fact.out
  have hc : ¬ ringChar F ∣ Nat.card P := by
    rw [hcF, hcard]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have hdim : Module.finrank F (F ⊗[E] ρ.asModule) = p := by
    simpa only [pow_one] using
      finrank_eq_primePow_of_faithful_irreducible_isExtraspecial
        (q := p) (n := 1) σ hσ hcard hc
  have hpF : (p : F) = 1 := by
    have h := congrArg (algebraMap E F ∘ algebraMap (ZMod 2) E)
      (hp.odd_of_ne_two hp2).natCast_zmod_two
    simpa only [Function.comp_apply, map_natCast, map_one] using h
  let τ : P → E := fun g => LinearMap.trace E ρ.asModule (ρ.endFieldRep g)
  have htrace (g : P) :
      algebraMap E F (τ g) = LinearMap.trace F (F ⊗[E] ρ.asModule) (σ g) :=
    (LinearMap.trace_baseChange (ρ.endFieldRep g) F).symm
  have hscalar (z : P) (hz : z ∈ Subgroup.center P) :
      σ z = algebraMap E F (τ z) • 1 := by
    obtain ⟨a, ha⟩ := center_apply_eq_smul_id_of_irreducible σ hz
    have he : algebraMap E F (τ z) = a := by
      rw [htrace, ha, map_smul]
      simp only [smul_eq_mul, LinearMap.trace_one, hdim, hpF, mul_one]
    rw [he]
    exact ha
  have hτ : ∀ g, τ g = 0 ∨ τ g ^ p = 1 := by
    intro g
    by_cases hg : g ∈ Subgroup.center P
    · right
      have hgp : g ^ p = 1 := by
        have h := pow_card_eq_one' (x := (⟨g, hg⟩ : Subgroup.center P))
        rw [IsExtraspecial.center_order_p p P] at h
        exact congrArg Subtype.val h
      have hpow : (algebraMap E F (τ g) ^ p) •
          (1 : Module.End F (F ⊗[E] ρ.asModule)) = 1 := by
        calc
          _ = ((algebraMap E F (τ g)) • (1 : Module.End F (F ⊗[E] ρ.asModule))) ^ p := by
            simp only [smul_pow, one_pow]
          _ = 1 := by rw [← hscalar g hg, ← map_pow, hgp, map_one]
      have hnontriv : Nontrivial (F ⊗[E] ρ.asModule) :=
        Subrepresentation.irreducible_module_nontrivial σ
      have hinj : Function.Injective (algebraMap F (Module.End F (F ⊗[E] ρ.asModule))) :=
        (algebraMap F (Module.End F (F ⊗[E] ρ.asModule))).injective
      apply (algebraMap E F).injective
      rw [map_pow, map_one]
      exact hinj (by simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using hpow)
    · left
      apply (algebraMap E F).injective
      rw [map_zero, htrace]
      exact trace_eq_zero_of_not_mem_center_of_faithful_irreducible_isExtraspecial
        (q := p) σ hσ hg
  have hnt : ∃ g, τ g ≠ 0 ∧ τ g ≠ 1 := by
    have hZ : Nontrivial (Subgroup.center P) :=
      Finite.one_lt_card_iff_nontrivial.mp (by
        rw [IsExtraspecial.center_order_p p P]
        exact hp.one_lt)
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
    refine ⟨z, ?_, ?_⟩
    · intro hzero
      have hs : σ z = 0 := by rw [hscalar z z.property, hzero, map_zero, zero_smul]
      have he : (1 : Module.End F (F ⊗[E] ρ.asModule)) = 0 := by
        calc
          1 = σ (z : P)⁻¹ * σ z := by rw [← map_mul, inv_mul_cancel, map_one]
          _ = 0 := by rw [hs, mul_zero]
      let : Nontrivial (F ⊗[E] ρ.asModule) :=
        Subrepresentation.irreducible_module_nontrivial σ
      exact one_ne_zero he
    · intro hone
      have hs : σ z = σ 1 := by
        rw [hscalar z z.property, hone, map_one, one_smul, map_one]
      exact hz (Subtype.ext (hσ hs))
  have hE : Module.finrank (ZMod 2) E = orderOf (2 : ZMod p) :=
    traceField_degree hp τ (span_range_endFieldRep_trace ρ) hτ hnt
  have hdimE : Module.finrank E ρ.asModule = p := by
    rwa [Module.finrank_baseChange] at hdim
  calc
    Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) ρ.asModule :=
      ρ.asModuleEquiv.finrank_eq.symm
    _ = Module.finrank (ZMod 2) E * Module.finrank E ρ.asModule :=
      (Module.finrank_mul_finrank (ZMod 2) E ρ.asModule).symm
    _ = p * orderOf (2 : ZMod p) := by rw [hE, hdimE, Nat.mul_comm]



private theorem extraspecial_semisimple {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P V : Type*} [Group P] [Finite P] [IsExtraspecial p P]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) P V) (hcard : Nat.card P = p ^ 3) :
    IsSemisimpleModule (ZMod 2)[P] ρ.asModule := by
  apply isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
  right
  rw [ZMod.ringChar_zmod_n, hcard]
  refine ⟨Nat.prime_two, (Nat.prime_two.coprime_iff_not_dvd.mpr ?_).pow_right 3⟩
  intro hdiv
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).mp hdiv).symm

/-- Nontrivial central action already forces the extraspecial lower bound. -/
theorem extraspecial_finrank_le_of_center_not_le_ker
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P V : Type*} [Group P] [Finite P] [IsExtraspecial p P]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) P V) (hcard : Nat.card P = p ^ 3)
    (hcenter : ¬ Subgroup.center P ≤ ρ.ker) :
    p * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  let : IsSemisimpleModule (ZMod 2)[P] ρ.asModule := extraspecial_semisimple hp2 ρ hcard
  obtain ⟨m, hm, hmk⟩ := exists_simple_submodule_nontrivial_of_not_le_ker ρ
    (Subgroup.center P) hcenter
  let τ := (Subrepresentation.ofSubmodule' m).toRepresentation
  let : IsIrreducible τ := irreducible_of_ofSubmodule'_simple ρ hm
  have hτ : Function.Injective τ := (MonoidHom.ker_eq_bot_iff _).mp
    (ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := p) τ hmk)
  have hdim := extraspecial_irreducible_finrank hp2 τ hτ hcard
  rw [← hdim]
  exact Submodule.finrank_le (Subrepresentation.ofSubmodule' m).toSubmodule

/-- A faithful binary representation of an extraspecial group of order `p³`. -/
theorem extraspecial_finrank_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P V : Type*} [Group P] [Finite P] [IsExtraspecial p P]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) P V) (hρ : Function.Injective ρ)
    (hcard : Nat.card P = p ^ 3) :
    p * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  apply extraspecial_finrank_le_of_center_not_le_ker hp2 ρ hcard
  intro hZ
  have hbot : Subgroup.center P = ⊥ := by
    apply bot_unique
    simpa only [(MonoidHom.ker_eq_bot_iff _).mpr hρ] using hZ
  have hc := IsExtraspecial.center_order_p p P
  rw [hbot, Subgroup.card_bot] at hc
  exact (Fact.out : p.Prime).ne_one hc.symm

/-- Every simple constituent is faithful when the central fixed space is zero. -/
private theorem simple_faithful_of_center_invariants_eq_bot
    {p : ℕ} [Fact p.Prime]
    {P V : Type*} [Group P] [Finite P] [IsExtraspecial p P]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) P V)
    (hfix : Representation.invariants (ρ.comp (Subgroup.center P).subtype) = ⊥)
    (m : Submodule (ZMod 2)[P] ρ.asModule) (hm : IsSimpleModule (ZMod 2)[P] m) :
    Function.Injective (Subrepresentation.ofSubmodule' m).toRepresentation := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := p)
  intro hk
  let τ := (Subrepresentation.ofSubmodule' m).toRepresentation
  have hzero := invariants_ofSubmodule'_eq_bot_of_invariants_eq_bot ρ
    (Subgroup.center P) m hfix
  let : IsIrreducible τ := irreducible_of_ofSubmodule'_simple ρ hm
  let : Nontrivial (Subrepresentation.ofSubmodule' m).toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial τ
  obtain ⟨v, hv⟩ := exists_ne (0 : (Subrepresentation.ofSubmodule' m).toSubmodule)
  apply hv
  have hmem : v ∈ Representation.invariants (τ.comp (Subgroup.center P).subtype) := by
    rw [mem_invariants]
    intro z
    have hz := MonoidHom.mem_ker.mp (hk z.property)
    exact LinearMap.congr_fun hz v
  change v ∈ Representation.invariants
    ((Subrepresentation.ofSubmodule' m).toRepresentation.comp (Subgroup.center P).subtype) at hmem
  rw [hzero] at hmem
  exact hmem

/-- Central fixed-point freeness makes the exact irreducible degree divide the
whole binary dimension. -/
theorem extraspecial_degree_dvd_finrank
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P V : Type*} [Group P] [Finite P] [IsExtraspecial p P]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) P V) (hcard : Nat.card P = p ^ 3)
    (hfix : Representation.invariants (ρ.comp (Subgroup.center P).subtype) = ⊥) :
    p * orderOf (2 : ZMod p) ∣ Module.finrank (ZMod 2) V := by
  classical
  let : IsSemisimpleModule (ZMod 2)[P] ρ.asModule := extraspecial_semisimple hp2 ρ hcard
  let : Module.Finite (ZMod 2)[P] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) (ZMod 2)[P] ρ.asModule
  obtain ⟨n, S, e, hs⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp
    (ZMod 2)[P] ρ.asModule
  let (i : Fin n) : FiniteDimensional (ZMod 2) (S i) :=
    finiteDimensional_of_irreducible_finite_group
      (Subrepresentation.ofSubmodule' (S i)).toRepresentation
      (irreducible_of_ofSubmodule'_simple ρ (hs i))
  have hdim (i : Fin n) : Module.finrank (ZMod 2) (S i) = p * orderOf (2 : ZMod p) := by
    let τ := (Subrepresentation.ofSubmodule' (S i)).toRepresentation
    let : IsIrreducible τ := irreducible_of_ofSubmodule'_simple ρ (hs i)
    have hd := extraspecial_irreducible_finrank hp2 τ
      (simple_faithful_of_center_invariants_eq_bot (p := p) ρ hfix (S i) (hs i)) hcard
    exact hd
  rw [← ρ.asModuleEquiv.finrank_eq,
    (e.restrictScalars (ZMod 2)).finrank_eq]
  change p * orderOf (2 : ZMod p) ∣ Module.finrank (ZMod 2) (⨁ i : Fin n, S i)
  rw [Module.finrank_directSum]
  exact Finset.dvd_sum fun i _ => (hdim i).symm ▸ dvd_refl _

/-- The order-27 divisibility used in the triple-cover case of A₇. -/
theorem six_dvd_finrank_of_extraspecial_twentySeven
    {P V : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) P V) (hcard : Nat.card P = 27)
    (hfix : Representation.invariants (ρ.comp (Subgroup.center P).subtype) = ⊥) :
    6 ∣ Module.finrank (ZMod 2) V := by
  simpa only [BinaryPrimeDegree.orderOf_two_mod_three, Nat.reduceMul] using
    extraspecial_degree_dvd_finrank (p := 3) (by decide) ρ hcard hfix

end Representation.BinaryCoprimeDegree
