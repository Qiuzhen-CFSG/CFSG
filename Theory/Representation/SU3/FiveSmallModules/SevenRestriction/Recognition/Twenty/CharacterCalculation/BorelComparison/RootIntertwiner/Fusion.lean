module

public import Theory.Representation.ExtraspecialFixedPoints
public import Theory.Representation.InvariantsBaseChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure


/-!
# A common constituent for an extraspecial five-root

Let P be an extraspecial subgroup of order 125 whose ambient group fuses
all nonidentity powers of a generator of Z(P). Two nonzero representations
in characteristic two, both without Z(P)-invariants, have a nonzero map
between their restrictions to P.

Over an algebraic closure, Maschke supplies a faithful simple constituent
of the first module. Its central scalar is a primitive fifth root. Central
fusion produces that eigenvalue in the second module, and a simple
submodule of the corresponding central eigenspace has the same scalar.
The faithful constituents have degree five, so extraspecial uniqueness
identifies them. A semisimple extension of their inclusion gives a nonzero
map on the whole module. Base change of the intertwiner space descends
existence to the original field.

This is the common-constituent step for the actual SU₃(5) root in
`RootIntertwiner`. Source: the extraspecial representation theory formalized
in `ExtraspecialFixedPoints`, used in the root-group route to
Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3.
-/

open Subgroup
open scoped MonoidAlgebra TensorProduct
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison.RootIntertwiner
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem semisimple
    {P K V : Type*} [Group P] [Finite P] [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] (ρ : Representation K P V)
    (hc : Nat.card P = 5 ^ 3) : IsSemisimpleModule K[P] ρ.asModule := by
  apply isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
  right
  refine ⟨ringChar.eq K 2 ▸ Nat.prime_two, ?_⟩
  rw [ringChar.eq K 2, hc]
  decide

private theorem exists_faithful_simple
    {P K V : Type*} [Group P] [Finite P] [IsExtraspecial 5 P]
    [Field K] [CharP K 2] [AddCommGroup V] [Module K V] [Nontrivial V]
    (ρ : Representation K P V) (hc : Nat.card P = 5 ^ 3)
    (hfix : invariants (ρ.comp (center P).subtype) = ⊥) :
    ∃ m : Submodule K[P] ρ.asModule,
      IsSimpleModule K[P] m ∧
      Function.Injective (Subrepresentation.ofSubmodule' m).toRepresentation := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsSemisimpleModule K[P] ρ.asModule := semisimple ρ hc
  have hker : ¬ center P ≤ ρ.ker := by
    intro hk
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hm : v ∈ invariants (ρ.comp (center P).subtype) := by
      intro z
      exact LinearMap.congr_fun (MonoidHom.mem_ker.mp (hk z.property)) v
    rw [hfix] at hm
    exact hv hm
  obtain ⟨m, hm, hk⟩ := exists_simple_submodule_nontrivial_of_not_le_ker ρ (center P) hker
  exact ⟨m, hm, (MonoidHom.ker_eq_bot_iff _).mp
    (ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := 5) _ hk)⟩

private theorem central_scalar_primitive
    {P K V : Type*} [Group P] [Finite P] [IsExtraspecial 5 P]
    [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K P V) [IsIrreducible ρ] (hf : Function.Injective ρ)
    (z : P) (hz : z ∈ center P) (hz1 : z ≠ 1) :
    ∃ a : K, IsPrimitiveRoot a 5 ∧ ρ z = a • 1 := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨a, ha⟩ := center_apply_eq_smul_id_of_irreducible ρ hz
  have hpow : z ^ 5 = 1 := by
    have h := pow_card_eq_one' (x := (⟨z, hz⟩ : center P))
    rw [IsExtraspecial.center_order_p 5 P] at h
    exact congrArg Subtype.val h
  have ha5 : a ^ 5 = 1 := by
    have he := congrArg ρ hpow
    rw [map_pow, ha, smul_pow, one_pow, map_one] at he
    have hev := LinearMap.congr_fun he v
    have hev' : (a ^ 5 - 1) • v = 0 := by
      simpa only [sub_smul, one_smul, LinearMap.smul_apply, Module.End.one_apply,
        sub_eq_zero] using hev
    exact sub_eq_zero.mp ((smul_eq_zero.mp hev').resolve_right hv)
  have ha1 : a ≠ 1 := by
    intro h
    apply hz1
    apply hf
    simpa [h] using ha
  exact ⟨a, isPrimitiveRoot_of_mem_nthRootsFinset (by decide)
    ((Polynomial.mem_nthRootsFinset (by decide : 0 < 5) (1 : K)).mpr ha5) ha1, ha⟩

private def inclusion
    {P K V : Type*} [Group P] [Field K] [AddCommGroup V] [Module K V]
    {ρ : Representation K P V} (S : Subrepresentation ρ) :
    IntertwiningMap S.toRepresentation ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

private theorem nonzero_map_of_equiv
    {P K V W : Type*} [Group P] [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K P V) (σ : Representation K P W)
    [IsSemisimpleModule K[P] ρ.asModule]
    (S : Subrepresentation ρ) (T : Subrepresentation σ)
    [Nontrivial S.toSubmodule] (e : Equiv S.toRepresentation T.toRepresentation) :
    ∃ f : IntertwiningMap ρ σ, f ≠ 0 := by
  let i := inclusion S
  let j := (inclusion T).comp e.toIntertwiningMap
  let iM := (IntertwiningMap.equivLinearMapAsModule _ _) i
  let jM := (IntertwiningMap.equivLinearMapAsModule _ _) j
  have hi : Function.Injective iM := by
    intro x y h
    exact Subtype.ext h
  obtain ⟨fM, hfM⟩ := IsSemisimpleModule.extension_property iM hi jM
  let f := (IntertwiningMap.equivLinearMapAsModule _ _).symm fM
  refine ⟨f, ?_⟩
  intro hf
  obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
  have h := LinearMap.congr_fun hfM (S.toRepresentation.asModuleEquiv.symm v)
  change f (v : V) = (e v : W) at h
  have he : e v = 0 := by
    apply Subtype.ext
    simpa [hf] using h.symm
  exact hv (e.toLinearEquiv.injective (by simpa using he))

private theorem exists_primitive_eigenvector
    {P K V : Type*} [Group P] [Finite P] [IsExtraspecial 5 P]
    [Field K] [IsAlgClosed K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Nontrivial V]
    (ρ : Representation K P V) (hc : Nat.card P = 5 ^ 3)
    (hfix : invariants (ρ.comp (center P).subtype) = ⊥)
    (z : P) (hz : z ∈ center P) (hz1 : z ≠ 1) :
    ∃ a : K, IsPrimitiveRoot a 5 ∧ ∃ v : V, v ≠ 0 ∧ ρ z v = a • v := by
  obtain ⟨m, hm, hf⟩ := exists_faithful_simple ρ hc hfix
  let S := Subrepresentation.ofSubmodule' m
  let τ := S.toRepresentation
  let : IsIrreducible τ := irreducible_of_ofSubmodule'_simple ρ hm
  let : FiniteDimensional K S.toSubmodule :=
    finiteDimensional_of_irreducible_finite_group τ inferInstance
  let : Nontrivial S.toSubmodule := Subrepresentation.irreducible_module_nontrivial τ
  obtain ⟨a, ha, hτ⟩ := central_scalar_primitive τ hf z hz hz1
  obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
  refine ⟨a, ha, v, (fun h => hv (Subtype.ext h)), ?_⟩
  exact congrArg Subtype.val (LinearMap.congr_fun hτ v)

private theorem eigenvector_of_fusion
    {G K V : Type*} [Group G] [Field K] [IsAlgClosed K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Nontrivial V]
    (ρ : Representation K G V) (P : Subgroup G) [Finite P] [IsExtraspecial 5 P]
    (hc : Nat.card P = 5 ^ 3)
    (hfix : invariants ((ρ.comp P.subtype).comp (center P).subtype) = ⊥)
    (z : P) (hz : z ∈ center P) (hz1 : z ≠ 1)
    (hfusion : ∀ i : ℕ, 0 < i → i < 5 →
      ∃ g : G, g * (z : G) * g⁻¹ = (z : G) ^ i)
    (a : K) (ha : IsPrimitiveRoot a 5) :
    ∃ v : V, v ≠ 0 ∧ ρ (z : G) v = a • v := by
  obtain ⟨b, hb, v, hv, hscalar⟩ :=
    exists_primitive_eigenvector (ρ.comp P.subtype) hc hfix z hz hz1
  change ρ (z : G) v = b • v at hscalar
  obtain ⟨i, hi5, hi⟩ := hb.eq_pow_of_pow_eq_one ha.pow_eq_one
  have hi0 : 0 < i := by
    by_contra hn
    have he : i = 0 := by omega
    exact ha.ne_one (by decide) (by simpa [he] using hi.symm)
  obtain ⟨g, hg⟩ := hfusion i hi0 hi5
  refine ⟨ρ g⁻¹ v, ?_, ?_⟩
  · intro hh
    have h := congrArg (ρ g) hh
    simp only [map_zero, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
      map_one, Module.End.one_apply] at h
    exact hv h
  have hpow (j : ℕ) : ρ ((z : G) ^ j) v = b ^ j • v := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', map_mul]
      change ρ (z : G) (ρ ((z : G) ^ j) v) = _
      rw [ih, map_smul, hscalar, smul_smul, pow_succ]
  have hconj : (z : G) * g⁻¹ = g⁻¹ * (z : G) ^ i := by rw [← hg]; group
  rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul,
    Module.End.mul_apply, hpow, map_smul, hi]

private def centralEigenspace
    {P K V : Type*} [Group P] [Field K] [AddCommGroup V] [Module K V]
    (ρ : Representation K P V) (z : P) (hz : z ∈ center P) (a : K) :
    Subrepresentation ρ where
  toSubmodule := Module.End.eigenspace (ρ z) a
  apply_mem_toSubmodule g v hv := by
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [← Module.End.mul_apply, ← map_mul,
      ← mem_center_iff.mp hz g, map_mul, Module.End.mul_apply, hv, map_smul]

private theorem exists_simple_with_scalar
    {P K V : Type*} [Group P] [Finite P] [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V]
    (ρ : Representation K P V) (hc : Nat.card P = 5 ^ 3)
    (z : P) (hz : z ∈ center P) (a : K)
    (v : V) (hv : v ≠ 0) (hscalar : ρ z v = a • v) :
    ∃ m : Submodule K[P] ρ.asModule, IsSimpleModule K[P] m ∧
      (Subrepresentation.ofSubmodule' m).toRepresentation z = a • 1 := by
  let : IsSemisimpleModule K[P] ρ.asModule := semisimple ρ hc
  let L := centralEigenspace ρ z hz a
  have hL : L.asSubmodule ≠ ⊥ := by
    intro he
    have hmem : ρ.asModuleEquiv.symm v ∈ L.asSubmodule :=
      Module.End.mem_eigenspace_iff.mpr hscalar
    rw [he] at hmem
    exact hv (ρ.asModuleEquiv.symm.injective hmem)
  obtain ⟨m, hmL, hm⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le L.asSubmodule).resolve_left hL
  refine ⟨m, hm, ?_⟩
  ext w
  exact Module.End.mem_eigenspace_iff.mp (hmL w.property)

private theorem faithful_of_scalar
    {P K V : Type*} [Group P] [Finite P] [IsExtraspecial 5 P]
    [Field K] [AddCommGroup V] [Module K V] [Nontrivial V]
    (ρ : Representation K P V) (z : P) (hz : z ∈ center P)
    (a : K) (ha : a ≠ 1) (hscalar : ρ z = a • 1) : Function.Injective ρ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := 5)
  intro hk
  have he := MonoidHom.mem_ker.mp (hk hz)
  rw [hscalar] at he
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have he' : (a - 1) • v = 0 := by
    simpa only [sub_smul, one_smul, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] using LinearMap.congr_fun he v
  exact ha (sub_eq_zero.mp ((smul_eq_zero.mp he').resolve_right hv))

private theorem equiv_of_generator_scalar
    {P K V W : Type*} [Group P] [Finite P] [IsExtraspecial 5 P]
    [Field K] [IsAlgClosed K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K P V) (σ : Representation K P W)
    [IsIrreducible ρ] [IsIrreducible σ]
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (hc : Nat.card P = 5 ^ 3)
    (z : P) (hz : z ∈ center P) (hz1 : z ≠ 1)
    (a : K) (haρ : ρ z = a • 1) (haσ : σ z = a • 1) :
    Nonempty (Equiv ρ σ) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hchar : ¬ ringChar K ∣ Nat.card P := by rw [ringChar.eq K 2, hc]; decide
  have hdρ := finrank_eq_primePow_of_faithful_irreducible_isExtraspecial
    (q := 5) (n := 1) ρ hρ hc hchar
  have hdσ := finrank_eq_primePow_of_faithful_irreducible_isExtraspecial
    (q := 5) (n := 1) σ hσ hc hchar
  apply equiv_of_centerChar_eq_for_faithful_irreducible_isExtraspecial
    (q := 5) hσ hρ hchar
  intro w hw
  have hmem : (⟨w, hw⟩ : center P) ∈ Submonoid.powers (⟨z, hz⟩ : center P) :=
    mem_powers_iff_mem_zpowers.mpr (mem_zpowers_of_prime_card
      (IsExtraspecial.center_order_p 5 P) (by exact fun h => hz1 (congrArg Subtype.val h)))
  obtain ⟨n, hn⟩ := hmem
  have hzn : z ^ n = w := congrArg Subtype.val hn
  rw [← hzn]
  change LinearMap.trace K W (σ (z ^ n)) = LinearMap.trace K V (ρ (z ^ n))
  rw [map_pow σ, map_pow ρ, haρ, haσ, smul_pow, smul_pow, one_pow, one_pow,
    map_smul, map_smul, LinearMap.trace_one, LinearMap.trace_one, hdρ, hdσ]

private theorem exists_intertwiner_algClosed
    {G K V W : Type*} [Group G] [Field K] [IsAlgClosed K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Nontrivial V]
    [AddCommGroup W] [Module K W] [Nontrivial W]
    (ρ : Representation K G V) (σ : Representation K G W)
    (P : Subgroup G) [Finite P] [IsExtraspecial 5 P]
    (hc : Nat.card P = 5 ^ 3)
    (hρfix : invariants ((ρ.comp P.subtype).comp (center P).subtype) = ⊥)
    (hσfix : invariants ((σ.comp P.subtype).comp (center P).subtype) = ⊥)
    (z : P) (hz : z ∈ center P) (hz1 : z ≠ 1)
    (hfusion : ∀ i : ℕ, 0 < i → i < 5 →
      ∃ g : G, g * (z : G) * g⁻¹ = (z : G) ^ i) :
    ∃ f : IntertwiningMap (ρ.comp P.subtype) (σ.comp P.subtype), f ≠ 0 := by
  obtain ⟨m, hm, hmfaith⟩ := exists_faithful_simple (ρ.comp P.subtype) hc hρfix
  let S := Subrepresentation.ofSubmodule' m
  let τ := S.toRepresentation
  let : IsIrreducible τ := irreducible_of_ofSubmodule'_simple (ρ.comp P.subtype) hm
  let : FiniteDimensional K S.toSubmodule :=
    finiteDimensional_of_irreducible_finite_group τ inferInstance
  let : Nontrivial S.toSubmodule := Subrepresentation.irreducible_module_nontrivial τ
  obtain ⟨a, ha, hτ⟩ := central_scalar_primitive τ hmfaith z hz hz1
  obtain ⟨v, hv, hav⟩ := eigenvector_of_fusion σ P hc hσfix z hz hz1 hfusion a ha
  obtain ⟨n, hn, hν⟩ := exists_simple_with_scalar (σ.comp P.subtype) hc z hz a v hv hav
  let T := Subrepresentation.ofSubmodule' n
  let ν := T.toRepresentation
  let : IsIrreducible ν := irreducible_of_ofSubmodule'_simple (σ.comp P.subtype) hn
  let : FiniteDimensional K T.toSubmodule :=
    finiteDimensional_of_irreducible_finite_group ν inferInstance
  let : Nontrivial T.toSubmodule := Subrepresentation.irreducible_module_nontrivial ν
  have hnfaith := faithful_of_scalar ν z hz a (ha.ne_one (by decide)) hν
  obtain ⟨e⟩ := equiv_of_generator_scalar τ ν hmfaith hnfaith hc z hz hz1 a hτ hν
  let : IsSemisimpleModule K[P] (Representation.asModule (ρ.comp P.subtype)) := semisimple _ hc
  exact nonzero_map_of_equiv (ρ.comp P.subtype) (σ.comp P.subtype) S T e

/-- Central fusion in the ambient group gives a common nonlinear constituent
of two nonzero, root-center-free representations. The map is defined over
the original field, with no splitting hypothesis. -/
public theorem exists_intertwiner_of_fusion
    {G K V W : Type*} [Group G] [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Nontrivial W]
    (ρ : Representation K G V) (σ : Representation K G W)
    (P : Subgroup G) [Finite P] [IsExtraspecial 5 P]
    (hc : Nat.card P = 5 ^ 3)
    (hρfix : invariants ((ρ.comp P.subtype).comp (center P).subtype) = ⊥)
    (hσfix : invariants ((σ.comp P.subtype).comp (center P).subtype) = ⊥)
    (z : P) (hz : z ∈ center P) (hz1 : z ≠ 1)
    (hfusion : ∀ i : ℕ, 0 < i → i < 5 →
      ∃ g : G, g * (z : G) * g⁻¹ = (z : G) ^ i) :
    ∃ f : IntertwiningMap (ρ.comp P.subtype) (σ.comp P.subtype), f ≠ 0 := by
  classical
  let E := AlgebraicClosure K
  let : Nontrivial (E ⊗[K] V) := Module.nontrivial_of_finrank_pos
    (by rw [Module.finrank_baseChange]; exact Module.finrank_pos)
  let : Nontrivial (E ⊗[K] W) := Module.nontrivial_of_finrank_pos
    (by rw [Module.finrank_baseChange]; exact Module.finrank_pos)
  have hρE : invariants (((ρ.extendScalars E).comp P.subtype).comp (center P).subtype) = ⊥ := by
    change invariants (extendScalars E ((ρ.comp P.subtype).comp (center P).subtype)) = ⊥
    rw [invariants_extendScalars_eq_baseChange_of_finite, hρfix]
    simp
  have hσE : invariants (((σ.extendScalars E).comp P.subtype).comp (center P).subtype) = ⊥ := by
    change invariants (extendScalars E ((σ.comp P.subtype).comp (center P).subtype)) = ⊥
    rw [invariants_extendScalars_eq_baseChange_of_finite, hσfix]
    simp
  obtain ⟨f, hf⟩ := exists_intertwiner_algClosed (ρ.extendScalars E) (σ.extendScalars E)
    P hc hρE hσE z hz hz1 hfusion
  let e := intertwiningMapBaseChangeEquiv (E := E) (ρ.comp P.subtype) (σ.comp P.subtype)
  by_contra! hzero
  have htensor : ∀ t : E ⊗[K] IntertwiningMap (ρ.comp P.subtype) (σ.comp P.subtype), t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul a x => rw [hzero x, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  obtain ⟨t, ht⟩ := e.surjective f
  exact hf (by rw [← ht, htensor t, map_zero])

end
end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison.RootIntertwiner
