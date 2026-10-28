module

public import Theory.Representation.ExtraspecialFixedPoints
public import Theory.Representation.InvariantsBaseChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Exact multiplicity of a rational extraspecial five-center

A central eigenspace with nontrivial character is a semisimple sum of faithful
irreducible representations of the extraspecial group of order 125. Each
constituent has degree five. An ambient element conjugating a central generator
to its square gives the cycle of dimension inequalities at the eigenvalues
ε, ε², ε⁴, ε³; hence all four dimensions agree. The fifth eigenspace is the
space fixed by the actual embedded center. Nontrivial central action makes
the resulting multiple of twenty positive.

Extension to an algebraic closure preserves both nontrivial action and the
dimension of invariants. The formula therefore holds over every characteristic
two field, without an irreducibility or splitting-field assumption.

Source: the extraspecial degree calculation in `ExtraspecialFixedPoints` and
the root-group route to Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3. `NonlinearMultiplicity` applies this result to the literal
special-unitary root subgroup.
-/

open Subgroup
open scoped DirectSum MonoidAlgebra TensorProduct
namespace Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity

set_option backward.isDefEq.respectTransparency false in
private theorem degree_five_dvd
    {P K V : Type*} [Group P] [Finite P] [IsExtraspecial 5 P]
    [Field K] [IsAlgClosed K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K P V) (hc : Nat.card P = 5 ^ 3)
    (hfix : Representation.invariants (ρ.comp (center P).subtype) = ⊥) :
    5 ∣ Module.finrank K V := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hchar : ¬ ringChar K ∣ Nat.card P := by rw [ringChar.eq K 2, hc]; decide
  let : IsSemisimpleModule K[P] ρ.asModule := by
    apply isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
    right
    exact ⟨ringChar.eq K 2 ▸ Nat.prime_two,
      (ringChar.eq K 2 ▸ Nat.prime_two).coprime_iff_not_dvd.mpr hchar⟩
  let : Module.Finite K[P] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite K K[P] ρ.asModule
  obtain ⟨n, S, e, hs⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp K[P] ρ.asModule
  let (i : Fin n) : FiniteDimensional K (S i) :=
    finiteDimensional_of_irreducible_finite_group
      (Subrepresentation.ofSubmodule' (S i)).toRepresentation
      (irreducible_of_ofSubmodule'_simple ρ (hs i))
  have hd (i : Fin n) : Module.finrank K (S i) = 5 := by
    let τ := (Subrepresentation.ofSubmodule' (S i)).toRepresentation
    let : IsIrreducible τ := irreducible_of_ofSubmodule'_simple ρ (hs i)
    have hτ : Function.Injective τ := by
      apply (MonoidHom.ker_eq_bot_iff τ).mp
      apply ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := 5)
      intro hk
      have hz := invariants_ofSubmodule'_eq_bot_of_invariants_eq_bot ρ (center P) (S i) hfix
      let : Nontrivial (Subrepresentation.ofSubmodule' (S i)).toSubmodule :=
        Subrepresentation.irreducible_module_nontrivial τ
      obtain ⟨v, hv⟩ := exists_ne (0 : (Subrepresentation.ofSubmodule' (S i)).toSubmodule)
      apply hv
      have hm : v ∈ Representation.invariants (τ.comp (center P).subtype) := by
        intro z
        exact LinearMap.congr_fun (MonoidHom.mem_ker.mp (hk z.property)) v
      change v ∈ Representation.invariants
        ((Subrepresentation.ofSubmodule' (S i)).toRepresentation.comp (center P).subtype) at hm
      rw [hz] at hm
      exact hm
    exact finrank_eq_primePow_of_faithful_irreducible_isExtraspecial
      (q := 5) (n := 1) τ hτ hc hchar
  rw [← ρ.asModuleEquiv.finrank_eq, (e.restrictScalars K).finrank_eq]
  change 5 ∣ Module.finrank K (⨁ i : Fin n, S i)
  rw [Module.finrank_directSum]
  exact Finset.dvd_sum fun i _ => (hd i).symm ▸ dvd_refl _

private def centralEigenspace
    {P K V : Type*} [Group P] [Field K] [AddCommGroup V] [Module K V]
    (ρ : Representation K P V) (z : P) (hz : z ∈ center P) (a : K) :
    Subrepresentation ρ where
  toSubmodule := Module.End.eigenspace (ρ z) a
  apply_mem_toSubmodule g v hv := by
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [← Module.End.mul_apply, ← map_mul,
      ← mem_center_iff.mp hz g, map_mul, Module.End.mul_apply, hv, map_smul]

private theorem central_eigenspace_dvd
    {P K V : Type*} [Group P] [Finite P] [IsExtraspecial 5 P]
    [Field K] [IsAlgClosed K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K P V) (hc : Nat.card P = 5 ^ 3)
    (z : P) (hz : z ∈ center P) (a : K) (ha : a ≠ 1) :
    5 ∣ Module.finrank K (Module.End.eigenspace (ρ z) a) := by
  let W := centralEigenspace ρ z hz a
  apply degree_five_dvd W.toRepresentation hc
  apply bot_unique
  intro v hv
  have hfix := congrArg Subtype.val (hv ⟨z, hz⟩)
  have hscalar := Module.End.mem_eigenspace_iff.mp v.property
  have he : (a - 1) • (v : V) = 0 := by
    rw [sub_smul, one_smul, ← hscalar]
    exact sub_eq_zero.mpr hfix
  exact Subtype.ext ((smul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ha))

private theorem eigenspace_le_conjugate
    {K G V : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) {z g : G} {i : ℕ} (hg : g * z * g⁻¹ = z ^ i)
    (a : K) :
    Module.finrank K (Module.End.eigenspace (ρ z) a) ≤
      Module.finrank K (Module.End.eigenspace (ρ z) (a ^ i)) := by
  let W := Module.End.eigenspace (ρ z) a
  have hpow (j : ℕ) (v : W) : ρ (z ^ j) v = a ^ j • (v : V) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', map_mul]
      change ρ z (ρ (z ^ j) v) = _
      rw [ih, map_smul, Module.End.mem_eigenspace_iff.mp v.property, smul_smul, pow_succ]
  have hconj : z * g⁻¹ = g⁻¹ * z ^ i := by rw [← hg]; group
  let f : W →ₗ[K] Module.End.eigenspace (ρ z) (a ^ i) :=
    ((ρ g⁻¹).comp W.subtype).codRestrict _ (fun v => by
      apply Module.End.mem_eigenspace_iff.mpr
      change ρ z (ρ g⁻¹ (v : V)) = _
      rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul,
        Module.End.mul_apply, hpow, map_smul]
      rfl)
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  intro v w hvw
  apply Subtype.ext
  have hh := congrArg (fun t : Module.End.eigenspace (ρ z) (a ^ i) => ρ g (t : V)) hvw
  change ρ g (ρ g⁻¹ (v : V)) = ρ g (ρ g⁻¹ (w : V)) at hh
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hh

private theorem cyclic_five_dimension
    {K G V : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (z : G) (hz : z ^ 5 = 1)
    (g : G) (hg : g * z * g⁻¹ = z ^ 2)
    (a : K) (ha : IsPrimitiveRoot a 5) :
    Module.finrank K V = Module.finrank K (Module.End.eigenspace (ρ z) 1) +
      4 * Module.finrank K (Module.End.eigenspace (ρ z) a) := by
  classical
  let d (b : K) := Module.finrank K (Module.End.eigenspace (ρ z) b)
  have h12 : d a ≤ d (a ^ 2) := eigenspace_le_conjugate ρ hg a
  have h24 : d (a ^ 2) ≤ d (a ^ 4) := by
    have hh := eigenspace_le_conjugate ρ (i := 2) hg (a ^ 2)
    change d (a ^ 2) ≤ d ((a ^ 2) ^ 2) at hh
    rwa [← pow_mul] at hh
  have h43 : d (a ^ 4) ≤ d (a ^ 3) := by
    have hp : (a ^ 4) ^ 2 = a ^ 3 := by
      rw [← pow_mul, show 4 * 2 = 5 + 3 from rfl, pow_add, ha.pow_eq_one, one_mul]
    have hh := eigenspace_le_conjugate ρ (i := 2) hg (a ^ 4)
    change d (a ^ 4) ≤ d ((a ^ 4) ^ 2) at hh
    rwa [hp] at hh
  have h31 : d (a ^ 3) ≤ d a := by
    have hp : (a ^ 3) ^ 2 = a := by
      rw [← pow_mul, show 3 * 2 = 5 + 1 from rfl, pow_add, ha.pow_eq_one, one_mul, pow_one]
    have hh := eigenspace_le_conjugate ρ (i := 2) hg (a ^ 3)
    change d (a ^ 3) ≤ d ((a ^ 3) ^ 2) at hh
    rwa [hp] at hh
  have h2 : d (a ^ 2) = d a := by omega
  have h3 : d (a ^ 3) = d a := by omega
  have h4 : d (a ^ 4) = d a := by omega
  let u := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom z)
  have hpow : u ^ 5 = 1 := by
    change LinearMap.GeneralLinearGroup.generalLinearEquiv K V (ρ.asGroupHom z) ^ 5 = 1
    rw [← map_pow, ← map_pow, hz, map_one, map_one]
  have hi := proposition_2_4_a hpow (by decide : 5 ≥ 2) ha
  let A (i : Fin 5) := Module.End.eigenspace u.toLinearMap (a ^ (i : ℤ))
  let e : (⨁ i : Fin 5, A i) ≃ₗ[K] V :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hi
  have hdim : Module.finrank K V = ∑ i : Fin 5, d (a ^ (i : ℕ)) := by
    rw [← e.finrank_eq, Module.finrank_directSum]
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg (fun W : Submodule K V => Module.finrank K W)
    change Module.End.eigenspace (ρ z) (a ^ ((i : ℕ) : ℤ)) =
      Module.End.eigenspace (ρ z) (a ^ (i : ℕ))
    rw [zpow_natCast]
  rw [hdim]
  change (∑ i : Fin 5, d (a ^ (i : ℕ))) = d 1 + 4 * d a
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
    Nat.reduceAdd, pow_zero, pow_one]
  change d 1 + (d a + (d (a ^ 2) + (d (a ^ 3) + (d (a ^ 4) + 0)))) = _
  rw [h2, h3, h4]
  omega

/-- Over a splitting field, the four nontrivial central characters have
equal multiplicity and degree-five constituents. -/
public theorem multiplicity_algClosed
    {K G V : Type*} [Field K] [IsAlgClosed K] [CharP K 2] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (P : Subgroup G) [Finite P] [IsExtraspecial 5 P]
    (hc : Nat.card P = 5 ^ 3) (z : P) (hz : z ∈ center P) (hz1 : z ≠ 1)
    (hne : ρ (z : G) ≠ 1) (g : G) (hg : g * (z : G) * g⁻¹ = (z : G) ^ 2) :
    ∃ a : ℕ, 0 < a ∧ Module.finrank K V =
      Module.finrank K (Representation.invariants
        (ρ.comp ((center P).map P.subtype).subtype)) + 20 * a := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hzpow : (z : G) ^ 5 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨z, hz⟩ : center P))
    rw [IsExtraspecial.center_order_p 5 P] at hh
    exact congrArg (fun w : center P => (w : G)) hh
  obtain ⟨ε, hε⟩ := exists_primitiveRoot_of_isAlgClosed_not_dvd
    (F := K) (h := 5) (by rw [ringChar.eq K 2]; decide)
  have hd := cyclic_five_dimension ρ (z : G) hzpow g hg ε hε
  have hdiv := central_eigenspace_dvd (ρ.comp P.subtype) hc z hz ε (hε.ne_one (by decide))
  obtain ⟨a, ha⟩ := hdiv
  change Module.finrank K (Module.End.eigenspace (ρ (z : G)) ε) = 5 * a at ha
  have hinv : Representation.invariants (ρ.comp ((center P).map P.subtype).subtype) =
      Module.End.eigenspace (ρ (z : G)) 1 := by
    ext v
    rw [Module.End.mem_eigenspace_iff, one_smul]
    constructor
    · intro hv
      exact hv ⟨z, ⟨z, hz, rfl⟩⟩
    · intro hv t
      obtain ⟨w, hw, he⟩ := t.property
      have hf : v ∈ Representation.invariants
          ((ρ.comp P.subtype).comp (center P).subtype) := by
        apply (Representation.mem_invariants_iff_of_forall_mem_zpowers
          _ (⟨z, hz⟩ : center P) (fun _ => mem_zpowers_of_prime_card
            (IsExtraspecial.center_order_p 5 P) (by exact fun h => hz1 (congrArg Subtype.val h))) v).mpr
        exact hv
      change ρ (t : G) v = v
      rw [← he]
      exact hf ⟨w, hw⟩
  refine ⟨a, ?_, ?_⟩
  · by_contra hapos
    have ha0 : a = 0 := by omega
    rw [ha, ha0, mul_zero, mul_zero, add_zero] at hd
    have htop := Submodule.eq_top_of_finrank_eq hd.symm
    apply hne
    ext v
    change ρ (z : G) v = v
    have hv : v ∈ Module.End.eigenspace (ρ (z : G)) 1 := htop ▸ Submodule.mem_top
    simpa only [one_smul] using Module.End.mem_eigenspace_iff.mp hv
  · rw [hinv, hd, ha]
    omega

/-- The positive multiple-of-twenty formula descends to the original field.
The invariant subgroup is the literal image of the extraspecial center. -/
public theorem multiplicity
    {K G V : Type*} [Field K] [CharP K 2] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (P : Subgroup G) [Finite P] [IsExtraspecial 5 P]
    (hc : Nat.card P = 5 ^ 3) (z : P) (hz : z ∈ center P) (hz1 : z ≠ 1)
    (hne : ρ (z : G) ≠ 1) (g : G) (hg : g * (z : G) * g⁻¹ = (z : G) ^ 2) :
    ∃ a : ℕ, 0 < a ∧ Module.finrank K V =
      Module.finrank K (Representation.invariants
        (ρ.comp ((center P).map P.subtype).subtype)) + 20 * a := by
  let E := AlgebraicClosure K
  let eZ := (center P).equivMapOfInjective P.subtype P.subtype_injective
  let : Finite ((center P).map P.subtype) := Finite.of_surjective eZ eZ.surjective
  have hne' : ρ.extendScalars E (z : G) ≠ 1 := by
    intro hh
    apply hne
    apply LinearMap.baseChangeHom_injective (R := K) (S := E) (M := V) (N := V)
    change (ρ (z : G)).baseChange E = (1 : Module.End K V).baseChange E
    change (ρ (z : G)).baseChange E = 1 at hh
    simpa only [LinearMap.baseChange_one] using hh
  obtain ⟨a, ha, hd⟩ := multiplicity_algClosed (ρ.extendScalars E) P hc z hz hz1 hne' g hg
  refine ⟨a, ha, ?_⟩
  have hcomp : (ρ.extendScalars E).comp ((center P).map P.subtype).subtype =
      Representation.extendScalars E (ρ.comp ((center P).map P.subtype).subtype) := rfl
  rw [hcomp, finrank_invariants_extendScalars_eq_of_finite, Module.finrank_baseChange] at hd
  exact hd

end Representation.SU3.FiveSmallModules.Degrees.RootEigenline.NonlinearMultiplicity
