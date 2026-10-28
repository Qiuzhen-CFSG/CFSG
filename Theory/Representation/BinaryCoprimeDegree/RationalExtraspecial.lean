module

public import Theory.GroupTheory.PGroup.RationalExtraspecial
public import Theory.Representation.ExtraspecialFixedPoints
public import Theory.Representation.ExtendScalars
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The p(p−1) degree bound from a rational extraspecial subgroup

Over an algebraic closure of a characteristic-two field, a faithful simple
constituent of an extraspecial group of order p³ has dimension p. A
nonidentity central element acts by a primitive p-th root. Conjugating that
constituent gives subspaces in the p−1 distinct nontrivial eigenspaces when
the central element is conjugate to each of its nonidentity powers.
Independence of eigenspaces gives dimension at least p(p−1).

Scalar extension preserves faithfulness and dimension, so the result holds
on the original binary space without any absolute-irreducibility premise.
The group configuration, including its passage through central covers, is
specified independently in `Theory.GroupTheory.PGroup.RationalExtraspecial`.

This supplies the representation step in the local root-group route to the
odd PSU₃ bound used by Guralnick–Malle, Classification of 2F-modules I,
Proposition 4.3 (citing Seitz–Zalesskii, J. Algebra 158 (1993), 233–243),
and Aschbacher–Smith K.2, printed p.453.
-/

public section
open scoped DirectSum TensorProduct MonoidAlgebra
open Subgroup
namespace Representation.BinaryCoprimeDegree

private theorem sum_eigenspace_finrank_le
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (f : Module.End F V)
    {ι : Type*} [Fintype ι] (a : ι → F) (ha : Function.Injective a) :
    ∑ i, Module.finrank F (f.eigenspace (a i)) ≤ Module.finrank F V := by
  classical
  let W := fun i => f.eigenspace (a i)
  have hi : iSupIndep W := f.eigenspaces_iSupIndep.comp ha
  have hh := LinearMap.finrank_le_finrank_of_injective
    (f := DirectSum.coeLinearMap W) hi.dfinsupp_lsum_injective
  rwa [Module.finrank_directSum] at hh

private theorem scalar_subspace_le_eigenspace_finrank
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ρ : Representation F G V)
    (W : Submodule F V) {z g : G} {a : F} {i : ℕ}
    (hW : ∀ v : W, ρ z v = a • (v : V))
    (hg : g * z * g⁻¹ = z ^ i) :
    Module.finrank F W ≤ Module.finrank F (Module.End.eigenspace (ρ z) (a ^ i)) := by
  have hpow (j : ℕ) (v : W) : ρ (z ^ j) v = a ^ j • (v : V) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', map_mul]
      change ρ z (ρ (z ^ j) v) = _
      rw [ih, map_smul, hW, smul_smul, pow_succ]
  have hconj : z * g⁻¹ = g⁻¹ * z ^ i := by
    rw [← hg]
    group
  let f : W →ₗ[F] (Module.End.eigenspace (ρ z) (a ^ i)) :=
    ((ρ g⁻¹).comp W.subtype).codRestrict _ (fun v => by
      apply Module.End.mem_eigenspace_iff.mpr
      change ρ z (ρ g⁻¹ (v : V)) = _
      rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul,
        Module.End.mul_apply, hpow, map_smul]
      rfl)
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  intro v w hvw
  apply Subtype.ext
  have hh := congrArg (fun t : (Module.End.eigenspace (ρ z) (a ^ i)) => ρ g (t : V)) hvw
  change ρ g (ρ g⁻¹ (v : V)) = ρ g (ρ g⁻¹ (w : V)) at hh
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hh

/-- Over an algebraically closed characteristic-two field, rational fusion of
one nonidentity central element of an extraspecial subgroup forces p(p-1). -/
theorem rational_extraspecial_finrank_ge_algClosed
    {F G V : Type*} [Field F] [IsAlgClosed F] [CharP F 2] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : Representation F G V) (hρ : Function.Injective ρ)
    (P : Subgroup G) [Finite P] [IsExtraspecial p P]
    (hcard : Nat.card P = p ^ 3)
    (z : P) (hz : z ∈ center P) (hz1 : z ≠ 1)
    (hfusion : ∀ i : ℕ, 0 < i → i < p →
      ∃ g : G, g * (z : G) * g⁻¹ = (z : G) ^ i) :
    p * (p - 1) ≤ Module.finrank F V := by
  classical
  have hp : p.Prime := Fact.out
  have hc : ¬ ringChar F ∣ Nat.card P := by
    rw [ringChar.eq F 2, hcard]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow hd)).symm
  let σ : Representation F P V := ρ.comp P.subtype
  let : IsSemisimpleModule F[P] σ.asModule := by
    apply isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
    right
    rw [ringChar.eq F 2]
    exact ⟨Nat.prime_two, Nat.prime_two.coprime_iff_not_dvd.mpr
      (by simpa only [ringChar.eq F 2] using hc)⟩
  have hcent : ¬ center P ≤ σ.ker := by
    intro hh
    apply hz1
    apply Subtype.ext
    apply hρ
    exact (MonoidHom.mem_ker.mp (hh hz)).trans (map_one ρ).symm
  obtain ⟨m, hm, hmk⟩ := exists_simple_submodule_nontrivial_of_not_le_ker σ (center P) hcent
  let W := (Subrepresentation.ofSubmodule' m).toSubmodule
  let τ := (Subrepresentation.ofSubmodule' m).toRepresentation
  let : IsIrreducible τ := irreducible_of_ofSubmodule'_simple σ hm
  have hτ : Function.Injective τ := (MonoidHom.ker_eq_bot_iff τ).mp
    (ker_eq_bot_of_center_not_le_ker_of_isExtraspecial (q := p) τ hmk)
  have hd : Module.finrank F W = p := by
    simpa only [pow_one] using
      finrank_eq_primePow_of_faithful_irreducible_isExtraspecial
        (q := p) (n := 1) τ hτ hcard hc
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial τ
  obtain ⟨a, ha⟩ := center_apply_eq_smul_id_of_irreducible τ hz
  have hap : a ^ p = 1 := by
    have hzp : z ^ p = 1 := by
      have hh := pow_card_eq_one' (x := (⟨z, hz⟩ : center P))
      rw [IsExtraspecial.center_order_p p P] at hh
      exact congrArg Subtype.val hh
    apply (algebraMap F (Module.End F W)).injective
    simp only [Algebra.algebraMap_eq_smul_one, one_smul]
    calc
      a ^ p • (1 : Module.End F W) = (a • (1 : Module.End F W)) ^ p := by
        simp only [smul_pow, one_pow]
      _ = (1 : Module.End F W) := by rw [← ha, ← map_pow, hzp, map_one]
  have ha1 : a ≠ 1 := by
    intro he
    apply hz1
    apply hτ
    rw [ha, he, one_smul, map_one]
  have haroot : IsPrimitiveRoot a p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hap ha1)
  have hW (v : W) : ρ (z : G) v = a • (v : V) := by
    have hh := LinearMap.congr_fun ha v
    exact congrArg Subtype.val hh
  have hb (i : Fin (p - 1)) :
      p ≤ Module.finrank F (Module.End.eigenspace (ρ (z : G)) (a ^ (i.val + 1))) := by
    obtain ⟨g, hg⟩ := hfusion (i.val + 1) (by omega) (by omega)
    calc
      p = Module.finrank F W := hd.symm
      _ ≤ _ := scalar_subspace_le_eigenspace_finrank ρ W hW hg
  have hi : Function.Injective (fun i : Fin (p - 1) => a ^ (i.val + 1)) := by
    intro i j he
    apply Fin.ext
    have hh := haroot.pow_inj (by omega : i.val + 1 < p)
      (by omega : j.val + 1 < p) he
    omega
  calc
    p * (p - 1) = ∑ _ : Fin (p - 1), p := by simp [Nat.mul_comm]
    _ ≤ ∑ i : Fin (p - 1),
        Module.finrank F (Module.End.eigenspace (ρ (z : G)) (a ^ (i.val + 1))) :=
      Finset.sum_le_sum (fun i _ => hb i)
    _ ≤ Module.finrank F V := sum_eigenspace_finrank_le _ _ hi

/-- Scalar extension preserves the bound over the original coefficient field. -/
theorem rational_extraspecial_finrank_ge
    {F G V : Type*} [Field F] [CharP F 2] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : Representation F G V) (hρ : Function.Injective ρ)
    (P : Subgroup G) [Finite P] [IsExtraspecial p P]
    (hcard : Nat.card P = p ^ 3)
    (z : P) (hz : z ∈ center P) (hz1 : z ≠ 1)
    (hfusion : ∀ i : ℕ, 0 < i → i < p →
      ∃ g : G, g * (z : G) * g⁻¹ = (z : G) ^ i) :
    p * (p - 1) ≤ Module.finrank F V := by
  have hh := rational_extraspecial_finrank_ge_algClosed hp2
    (ρ.extendScalars (AlgebraicClosure F))
    ((extendScalars_faithful_iff (AlgebraicClosure F) ρ).mp hρ)
    P hcard z hz hz1 hfusion
  simpa only [Module.finrank_baseChange] using hh

/-- A rational extraspecial subgroup bounds every faithful characteristic-two
representation, with no irreducibility assumption. -/
theorem finrank_ge_of_rational_extraspecial
    {F G V : Type*} [Field F] [CharP F 2] [Group G] [Finite G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : Representation F G V) (hρ : Function.Injective ρ)
    (h : Theory.GroupTheory.HasRationalExtraspecialSubgroup G p) :
    p * (p - 1) ≤ Module.finrank F V := by
  obtain ⟨P, hP, hcard, z, hz, hz1, hconj⟩ := h
  let : IsExtraspecial p P := hP
  exact rational_extraspecial_finrank_ge hp2 ρ hρ P hcard z hz hz1 hconj

end Representation.BinaryCoprimeDegree
