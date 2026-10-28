module

public import Theory.Representation.AbelianWeightAutomizer
public import Theory.Representation.ExtendScalars
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.FixedPointFree
public import Theory.Representation.PermutationBasisOrbits
public import Theory.Representation.InvariantsBaseChange
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Displacement bounds from abelian Frobenius kernels

A faithful cross-characteristic representation has a nontrivial weight for a
nontrivial finite abelian kernel. If a complement acts freely on that kernel,
its orbit on this weight is free. Choose one nonzero weight vector: its
complement translates are independent and span a regular complement module.

An element of prime order `p` permutes this basis in orbits of length `p`.
Thus a complement of order `n` supplies at least `n - n / p` displacement
dimensions and at least `n / p` fixed dimensions. The complement need not
have order invertible in the coefficient field. Extending scalars and then
descending fixed dimensions proves the same bounds over an arbitrary field.

For the Borel 5²:12 of PSL₂(25), these are the displacement bound eight and
the degree-twelve fixed-space calculation in Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 4.1, manuscript p.9,
used by Aschbacher--Smith K.2, printed p.453. The concrete source application
is in `TwentyFive/ThreeDisplacement.lean`.
-/

public section

open scoped IsMulCommutative
namespace Representation

private theorem character_eq_one_of_fixedPointFree {K A : Type*}
    [Group K] [Finite K] [Group A]
    (a : MulAut K) (hfixed : MonoidHom.FixedPointFree a)
    (chi : K →* A) (hchi : ∀ k, chi (a k) = chi k) : chi = 1 := by
  ext k
  obtain ⟨x, rfl⟩ := hfixed.commutatorMap_surjective k
  change chi (x / a x) = 1
  rw [map_div, hchi, div_self']

variable {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]

/-- One vector in a nontrivial weight space has linearly independent
translates under a complement acting freely on the abelian kernel. -/
theorem exists_linearIndependent_normalizer_orbit [IsAlgClosed E]
    [FiniteDimensional E V] (rho : Representation E G V)
    (K C : Subgroup G) [Finite K] [Nontrivial K] [IsMulCommutative K]
    (hrho : Function.Injective rho) (horder : (Nat.card K : E) ≠ 0)
    (hnorm : C ≤ (Subgroup.normalizer (K : Set G)))
    (hfree : ∀ c : C, c ≠ 1 → ∀ k : K,
      (c : G) * k * (c : G)⁻¹ = k → k = 1) :
    ∃ v : V, LinearIndependent E (fun c : C => rho c v) := by
  classical
  let n : C →* (Subgroup.normalizer (K : Set G)) := Subgroup.inclusion hnorm
  let a : C →* MulAut K := K.normalizerMonoidHom.comp n
  let p : C →* Equiv.Perm (CharacterWeight (rho.comp K.subtype)) :=
    (automizerWeightPerm rho K).comp (K.normalizerMonoidHom.rangeRestrict.comp n)
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  have hchi : ∃ chi : CharacterWeight (rho.comp K.subtype), chi.val ≠ 1 := by
    by_contra! h
    apply hk
    apply eq_of_characterWeight_values (rho.comp K.subtype)
      (hrho.comp Subtype.val_injective) horder
    intro chi
    simp [h chi]
  obtain ⟨chi, hchi⟩ := hchi
  have hp (c : C) : (p c chi).val = chi.val.comp (a c).symm.toMonoidHom := rfl
  have hstab (c : C) (hc : p c chi = chi) : c = 1 := by
    by_contra hne
    apply hchi
    apply character_eq_one_of_fixedPointFree (a c).symm
    · intro x hx
      apply hfree c hne x
      have hx' : a c x = x := by
        exact (congrArg (a c) hx).symm.trans ((a c).apply_symm_apply x)
      exact congrArg Subtype.val hx'
    · intro x
      exact DFunLike.congr_fun ((hp c).symm.trans (congrArg Subtype.val hc)) x
  have hinj : Function.Injective (fun c : C => p c chi) := by
    intro c d h
    change p c chi = p d chi at h
    have hcd : p (d⁻¹ * c) chi = chi := by
      rw [map_mul, map_inv]
      change (p d).symm (p c chi) = chi
      rw [h]
      exact (p d).symm_apply_apply chi
    exact (inv_mul_eq_one.mp (hstab _ hcd)).symm
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot chi.property
  refine ⟨v, ?_⟩
  have hi : Function.Injective (fun c : C => (p c chi).val) :=
    Subtype.val_injective.comp hinj
  apply iSupIndep.linearIndependent
    (fun c : C => characterWeightSpace (rho.comp K.subtype) (p c chi).val)
    ((characterWeightSpace_independent (rho.comp K.subtype) horder).comp hi)
  · intro c
    simp only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hv ⊢
    intro k
    have hc : (k : G) * c = c * ((a c).symm k : K) := by
      have he := congrArg (fun z : K => (z : G)) ((a c).apply_symm_apply k)
      change (c : G) * ((a c).symm k : K) * (c : G)⁻¹ = k at he
      rw [← he]
      group
    change rho (k : G) (rho c v) = (chi.val ((a c).symm k) : E) • rho c v
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    rw [show rho (((a c).symm k : K) : G) v =
      (chi.val ((a c).symm k) : E) • v from hv ((a c).symm k)]
    exact map_smul _ _ _
  · intro c hz
    apply hv0
    have he := congrArg (rho (c : G)⁻¹) hz
    simpa only [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using he

end Representation

namespace Representation
variable {E C V : Type*} [Field E] [Group C] [Finite C]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- A regular orbit of independent vectors gives both displacement and fixed-space bounds. -/
theorem prime_bounds_of_linearIndependent_orbit (rho : Representation E C V)
    (v : V) (hv : LinearIndependent E (fun c => rho c v))
    (c : C) {p : ℕ} (hp : p.Prime) (hc : orderOf c = p) :
    Nat.card C - Nat.card C / p ≤ Module.finrank E (LinearMap.range (rho c - 1)) ∧
      Nat.card C / p ≤ Module.finrank E (LinearMap.ker (rho c - 1)) := by
  classical
  let W : Submodule E V := Submodule.span E (Set.range fun d : C => rho d v)
  have hW : ∀ d : C, W ≤ W.comap (rho d) := by
    intro d
    apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    change rho d (rho e v) ∈ W
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span ⟨d * e, rfl⟩
  let sigma := rho.subrepresentation W hW
  let b : Module.Basis C E W := Module.Basis.span hv
  let T : W ≃ₗ[E] W :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv E W) (sigma.asGroupHom c)
  let perm : Equiv.Perm C := Equiv.mulLeft c
  have hbval (d : C) : (b d : V) = rho d v := Module.Basis.coe_span_apply hv d
  have hb (d : C) : T (b d) = b (perm d) := by
    apply Subtype.ext
    change rho c ((b d : W) : V) = (b (c * d) : V)
    rw [hbval, hbval, ← Module.End.mul_apply, ← map_mul]
  have hn : Module.finrank E W = Nat.card C := Module.finrank_eq_nat_card_basis b
  have hfix : Module.finrank E T.fixedSubmodule = Nat.card C / p := by
    rw [equivariantBasis_fixedSubmodule_finrank_eq_orbitQuotient_card b T perm hb]
    have hpow : perm ^ p = 1 := by
      change (MulAction.toPermHom C C c) ^ p = 1
      rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
    let : IsEmpty (Function.fixedPoints perm) := ⟨by
      rintro ⟨d, hd⟩
      change c * d = d at hd
      have hc1 : c = 1 := mul_right_cancel (hd.trans (one_mul d).symm)
      have he : 1 = p := by simpa only [hc1, orderOf_one] using hc
      exact hp.ne_one he.symm⟩
    have hcount := primePow_perm_fixedPoints_orbit_formula hp perm hpow
    have he : Nat.card C = Nat.card
        (MulAction.orbitRel.Quotient (Subgroup.zpowers perm) C) * p := by
      simpa using hcount
    rw [he, Nat.mul_div_cancel _ hp.pos]
  have hk : LinearMap.ker (sigma c - 1) = T.fixedSubmodule := by
    ext w
    change sigma c w - w = 0 ↔ T w = w
    exact sub_eq_zero
  have hf : Module.finrank E (LinearMap.ker (sigma c - 1)) = Nat.card C / p := by
    rw [hk, hfix]
  have hr : Module.finrank E (LinearMap.range (sigma c - 1)) =
      Nat.card C - Nat.card C / p := by
    have he := (sigma c - 1).finrank_range_add_finrank_ker
    rw [hn, hf] at he
    omega
  constructor
  · rw [← hr]
    let f : LinearMap.range (sigma c - 1) →ₗ[E] LinearMap.range (rho c - 1) :=
      { toFun := fun w => ⟨w.val.val, by
          obtain ⟨z, hz⟩ := w.property
          exact ⟨z.val, congrArg Subtype.val hz⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact LinearMap.finrank_le_finrank_of_injective (f := f) (by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun w => w.val) h)))
  · rw [← hf]
    let f : LinearMap.ker (sigma c - 1) →ₗ[E] LinearMap.ker (rho c - 1) :=
      { toFun := fun w => ⟨w.val.val, congrArg Subtype.val w.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact LinearMap.finrank_le_finrank_of_injective (f := f) (by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun w => w.val) h)))
end Representation

namespace Representation
variable {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]

/-- The displacement kernel is the invariant space of the cyclic subgroup. -/
theorem ker_sub_one_eq_cyclic_invariants (rho : Representation E G V) (g : G) :
    LinearMap.ker (rho g - 1) = invariants (rho.comp (Subgroup.zpowers g).subtype) := by
  ext v
  rw [Representation.mem_invariants_iff_of_forall_mem_zpowers
    (rho.comp (Subgroup.zpowers g).subtype) ⟨g, Subgroup.mem_zpowers g⟩ (by
      intro x
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.property
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩)]
  exact sub_eq_zero

variable [FiniteDimensional E V]

/-- Scalar extension preserves the fixed dimension of a finite-order actor. -/
theorem finrank_ker_sub_one_extendScalars (L : Type*) [Field L] [Algebra E L]
    (rho : Representation E G V) (g : G) [Finite (Subgroup.zpowers g)] :
    Module.finrank L (LinearMap.ker (rho.extendScalars L g - 1)) =
      Module.finrank E (LinearMap.ker (rho g - 1)) := by
  rw [ker_sub_one_eq_cyclic_invariants, ker_sub_one_eq_cyclic_invariants]
  change Module.finrank L (invariants (extendScalars L (rho.comp (Subgroup.zpowers g).subtype))) = _
  exact finrank_invariants_extendScalars_eq_of_finite _

/-- A Frobenius complement of order `n` supplies at least `n - n / p`
displacement dimensions and `n / p` fixed dimensions for each prime-order actor.
Only the abelian kernel needs to have order invertible in the coefficient field. -/
theorem prime_displacement_bounds_of_fixedPointFree_normalizer
    (rho : Representation E G V) (K C : Subgroup G)
    [Finite K] [Nontrivial K] [IsMulCommutative K] [Finite C]
    (hrho : Function.Injective rho) (horder : (Nat.card K : E) ≠ 0)
    (hnorm : C ≤ Subgroup.normalizer (K : Set G))
    (hfree : ∀ c : C, c ≠ 1 → ∀ k : K,
      (c : G) * k * (c : G)⁻¹ = k → k = 1)
    (c : C) {p : ℕ} (hp : p.Prime) (hc : orderOf c = p) :
    Nat.card C - Nat.card C / p ≤ Module.finrank E (LinearMap.range (rho c - 1)) ∧
      Nat.card C / p ≤ Module.finrank E (LinearMap.ker (rho c - 1)) := by
  let L := AlgebraicClosure E
  have horder' : (Nat.card K : L) ≠ 0 := by
    intro h
    apply horder
    apply (algebraMap E L).injective
    simpa using h
  obtain ⟨v, hv⟩ := exists_linearIndependent_normalizer_orbit (rho.extendScalars L) K C
    ((extendScalars_faithful_iff L rho).mp hrho) horder' hnorm hfree
  let sigma : Representation E C V := rho.comp C.subtype
  have hb := prime_bounds_of_linearIndependent_orbit
    (sigma.extendScalars L) v hv c hp hc
  have he := finrank_ker_sub_one_extendScalars L sigma c
  have hd : Module.finrank E (LinearMap.range (sigma c - 1)) +
      Module.finrank E (LinearMap.ker (sigma c - 1)) = Module.finrank E V :=
    (sigma c - 1).finrank_range_add_finrank_ker
  have hd' : Module.finrank L (LinearMap.range (sigma.extendScalars L c - 1)) +
      Module.finrank L (LinearMap.ker (sigma.extendScalars L c - 1)) = Module.finrank E V := by
    have he := (sigma.extendScalars L c - 1).finrank_range_add_finrank_ker
    rw [Module.finrank_baseChange] at he
    exact he
  have hr : Module.finrank L (LinearMap.range (sigma.extendScalars L c - 1)) =
      Module.finrank E (LinearMap.range (sigma c - 1)) := by
    apply Nat.add_right_cancel (m := Module.finrank E (LinearMap.ker (sigma c - 1)))
    calc
      _ = Module.finrank L (LinearMap.range (sigma.extendScalars L c - 1)) +
          Module.finrank L (LinearMap.ker (sigma.extendScalars L c - 1)) :=
        congrArg (fun n => Module.finrank L (LinearMap.range (sigma.extendScalars L c - 1)) + n) he.symm
      _ = Module.finrank E V := hd'
      _ = _ := hd.symm
  exact ⟨hb.1.trans_eq hr, hb.2.trans_eq he⟩
end Representation
