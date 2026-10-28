module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RepresentationTheory.Invariants

/-!
# Fixed bases for finite semilinear actions

Let a finite group act faithfully on a field and compatibly on a vector space.
Its invariant vectors span the space: a linear form vanishing on all orbit sums
would give a linear relation among distinct field automorphisms. Extract a basis
from these invariant vectors. In that basis, the invariant space has coordinates
in the fixed field. Artin's fixed-field degree theorem then gives its dimension.

The construction uses no assumed fixed basis and no division by the group order;
the characteristic may divide that order. This is the descent argument underlying
Aschbacher–Smith, H.0.1, printed p.377 of the 1 March 2004 manuscript.
-/

public section

open Module

namespace Representation.FiniteFieldSemilinearDisplacement.Descent
variable {K F G V : Type*} [Field K] [Field F] [Group G] [Fintype G]
  [AddCommGroup V] [Module K V] [Module F V]
  (ρ : Representation K G V) (τ : G →* (F ≃+* F))
  (hτ : Function.Injective τ)
  (hsemi : ∀ (g : G) (a : F) (v : V), ρ g (a • v) = τ g a • ρ g v)

include hτ hsemi

/-- Invariant vectors span a vector space with a faithful finite semilinear action. -/
theorem span_fixed_eq_top : Submodule.span F {v : V | ∀ g, ρ g v = v} = ⊤ := by
  classical
  let W := Submodule.span F {v : V | ∀ g, ρ g v = v}
  by_contra hn
  obtain ⟨φ, hφ, hW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (show W < ⊤ from lt_top_iff_ne_top.mpr hn) inferInstance
  have hsum (a : F) (v : V) : (∑ g : G, ρ g (a • v)) ∈ W := by
    apply Submodule.subset_span
    intro h
    simp only [map_sum, ← Module.End.mul_apply, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => rfl)
  have hi : LinearIndependent F (fun g : G => fun a : F => τ g a) := by
    apply (linearIndependent_monoidHom F F).comp (fun g => (τ g).toMonoidHom)
    intro g h he
    apply hτ
    ext a
    exact DFunLike.congr_fun he a
  apply hφ
  ext v
  have hz : ∑ g : G, φ (ρ g v) • (fun a : F => τ g a) = 0 := by
    ext a
    have hm : φ (∑ g : G, ρ g (a • v)) = 0 := by
      have := Submodule.mem_map_of_mem (hsum a v) (f := φ)
      rwa [hW, Submodule.mem_bot] at this
    simpa only [map_sum, hsemi, map_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mul_comm, Pi.zero_apply] using hm
  have hh := linearIndependent_iff'.mp hi Finset.univ (fun g => φ (ρ g v)) hz 1
    (Finset.mem_univ 1)
  simpa using hh

/-- A fixed basis is constructed from orbit sums and independence of field automorphisms. -/
theorem exists_fixed_basis : ∃ (s : Set V) (b : Basis s F V), ∀ i g, ρ g (b i) = b i := by
  let s : Set V := {v | ∀ g, ρ g v = v}
  have hs : ⊤ ≤ Submodule.span F s := le_of_eq (span_fixed_eq_top ρ τ hτ hsemi).symm
  refine ⟨_, Basis.ofSpan hs, ?_⟩
  intro i g
  exact Basis.extendLe_subset (linearIndependent_empty F V) (Set.empty_subset s) hs
    (Set.mem_range_self i) g
end Representation.FiniteFieldSemilinearDisplacement.Descent

namespace Representation.FiniteFieldSemilinearDisplacement.Descent
variable {K F G V : Type*} [Field K] [Field F] [Algebra K F] [Group G] [Fintype G]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower K F V]
  [FiniteDimensional F V] [FiniteDimensional K F]
  (ρ : Representation K G V) (τ : G →* (F ≃ₐ[K] F))
  (hτ : Function.Injective τ)
  (hsemi : ∀ (g : G) (a : F) (v : V), ρ g (a • v) = τ g a • ρ g v)

include hτ hsemi in
/-- Descent to the fixed field divides the base-field dimension by the group order. -/
theorem card_mul_finrank_invariants :
    Nat.card G * finrank K ρ.invariants = finrank K F * finrank F V := by
  classical
  let τr : G →* (F ≃+* F) :=
    { toFun := fun g => (τ g).toRingEquiv
      map_one' := by ext a; simp
      map_mul' := by intro g h; ext a; simp }
  have hτr : Function.Injective τr := by
    intro g h he
    apply hτ
    ext a
    exact congrArg (fun f : F ≃+* F => f a) he
  obtain ⟨s, b, hb⟩ := exists_fixed_basis ρ τr hτr hsemi
  let : Finite s := Module.Finite.finite_basis b
  let : Fintype s := Fintype.ofFinite s
  let E := IntermediateField.fixedField τ.range
  have hE (a : F) : a ∈ E ↔ ∀ g, τ g a = a := by
    simp only [E, IntermediateField.mem_fixedField_iff, MonoidHom.mem_range, forall_exists_index]
    constructor
    · intro h g
      exact h (τ g) g rfl
    · rintro h _ g rfl
      exact h g
  have hact (g : G) (c : s → F) :
      ρ g (b.equivFun.symm c) = b.equivFun.symm (fun i => τ g (c i)) := by
    simp only [b.equivFun_symm_apply, map_sum, hsemi, hb]
  have hcoord (g : G) (v : V) (i : s) :
      b.equivFun (ρ g v) i = τ g (b.equivFun v i) := by
    have h := congrArg (fun w => b.equivFun w i) (hact g (b.equivFun v))
    simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] using h
  let f : ρ.invariants →ₗ[K] (s → E) :=
    { toFun := fun v i => ⟨b.equivFun v i, (hE _).mpr fun g => by
        rw [← hcoord, v.property g]⟩
      map_add' := fun v w => by ext i; simp
      map_smul' := fun a v => by
        ext i
        exact congrFun (b.equivFun.toLinearMap.restrictScalars K |>.map_smul a (v : V)) i }
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      apply Subtype.ext
      apply b.equivFun.injective
      ext i
      exact congrArg Subtype.val (congrFun h i)
    · intro c
      refine ⟨⟨b.equivFun.symm (fun i => (c i : F)), ?_⟩, ?_⟩
      · intro g
        rw [hact]
        congr 1
        funext i
        exact (hE _).mp (c i).property g
      · ext i
        exact congrFun (b.equivFun.apply_symm_apply (fun i => (c i : F))) i
  have hdim : finrank K ρ.invariants = Fintype.card s * finrank K E := by
    rw [(LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_pi_fintype]
    simp
  have hdeg : finrank E F = Nat.card G := by
    rw [IntermediateField.finrank_fixedField_eq_card]
    exact Nat.card_congr (Equiv.ofBijective τ.rangeRestrict
      ⟨fun _ _ h => hτ (congrArg Subtype.val h), MonoidHom.rangeRestrict_surjective τ⟩).symm
  have htower := Module.finrank_mul_finrank K E F
  rw [hdeg] at htower
  rw [hdim, Module.finrank_eq_card_basis b, ← htower]
  ac_rfl
end Representation.FiniteFieldSemilinearDisplacement.Descent
