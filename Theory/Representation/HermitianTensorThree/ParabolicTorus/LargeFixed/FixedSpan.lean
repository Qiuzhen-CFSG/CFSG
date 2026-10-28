module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Algebra.Algebra.ZMod

/-!
# A fixed-space bound without faithful coefficient action

For a semilinear actor, take the coefficient-field span of its fixed vectors
and extract a basis from those vectors. The coordinates of every fixed vector
lie in the fixed field of the coefficient automorphism. Artin's fixed-field
degree theorem therefore bounds the fixed binary dimension by the ambient
binary dimension divided by the coefficient order. The actor itself may have
larger order. We also prove coefficient-order divisibility and divisibility
of the fixed binary dimension for field-linear actors.

These general lemmas are applied to the literal Hermitian tensor action in
`ParabolicTorus.LargeFixed`, extending the prime-order estimate of
Aschbacher–Smith H.0.1, printed p.377 of the 1 March 2004 manuscript, to the
composite odd actors needed in 8.2.3, printed pp.715–716.
-/

public section
noncomputable section
open Module
namespace Representation.FiniteFieldSemilinearDisplacement
open BinaryOffender
variable {F G V : Type*} [Field F] [Algebra (ZMod 2) F] [Group G]
  [AddCommGroup V] [Module F V] [Module (ZMod 2) V]
  [FiniteDimensional F V] [FiniteDimensional (ZMod 2) F]

/-- The coefficient order bounds fixed dimension even when the cyclic actor has
larger order and acts nonfaithfully on the coefficient field. -/
theorem fixedSpace_order_bound (ρ : Representation (ZMod 2) G V) (x : G)
    (σ : F ≃ₐ[ZMod 2] F)
    (hsemi : ∀ (a : F) (v : V), ρ x (a • v) = σ a • ρ x v) :
    orderOf σ * finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers x)) ≤
      finrank (ZMod 2) F * finrank F V := by
  classical
  let U := fixedSpace ρ (Subgroup.zpowers x)
  let W := Submodule.span F (U : Set V)
  let S : Set W := {v | (v : V) ∈ U}
  have hspan : Submodule.span F S = ⊤ := by
    apply (Submodule.span_val_image_eq_iff W S).mp
    have himage : Subtype.val '' S = (U : Set V) := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩; exact hw
      · intro hv; exact ⟨⟨v, Submodule.subset_span hv⟩, hv, rfl⟩
    rw [himage]
  obtain ⟨I, b, hb⟩ : ∃ (I : Type _) (b : Basis I F W),
      ∀ i, ρ x (b i : V) = (b i : V) := by
    refine ⟨_, Basis.ofSpan (le_of_eq hspan.symm), ?_⟩
    intro i
    apply (mem_fixedSpace_zpowers_iff ρ x _).mp
    exact Basis.ofSpan_subset (le_of_eq hspan.symm) (Set.mem_range_self i)
  let : Finite I := Module.Finite.finite_basis b
  let : Fintype I := Fintype.ofFinite I
  let E := IntermediateField.fixedField (Subgroup.zpowers σ)
  have hE (a : F) : a ∈ E ↔ σ a = a := by
    simp only [E, IntermediateField.mem_fixedField_iff]
    constructor
    · intro h; exact h σ (Subgroup.mem_zpowers σ)
    · intro h τ hτ
      obtain ⟨k, rfl⟩ := hτ
      exact MulAction.mem_fixedBy_zpow (show a ∈ MulAction.fixedBy F σ from h) k
  let j : U →ₗ[ZMod 2] W :=
    { toFun := fun v => ⟨v, Submodule.subset_span v.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hact (c : I → F) :
      ρ x (b.equivFun.symm c : V) =
        (b.equivFun.symm (fun i => σ (c i)) : V) := by
    simp only [b.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul,
      map_sum, hsemi, hb]
  have hcoord (v : U) (i : I) : σ (b.equivFun (j v) i) = b.equivFun (j v) i := by
    have he := hact (b.equivFun (j v))
    rw [LinearEquiv.symm_apply_apply] at he
    have hv : ρ x (j v : V) = (j v : V) :=
      (mem_fixedSpace_zpowers_iff ρ x v).mp v.property
    rw [hv] at he
    have hh := congrArg (fun w : W => b.equivFun w i) (Subtype.ext he)
    simpa only [LinearEquiv.apply_symm_apply] using hh.symm
  let f : U →ₗ[ZMod 2] (I → E) :=
    { toFun := fun v i => ⟨b.equivFun (j v) i, (hE _).mpr (hcoord v i)⟩
      map_add' := fun v w => by ext i; simp
      map_smul' := fun a v => by
        ext i
        exact congrFun ((b.equivFun.toLinearMap.restrictScalars (ZMod 2)).comp j |>.map_smul a v) i }
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    have he : b.equivFun (j v) = b.equivFun (j w) := by
      ext i
      exact congrArg Subtype.val (congrFun h i)
    exact congrArg (fun z : W => (z : V)) (b.equivFun.injective he)
  have hdim : finrank (ZMod 2) U ≤ Fintype.card I * finrank (ZMod 2) E := by
    have hh := LinearMap.finrank_le_finrank_of_injective hf
    simpa only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
      smul_eq_mul] using hh
  have hdeg : finrank E F = orderOf σ := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
  have htower := Module.finrank_mul_finrank (ZMod 2) E F
  rw [hdeg] at htower
  calc
    orderOf σ * finrank (ZMod 2) U ≤
        orderOf σ * (Fintype.card I * finrank (ZMod 2) E) := Nat.mul_le_mul_left _ hdim
    _ = finrank (ZMod 2) F * finrank F W := by
      rw [Module.finrank_eq_card_basis b, ← htower]
      ac_rfl
    _ ≤ finrank (ZMod 2) F * finrank F V := Nat.mul_le_mul_left _ W.finrank_le

omit [FiniteDimensional F V] [FiniteDimensional (ZMod 2) F] in
/-- On a nonzero module, the coefficient automorphism's order divides the actor's. -/
theorem coefficient_order_dvd [Nontrivial V]
    (ρ : Representation (ZMod 2) G V) (x : G) (σ : F ≃ₐ[ZMod 2] F)
    (hsemi : ∀ (a : F) (v : V), ρ x (a • v) = σ a • ρ x v) :
    orderOf σ ∣ orderOf x := by
  have hp (k : ℕ) (a : F) (v : V) :
      ρ (x ^ k) (a • v) = (σ ^ k) a • ρ (x ^ k) v := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [pow_succ', map_mul, Module.End.mul_apply, AlgEquiv.mul_apply]
      rw [ih, hsemi]
  apply orderOf_dvd_of_pow_eq_one
  ext a
  apply eq_of_smul_eq_smul (α := V)
  intro v
  simpa only [pow_orderOf_eq_one, map_one, Module.End.one_apply, AlgEquiv.one_apply] using
    (hp (orderOf x) a v).symm

omit [FiniteDimensional F V] [FiniteDimensional (ZMod 2) F] in
/-- The fixed binary dimension of a field-linear actor is divisible by the field degree. -/
theorem field_degree_dvd_fixedSpace
    (ρ : Representation (ZMod 2) G V) (x : G)
    (hlinear : ∀ (a : F) (v : V), ρ x (a • v) = a • ρ x v) :
    finrank (ZMod 2) F ∣ finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers x)) := by
  let f : V →ₗ[F] V :=
    { toFun := ρ x
      map_add' := (ρ x).map_add
      map_smul' := hlinear }
  let W := (f - LinearMap.id).ker
  have he : fixedSpace ρ (Subgroup.zpowers x) = W.restrictScalars (ZMod 2) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    change ρ x v = v ↔ ρ x v - v = 0
    exact sub_eq_zero.symm
  rw [he]
  exact ⟨finrank F W, (Module.finrank_mul_finrank (ZMod 2) F W).symm⟩
end Representation.FiniteFieldSemilinearDisplacement
