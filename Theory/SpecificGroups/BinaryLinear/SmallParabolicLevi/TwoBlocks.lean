module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.FieldTheory.Finiteness
public import Theory.GroupTheory.PCoreSurjective

/-!
# The two diagonal blocks of a binary subspace stabilizer

Restriction to W and the induced action on V/W give a surjection from the
actual stabilizer onto GL(W) × GL(V/W). A linear section of the quotient
lifts the two automorphisms simultaneously. The kernel is the subgroup
fixing W pointwise with displacement in W, hence the binary radical.

In finite dimension every binary general linear group has trivial two-core:
a normal two-subgroup has a nonzero fixed vector, and transitivity carries
it to every nonzero vector. Thus the block-action kernel is exactly the
intrinsic two-core, giving a quotient equivalence with both factors marked.
The transitivity argument extends the four-dimensional proof in
Theory.LinearAlgebra.BinaryFivePointStabilizer.GeneralLinearCore.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.25, printed pp.959–960 (PDF pp.976–977), for blocks of sizes 2+3,
3+2, 1+3 and 3+1. This module does not assert the marked residual calculations.
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.SmallParabolicLevi
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem mkQ_eq_zero (W : Submodule (ZMod 2) V) {x : V} :
    W.mkQ x = 0 ↔ x ∈ W := Submodule.Quotient.mk_eq_zero W

/-- Restriction of an actual subspace stabilizer to the subspace. -/
def subspaceAction (W : Submodule (ZMod 2) V) : parabolic W →* GL W where
  toFun g :=
    { toFun w := ⟨g.val w, (g.property w).mpr w.property⟩
      invFun w := ⟨g.val.symm w, ((parabolic W).inv_mem g.property w).mpr w.property⟩
      map_add' _ _ := Subtype.ext (map_add _ _ _)
      map_smul' _ _ := Subtype.ext (map_smul _ _ _)
      left_inv _ := Subtype.ext (g.val.symm_apply_apply _)
      right_inv _ := Subtype.ext (g.val.apply_symm_apply _) }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- A stabilizer element maps the marked subspace onto itself. -/
theorem map_subspace (W : Submodule (ZMod 2) V) (g : parabolic W) :
    W.map g.val.toLinearMap = W := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact (g.property w).mpr hw
  · intro w hw
    refine ⟨g.val.symm w, ?_, g.val.apply_symm_apply w⟩
    exact ((parabolic W).inv_mem g.property w).mpr hw

/-- The quotient action uses the same ambient automorphism as the restriction. -/
def quotientAction (W : Submodule (ZMod 2) V) : parabolic W →* GL (V ⧸ W) where
  toFun g := Submodule.Quotient.equiv W W g.val (map_subspace W g)
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_mul' _ _ := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

@[simp] theorem subspaceAction_apply (W : Submodule (ZMod 2) V)
    (g : parabolic W) (w : W) : (subspaceAction W g w : V) = g.val w := rfl

@[simp] theorem quotientAction_mk (W : Submodule (ZMod 2) V)
    (g : parabolic W) (v : V) : quotientAction W g (W.mkQ v) = W.mkQ (g.val v) := rfl

/-- The two diagonal blocks, with their geometric markings retained. -/
def blockAction (W : Submodule (ZMod 2) V) : parabolic W →* GL W × GL (V ⧸ W) :=
  (subspaceAction W).prod (quotientAction W)

/-- The kernel is exactly the actual radical, regarded inside the parabolic. -/
theorem ker_blockAction (W : Submodule (ZMod 2) V) :
    (blockAction W).ker = (radical W).subgroupOf (parabolic W) := by
  ext g
  rw [MonoidHom.mem_ker]
  change (subspaceAction W g, quotientAction W g) = (1, 1) ↔
    (∀ w ∈ W, g.val w = w) ∧ ∀ v, g.val v - v ∈ W
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨hs, hq⟩
    constructor
    · intro w hw
      exact congrArg Subtype.val (LinearEquiv.congr_fun hs ⟨w, hw⟩)
    · intro v
      exact (Submodule.Quotient.eq W).mp (LinearEquiv.congr_fun hq (W.mkQ v))
  · rintro ⟨hs, hq⟩
    constructor
    · ext w
      exact hs w w.property
    · ext x
      induction x using Submodule.Quotient.induction_on with
      | _ v => exact (Submodule.Quotient.eq W).mpr (hq v)

private def splitProjection (W : Submodule (ZMod 2) V) (s : (V ⧸ W) →ₗ[ZMod 2] V)
    (hs : ∀ x, W.mkQ (s x) = x) : V →ₗ[ZMod 2] W :=
  (LinearMap.id - s.comp W.mkQ).codRestrict W (by
    intro x
    apply (mkQ_eq_zero W).mp
    change W.mkQ (x - s (W.mkQ x)) = 0
    rw [map_sub, hs, sub_self])

private theorem splitProjection_subtype (W : Submodule (ZMod 2) V)
    (s : (V ⧸ W) →ₗ[ZMod 2] V) (hs : ∀ x, W.mkQ (s x) = x) (w : W) :
    splitProjection W s hs w = w := by
  apply Subtype.ext
  change (w : V) - s (W.mkQ w) = w
  rw [(mkQ_eq_zero W).mpr w.property, map_zero, sub_zero]

private theorem splitProjection_section (W : Submodule (ZMod 2) V)
    (s : (V ⧸ W) →ₗ[ZMod 2] V) (hs : ∀ x, W.mkQ (s x) = x) (x : V ⧸ W) :
    splitProjection W s hs (s x) = 0 := by
  apply Subtype.ext
  change s x - s (W.mkQ (s x)) = 0
  rw [hs, sub_self]

private def splitEquiv (W : Submodule (ZMod 2) V)
    (s : (V ⧸ W) →ₗ[ZMod 2] V) (hs : ∀ x, W.mkQ (s x) = x) :
    (W × (V ⧸ W)) ≃ₗ[ZMod 2] V where
  __ := W.subtype.coprod s
  invFun x := (splitProjection W s hs x, W.mkQ x)
  left_inv x := by
    apply Prod.ext
    · change splitProjection W s hs ((x.1 : V) + s x.2) = x.1
      rw [map_add, splitProjection_subtype, splitProjection_section, add_zero]
    · change W.mkQ ((x.1 : V) + s x.2) = x.2
      rw [map_add, (mkQ_eq_zero W).mpr x.1.property, hs, zero_add]
  right_inv x := by
    change (x - s (W.mkQ x)) + s (W.mkQ x) = x
    exact sub_add_cancel _ _

/-- Both block automorphisms lift simultaneously, by a linear section of `V → V/W`. -/
theorem blockAction_surjective (W : Submodule (ZMod 2) V) :
    Function.Surjective (blockAction W) := by
  obtain ⟨s, hs⟩ := W.mkQ.exists_rightInverse_of_surjective W.range_mkQ
  have hs' (x : V ⧸ W) : W.mkQ (s x) = x := LinearMap.congr_fun hs x
  let e := splitEquiv W s hs'
  rintro ⟨a, b⟩
  let g := (e.symm.trans (a.prodCongr b)).trans e
  have hq (x : V) : W.mkQ (g x) = b (W.mkQ x) := by
    change W.mkQ ((a (splitProjection W s hs' x) : V) + s (b (W.mkQ x))) = _
    rw [map_add, (mkQ_eq_zero W).mpr (a _).property, hs', zero_add]
  have hg : g ∈ parabolic W := by
    intro x
    rw [← mkQ_eq_zero W, hq, b.map_eq_zero_iff,
      mkQ_eq_zero]
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Prod.ext
  · ext w
    change (a (splitProjection W s hs' (w : V)) : V) + s (b (W.mkQ w)) = (a w : V)
    rw [splitProjection_subtype, (mkQ_eq_zero W).mpr w.property,
      map_zero, map_zero, add_zero]
  · ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact hq x



private theorem transitive_nonzero (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : GL V, g x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V y hy
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨g, ?_⟩
  have h := hg (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h.symm

/-- The binary general linear group has trivial two-core in every finite dimension. -/
theorem linearGroup_twoCore_eq_bot [FiniteDimensional (ZMod 2) V] :
    pCore 2 (GL V) = ⊥ := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  by_cases hdim : Module.finrank (ZMod 2) V = 0
  · have : Subsingleton V := (Module.finrank_eq_zero_iff_of_free (ZMod 2) V).mp hdim
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g _
    ext x
    exact Subsingleton.elim _ _
  let N := pCore 2 (GL V)
  have hcard : 2 ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self _ hdim
  have hzero : (0 : V) ∈ MulAction.fixedPoints N V := by
    intro g
    exact map_zero g.val
  have hN : IsPGroup 2 N := pCore_isPGroup
  obtain ⟨v, hv, hv0⟩ :=
    hN.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hcard hzero
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro n hn
  ext w
  change n w = w
  by_cases hw : w = 0
  · rw [hw, map_zero]
  obtain ⟨g, hg⟩ := transitive_nonzero v w (Ne.symm hv0) hw
  have hconj : g⁻¹ * n * g ∈ N :=
    (inferInstance : N.Normal).conj_mem' n hn g
  have hfix := hv ⟨g⁻¹ * n * g, hconj⟩
  change g.symm (n (g v)) = v at hfix
  have heq := congrArg g hfix
  simpa only [LinearEquiv.apply_symm_apply, hg] using heq

private theorem prod_twoCore_eq_bot {A B : Type*} [Group A] [Group B]
    (hA : pCore 2 A = ⊥) (hB : pCore 2 B = ⊥) : pCore 2 (A × B) = ⊥ := by
  have hfst : (pCore 2 (A × B)).map (MonoidHom.fst A B) ≤ pCore 2 A :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _ (fun a => ⟨(a, 1), rfl⟩),
      pCore_isPGroup.map _⟩
  have hsnd : (pCore 2 (A × B)).map (MonoidHom.snd A B) ≤ pCore 2 B :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _ (fun b => ⟨(1, b), rfl⟩),
      pCore_isPGroup.map _⟩
  rw [hA] at hfst
  rw [hB] at hsnd
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  exact Prod.ext (hfst (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩))
    (hsnd (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩))

/-- The two diagonal actions have exactly the intrinsic two-core as kernel. -/
theorem ker_blockAction_eq_twoCore [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) : (blockAction W).ker = pCore 2 (parabolic W) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (GL V) := Finite.of_injective
    (fun g : GL V => (g : V → V)) DFunLike.coe_injective
  let : Finite (V ⧸ W) := Module.finite_of_finite (ZMod 2)
  let : Finite (GL W) := Finite.of_injective
    (fun g : GL W => (g : W → W)) DFunLike.coe_injective
  let : Finite (GL (V ⧸ W)) := Finite.of_injective
    (fun g : GL (V ⧸ W) => (g : (V ⧸ W) → (V ⧸ W))) DFunLike.coe_injective
  have hk : IsPGroup 2 (blockAction W).ker := by
    rw [ker_blockAction]
    exact (radical_two W).comap_subtype
  have h := (blockAction W).comap_pCore_of_ker_isPGroup (blockAction_surjective W) hk
  rw [prod_twoCore_eq_bot linearGroup_twoCore_eq_bot linearGroup_twoCore_eq_bot] at h
  exact h

/-- The actual parabolic modulo its two-core, with both geometric factors marked. -/
noncomputable def quotientTwoCoreEquiv [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) :
    (parabolic W ⧸ pCore 2 (parabolic W)) ≃* GL W × GL (V ⧸ W) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_blockAction_eq_twoCore W).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (blockAction W) (blockAction_surjective W))

@[simp] theorem quotientTwoCoreEquiv_mk [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (g : parabolic W) :
    quotientTwoCoreEquiv W (QuotientGroup.mk' _ g) = blockAction W g := rfl

/-- The two-core inside the parabolic is precisely the restricted radical. -/
theorem twoCore_eq_radical [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) :
    pCore 2 (parabolic W) = (radical W).subgroupOf (parabolic W) :=
  (ker_blockAction_eq_twoCore W).symm.trans (ker_blockAction W)

/-- Mapping the intrinsic two-core back gives the literal ambient radical. -/
theorem map_twoCore_eq_radical [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) :
    (pCore 2 (parabolic W)).map (parabolic W).subtype = radical W := by
  rw [twoCore_eq_radical, Subgroup.map_subgroupOf_eq_of_le (radical_le_parabolic W)]

/-- The first quotient factor is the restriction to the marked subspace. -/
theorem quotientTwoCoreEquiv_fst_apply [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (g : parabolic W) (w : W) :
    ((quotientTwoCoreEquiv W (QuotientGroup.mk' _ g)).1 w : V) = g.val w := rfl

/-- The second quotient factor is the action on the marked quotient space. -/
theorem quotientTwoCoreEquiv_snd_mk_apply [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (g : parabolic W) (v : V) :
    (quotientTwoCoreEquiv W (QuotientGroup.mk' _ g)).2 (W.mkQ v) = W.mkQ (g.val v) := rfl

end BinaryLinear.SmallParabolicLevi

end
