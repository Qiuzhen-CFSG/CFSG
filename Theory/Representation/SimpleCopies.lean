module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Field.ZMod

/-!
# Odd cardinality of the copies of a simple binary module

The nonzero homomorphisms from a simple module are parametrized by their
image submodule and an isomorphism onto that image. The latter choices form
a torsor under the automorphism group of the simple module. Thus the number
of copies divides the number of nonzero homomorphisms, which is odd over F₂.
Any two-group acting on these actual copies consequently fixes one.

This is the counting step in Aschbacher–Smith, *The Classification of
Quasithin Groups*, Lemma A.1.42, printed p.32. It counts a single prescribed
simple type, rather than all simple types in the orbit span.
-/

@[expose] public section

namespace Representation.SimpleCopies
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
variable {A S V : Type*} [Ring A] [AddCommGroup S] [Module A S]
  [AddCommGroup V] [Module A V] [IsSimpleModule A S]

def Copies (A S V : Type*) [Ring A] [AddCommGroup S] [Module A S]
    [AddCommGroup V] [Module A V] :=
  {U : Submodule A V // Nonempty (S ≃ₗ[A] U)}

private def realize (p : Σ U : Copies A S V, S ≃ₗ[A] U.val) :
    {f : S →ₗ[A] V // f ≠ 0} := by
  let := IsSimpleModule.nontrivial A S
  exact ⟨p.1.val.subtype.comp p.2.toLinearMap,
    LinearMap.ne_zero_of_injective (p.1.val.subtype_injective.comp p.2.injective)⟩

private theorem range_realize (p : Σ U : Copies A S V, S ≃ₗ[A] U.val) :
    (realize p).val.range = p.1.val := by
  rw [realize, LinearMap.range_comp, LinearMap.range_eq_top.mpr p.2.surjective,
    Submodule.map_top, Submodule.range_subtype]

private theorem realize_bijective : Function.Bijective
    (realize : (Σ U : Copies A S V, S ≃ₗ[A] U.val) → {f : S →ₗ[A] V // f ≠ 0}) := by
  constructor
  · rintro ⟨U, e⟩ ⟨W, f⟩ h
    have heq : U = W := Subtype.ext <|
      (range_realize ⟨U,e⟩).symm.trans ((congrArg (fun x => x.val.range) h).trans
        (range_realize ⟨W,f⟩))
    subst W
    congr 1
    apply LinearEquiv.ext
    intro s
    exact Subtype.ext (LinearMap.congr_fun (congrArg Subtype.val h) s)
  · intro f
    let e := LinearEquiv.ofInjective f.val (LinearMap.injective_of_ne_zero f.property)
    refine ⟨⟨⟨f.val.range, ⟨e⟩⟩, e⟩, ?_⟩
    rfl

private noncomputable def isomorphismsEquiv (U : Copies A S V) :
    (S ≃ₗ[A] U.val) ≃ (S ≃ₗ[A] S) where
  toFun e := e.trans U.property.some.symm
  invFun e := e.trans U.property.some
  left_inv e := by ext s; simp
  right_inv e := by ext s; simp

/-- Nonzero maps from a simple module are parametrized by their image and an
isomorphism, whose choices form a torsor under the automorphism group. -/
private noncomputable def nonzeroMapsEquiv :
    {f : S →ₗ[A] V // f ≠ 0} ≃ Copies A S V × (S ≃ₗ[A] S) :=
  (Equiv.ofBijective realize realize_bijective).symm.trans
    (Equiv.sigmaEquivProdOfEquiv isomorphismsEquiv)

/-- The image-fiber count for a fixed simple type. -/
theorem card_nonzeroMaps :
    Nat.card {f : S →ₗ[A] V // f ≠ 0} =
      Nat.card (Copies A S V) * Nat.card (S ≃ₗ[A] S) :=
  (Nat.card_congr nonzeroMapsEquiv).trans (Nat.card_prod _ _)

variable [Finite S] [Finite V]

private theorem odd_nonzero_card (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] [Nontrivial W] : Odd (Nat.card {w : W // w ≠ 0}) := by
  classical
  let := Fintype.ofFinite W
  have := Module.Finite.of_finite (R := ZMod 2) (M := W)
  have hcard : Nat.card {w : W // w ≠ 0} = 2 ^ Module.finrank (ZMod 2) W - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_unique (α := {x : W // x = 0}),
      ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2)]
    simp only [Nat.card_eq_fintype_card, ZMod.card]
  rw [hcard]
  have hp : 0 < Module.finrank (ZMod 2) W := Module.finrank_pos
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  rw [hn, pow_succ]
  have hpow : 0 < 2 ^ n := pow_pos (by decide) _
  refine ⟨2 ^ n - 1, ?_⟩
  omega

/-- There are an odd number of submodules of a prescribed simple binary type
whenever at least one copy occurs. No semisimplicity hypothesis is required. -/
theorem odd_card_copies [Module (ZMod 2) V] [SMulCommClass A (ZMod 2) V]
    (h : Nonempty (Copies A S V)) : Odd (Nat.card (Copies A S V)) := by
  let := IsSimpleModule.nontrivial A S
  have : Finite (S →ₗ[A] V) := Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨U⟩ := h
  have hne : (U.val.subtype.comp U.property.some.toLinearMap : S →ₗ[A] V) ≠ 0 :=
    LinearMap.ne_zero_of_injective
      (U.val.subtype_injective.comp U.property.some.injective)
  have : Nontrivial (S →ₗ[A] V) := ⟨⟨_, 0, hne⟩⟩
  have hodd := odd_nonzero_card (S →ₗ[A] V)
  rw [card_nonzeroMaps] at hodd
  exact (Nat.odd_mul.mp hodd).1

/-- A two-group acting on the actual copies of one simple binary type fixes
a copy. The caller supplies its action on this literal set of submodules. -/
theorem exists_fixed_copy {P : Type*} [Group P]
    [Module (ZMod 2) V] [SMulCommClass A (ZMod 2) V]
    [MulAction P (Copies A S V)] (hP : IsPGroup 2 P)
    (h : Nonempty (Copies A S V)) :
    ∃ U : Copies A S V, ∀ p : P, p • U = U := by
  have hodd := odd_card_copies h
  obtain ⟨U, hU⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Copies A S V)
    (by simpa only [← even_iff_two_dvd, Nat.not_even_iff_odd] using hodd)
  exact ⟨U, hU⟩
end Representation.SimpleCopies
