module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.NormalType
public import Mathlib.LinearAlgebra.Prod

/-!
# A cubic fixes a copy in a doubled simple module

Nonzero maps count the simple constituents of a doubled module: their
number is the order of the endomorphism division ring plus one. Conjugation
acts on the actual irreducible subrepresentations. If that number is prime
to three, the fixed-point theorem supplies a constituent fixed by a cubic
actor, with its original action and module isomorphism retained.

Source: Aschbacher--Smith A.3.19, printed pp.54--55. The natural-module
application is CubicDouble; the chosen-source multiplicity premise remains
with the preliminary assembly owner.
-/

public noncomputable section
open Representation
open scoped MonoidAlgebra
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural

section Ring
variable {A S V : Type*} [Ring A] [AddCommGroup S] [Module A S]
  [AddCommGroup V] [Module A V] [IsSimpleModule A S]

private theorem card_nonzero (X : Type*) [Zero X] [Finite X] :
    Nat.card {x : X // x ≠ 0} = Nat.card X - 1 := by
  classical
  let := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_unique (α := {x : X // x = 0}), Nat.card_eq_fintype_card]

private def nonzeroEndEquiv : {f : Module.End A S // f ≠ 0} ≃ (S ≃ₗ[A] S) where
  toFun f := LinearEquiv.ofBijective f.val (LinearMap.bijective_of_ne_zero f.property)
  invFun e := by
    let : Nontrivial S := IsSimpleModule.nontrivial A S
    exact ⟨e.toLinearMap, LinearMap.ne_zero_of_injective e.injective⟩
  left_inv f := rfl
  right_inv e := by ext; rfl

theorem card_copies_double [Finite S] [Finite V] (e : V ≃ₗ[A] S × S) :
    Nat.card (SimpleCopies.Copies A S V) = Nat.card (Module.End A S) + 1 := by
  let : Nontrivial S := IsSimpleModule.nontrivial A S
  let : Finite (Module.End A S) := Finite.of_injective _ DFunLike.coe_injective
  let : Finite (S →ₗ[A] V) := Finite.of_injective _ DFunLike.coe_injective
  have hE : 1 < Nat.card (Module.End A S) := Finite.one_lt_card
  have hmaps : Nat.card (S →ₗ[A] V) = Nat.card (Module.End A S) ^ 2 := by
    let t : (S →ₗ[A] V) ≃ (S →ₗ[A] S × S) := {
      toFun f := e.toLinearMap.comp f
      invFun f := e.symm.toLinearMap.comp f
      left_inv f := by ext; simp
      right_inv f := by
        apply LinearMap.ext
        intro x
        exact e.apply_symm_apply (f x) }
    rw [Nat.card_congr t]
    rw [← Nat.card_congr (LinearMap.prodEquiv ℕ).toEquiv, Nat.card_prod, pow_two]
  have hauto : Nat.card (S ≃ₗ[A] S) = Nat.card (Module.End A S) - 1 := by
    rw [← Nat.card_congr nonzeroEndEquiv]
    exact card_nonzero _
  have h := SimpleCopies.card_nonzeroMaps (A := A) (S := S) (V := V)
  rw [card_nonzero, hmaps, hauto] at h
  have hfactor : Nat.card (Module.End A S) ^ 2 - 1 =
      (Nat.card (Module.End A S) + 1) * (Nat.card (Module.End A S) - 1) := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ Nat.card (Module.End A S) from by omega),
      Nat.sub_add_cancel (show 1 ≤ Nat.card (Module.End A S)^2 from by nlinarith)]
  exact Nat.mul_right_cancel (by omega) (h.symm.trans hfactor)


theorem isotypic_of_double (e : V ≃ₗ[A] S × S) : IsIsotypicOfType A V S := by
  intro U hU
  let f : U →ₗ[A] S := (LinearMap.fst A S S).comp (e.toLinearMap.comp U.subtype)
  let g : U →ₗ[A] S := (LinearMap.snd A S S).comp (e.toLinearMap.comp U.subtype)
  have h : f ≠ 0 ∨ g ≠ 0 := by
    by_contra! hn
    let : Nontrivial U := IsSimpleModule.nontrivial A U
    obtain ⟨u,hu⟩ := exists_ne (0 : U)
    apply hu
    apply U.subtype_injective
    apply e.injective
    rw [map_zero, map_zero]
    apply Prod.ext
    · exact LinearMap.congr_fun hn.1 u
    · exact LinearMap.congr_fun hn.2 u
  rcases h with hf | hg
  · exact ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)⟩
  · exact ⟨LinearEquiv.ofBijective g (LinearMap.bijective_of_ne_zero hg)⟩
end Ring

section Selection
variable {G V E : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
  [AddCommGroup E] [Module (ZMod 2)[N] E] [IsSimpleModule (ZMod 2)[N] E]
open Representation.BinaryOffender.Homogeneous

private def simpleCopiesEquiv
    (htype : IsIsotypicOfType (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)) E) :
    {U : Subrepresentation (ρ.comp N.subtype) // U.toRepresentation.IsIrreducible} ≃
      SimpleCopies.Copies (ZMod 2)[N] E (Representation.asModule (ρ.comp N.subtype)) where
  toFun U := by
    let := simple_asSubmodule U.val U.property
    exact ⟨U.val.asSubmodule, ⟨(htype U.val.asSubmodule).some.symm⟩⟩
  invFun U := by
    let S := Subrepresentation.ofSubmodule' U.val
    have hs : IsSimpleModule (ZMod 2)[N] U.val := U.property.some.isSimpleModule_iff.mp inferInstance
    refine ⟨S, (Subrepresentation.irreducible_iff_isAtom S).mpr ?_⟩
    exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff S).mp
      (isSimpleModule_iff_isAtom.mp hs)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A prime-to-three count of the actual simple constituents supplies a constituent
invariant under a three-subgroup, for the literal ambient operators. -/
theorem invariant_simple_of_count
    (htype : IsIsotypicOfType (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)) E)
    (hcount : ¬ 3 ∣ Nat.card (SimpleCopies.Copies (ZMod 2)[N] E
      (Representation.asModule (ρ.comp N.subtype))))
    (P : Subgroup G) (hP : IsPGroup 3 P) :
    ∃ U : Subrepresentation (ρ.comp N.subtype), U.toRepresentation.IsIrreducible ∧
      Nonempty (U.asSubmodule ≃ₗ[(ZMod 2)[N]] E) ∧
      ∀ p : P, U.toSubmodule.map (ρ p) = U.toSubmodule := by
  let Ω := {U : Subrepresentation (ρ.comp N.subtype) // U.toRepresentation.IsIrreducible}
  let c := normalTypeAction ρ N
  let : MulAction P Ω := {
    smul p U := ⟨c.conjugate p U.val, c.conjugate_irreducible U.val U.property p⟩
    one_smul U := Subtype.ext (c.one U.val)
    mul_smul p q U := Subtype.ext (c.mul p q U.val) }
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hΩ : ¬ 3 ∣ Nat.card Ω := by
    rw [Nat.card_congr (simpleCopiesEquiv ρ N htype)]
    exact hcount
  obtain ⟨U,hU⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card Ω hΩ
  let := simple_asSubmodule U.val U.property
  refine ⟨U.val,U.property,htype U.val.asSubmodule,?_⟩
  intro p
  have hf : c.conjugate p U.val = U.val := congrArg Subtype.val (hU p)
  exact (conjugateSubrepresentationOrderIso_toSubmodule ρ N p U.val).symm.trans
    (congrArg Subrepresentation.toSubmodule hf)

/-- In a doubled simple module, a three-group fixes a simple copy whenever
three divides the endomorphism field order minus one. -/
theorem invariant_simple_of_double [Finite V] [Finite E]
    (e : Representation.asModule (ρ.comp N.subtype) ≃ₗ[(ZMod 2)[N]] E × E)
    (hcard : 3 ∣ Nat.card (Module.End (ZMod 2)[N] E) - 1)
    (P : Subgroup G) (hP : IsPGroup 3 P) :
    ∃ U : Subrepresentation (ρ.comp N.subtype), U.toRepresentation.IsIrreducible ∧
      Nonempty (U.asSubmodule ≃ₗ[(ZMod 2)[N]] E) ∧
      ∀ p : P, U.toSubmodule.map (ρ p) = U.toSubmodule := by
  let : Finite (Representation.asModule (ρ.comp N.subtype)) :=
    Finite.of_equiv V (Representation.asModuleEquiv (ρ.comp N.subtype)).symm.toEquiv
  apply invariant_simple_of_count ρ N (isotypic_of_double e) ?_ P hP
  rw [card_copies_double e]
  let : Nontrivial E := IsSimpleModule.nontrivial (ZMod 2)[N] E
  let : Finite (Module.End (ZMod 2)[N] E) := Finite.of_injective _ DFunLike.coe_injective
  have hc : 1 < Nat.card (Module.End (ZMod 2)[N] E) := Finite.one_lt_card
  omega
end Selection
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.CubicNatural
