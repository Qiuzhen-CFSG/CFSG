module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.FixedRadical
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Natural fixed spaces for the maximal-rank outer tensor case

In the literal four-dimensional symplectic matrix action, an element fixing a
hyperplane has every displacement in its orthogonal line. Its displacement on
one vector outside the hyperplane determines the matrix. Thus the pointwise
stabilizer has at most `Nat.card k` elements. A faithful group of larger order
has common fixed space of dimension at most two; full fixation is excluded by
faithfulness. This argument works in every characteristic.

The order-`Nat.card k ^ 3` corollaries, including the coefficient-Frobenius twist
in characteristic two, supply the natural-section estimate needed for the
strict inequality on printed p.457. The homomorphism into the actual symplectic
matrix group is explicit, so these results apply to a descended native section
once its injectivity has been proved. No elementary-abelian hypothesis or
exclusion of the two-element field is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, K.3.4.2,
printed pp.456–457 (PDF pp.467–468), especially the maximal-rank strict estimate.
-/

@[expose] public section

open Theory.SpecificGroups.SymplecticFour
open Representation
noncomputable section
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry.MaximalNatural
variable {k : Type*} [Field k]

private theorem matrix_ext {g h : Sp k} (he : ∀ x : Vector k, g • x = h • x) : g = h := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have hh := congrFun (he (Pi.single j 1)) i
  simpa [smul_eq_mulVec, Matrix.mulVec_single] using hh

/-- Fixing a subspace pointwise puts every displacement in its right orthogonal complement. -/
theorem displacement_mem_orthogonal (U : Submodule k (Vector k)) (g : Sp k)
    (hg : ∀ x ∈ U, g • x = x) (v : Vector k) :
    g • v - v ∈ (form k).orthogonal U := by
  intro x hx
  have hp := preserves_form g x v
  rw [hg x hx] at hp
  change form k x (g • v - v) = 0
  rw [map_sub, hp, sub_self]

/-- For a faithful action fixing a hyperplane, one outside displacement determines the actor. -/
theorem hyperplane_eval_injective (U : Submodule k (Vector k))
    (hU : Module.finrank k U = 3) (v : Vector k) (hv : v ∉ U)
    {H : Type*} [Group H] (f : H →* Sp k) (hf : Function.Injective f)
    (hfix : ∀ a : H, ∀ x ∈ U, f a • x = x) :
    Function.Injective (fun a : H => f a • v - v) := by
  have hspan : U ⊔ Submodule.span k {v} = ⊤ := by
    apply Submodule.eq_top_iff_finrank_eq.mpr
    rw [Submodule.finrank_sup_span_singleton hv, hU]
    simp [Theory.SpecificGroups.SymplecticFour.Vector]
  intro a b hab
  have hev : f a • v = f b • v := sub_left_inj.mp hab
  apply hf
  apply matrix_ext
  intro x
  have heq : U ⊔ Submodule.span k {v} ≤
      LinearMap.eqLocus (toLinear (f a)).toLinearMap (toLinear (f b)).toLinearMap := by
    apply sup_le
    · intro y hy
      exact (hfix a y hy).trans (hfix b y hy).symm
    · apply Submodule.span_le.mpr
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hev
  apply heq
  rw [hspan]
  trivial

/-- A faithful group fixing a natural hyperplane has order at most the field order. -/
theorem card_le_of_fixes_hyperplane [Finite k]
    (U : Submodule k (Vector k)) (hU : Module.finrank k U = 3)
    {H : Type*} [Group H] (f : H →* Sp k) (hf : Function.Injective f)
    (hfix : ∀ a : H, ∀ x ∈ U, f a • x = x) : Nat.card H ≤ Nat.card k := by
  have hne : U ≠ ⊤ := by
    intro h
    have hd : Module.finrank k U = 4 := by
      rw [h]; simp [Theory.SpecificGroups.SymplecticFour.Vector]
    omega
  obtain ⟨v, hv⟩ := SetLike.exists_not_mem_of_ne_top U hne (by simp)
  let d : H → (form k).orthogonal U := fun a =>
    ⟨f a • v - v, displacement_mem_orthogonal U (f a) (hfix a) v⟩
  have hd : Function.Injective d := by
    intro a b hab
    exact hyperplane_eval_injective U hU v hv f hf hfix (congrArg Subtype.val hab)
  have hc := Nat.card_le_card_of_injective d hd
  have hdim : Module.finrank k ((form k).orthogonal U) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate, hU]
    simp [Theory.SpecificGroups.SymplecticFour.Vector]
  rwa [Module.natCard_eq_pow_finrank (K := k) (V := (form k).orthogonal U),
    hdim, pow_one] at hc

/-- A faithful natural action of order greater than the field order fixes at most a plane. -/
theorem invariants_finrank_le_two_of_card_lt [Finite k]
    {H : Type*} [Group H] [Finite H] (f : H →* Sp k) (hf : Function.Injective f)
    (hc : Nat.card k < Nat.card H) :
    Module.finrank k (invariants ((symplecticNatural 2).comp f)) ≤ 2 := by
  let U := invariants ((symplecticNatural 2).comp f)
  have hfix : ∀ a : H, ∀ x ∈ U, f a • x = x := fun a x hx => hx a
  have hne : U ≠ ⊤ := by
    intro htop
    have hi : Function.Injective (fun _ : H => ()) := by
      intro a b _
      apply hf
      apply matrix_ext
      intro x
      have hx : x ∈ U := by rw [htop]; trivial
      exact (hfix a x hx).trans (hfix b x hx).symm
    have hsmall := Nat.card_le_card_of_injective _ hi
    have hk : 1 < Nat.card k := Finite.one_lt_card
    simp only [Nat.card_unique] at hsmall
    omega
  have hd := Submodule.finrank_lt hne
  have hfour : Module.finrank k (Vector k) = 4 := by
    simp [Theory.SpecificGroups.SymplecticFour.Vector]
  rw [hfour] at hd
  by_contra hn
  have hthree : Module.finrank k U = 3 := by change ¬ Module.finrank k U ≤ 2 at hn; omega
  exact (not_le_of_gt hc) (card_le_of_fixes_hyperplane U hthree f hf hfix)

/-- The literal pointwise stabilizer of a natural hyperplane has order at most the field order. -/
theorem pointwise_stabilizer_hyperplane_card_le [Finite k]
    (U : Submodule k (Vector k)) (hU : Module.finrank k U = 3) :
    Nat.card (fixingSubgroup (Sp k) (U : Set (Vector k))) ≤ Nat.card k := by
  let P := fixingSubgroup (Sp k) (U : Set (Vector k))
  exact card_le_of_fixes_hyperplane U hU P.subtype Subtype.val_injective
    (fun a => (mem_fixingSubgroup_iff (Sp k)).mp a.property)

/-- The fixed-space bound for an actual subgroup of the standard symplectic matrix group. -/
theorem invariants_subgroup_finrank_le_two_of_card_lt [Finite k]
    (B : Subgroup (Sp k)) (hB : Nat.card k < Nat.card B) :
    Module.finrank k (invariants ((symplecticNatural 2).comp B.subtype)) ≤ 2 :=
  invariants_finrank_le_two_of_card_lt B.subtype Subtype.val_injective hB

/-- The maximal-rank consumer: a faithful group of order `q³` fixes at most a plane, also at `q = 2`. -/
theorem invariants_finrank_le_two_of_card_cube [Finite k]
    {H : Type*} [Group H] [Finite H] (f : H →* Sp k) (hf : Function.Injective f)
    (hH : Nat.card H = Nat.card k ^ 3) :
    Module.finrank k (invariants ((symplecticNatural 2).comp f)) ≤ 2 := by
  apply invariants_finrank_le_two_of_card_lt f hf
  rw [hH]
  simpa only [pow_one] using
    (Nat.pow_lt_pow_right (Finite.one_lt_card (α := k)) (by decide : 1 < 3))

/-- The order-`q³` specialization for the literal subgroup inclusion. -/
theorem invariants_subgroup_finrank_le_two_of_card_cube [Finite k]
    (B : Subgroup (Sp k)) (hB : Nat.card B = Nat.card k ^ 3) :
    Module.finrank k (invariants ((symplecticNatural 2).comp B.subtype)) ≤ 2 :=
  invariants_finrank_le_two_of_card_cube B.subtype Subtype.val_injective hB

/-- The same bound after applying a field automorphism to every matrix coefficient. -/
theorem invariants_fieldTwist_finrank_le_two_of_card_cube [Finite k]
    {H : Type*} [Group H] [Finite H] (f : H →* Sp k) (hf : Function.Injective f)
    (hH : Nat.card H = Nat.card k ^ 3) (σ : k ≃+* k) :
    Module.finrank k (invariants ((symplecticNatural 2).comp
      ((DiagramAutomorphisms.fieldAutomorphism σ).toMonoidHom.comp f))) ≤ 2 :=
  invariants_finrank_le_two_of_card_cube _
    ((DiagramAutomorphisms.fieldAutomorphism σ).injective.comp hf) hH

/-- The coefficient-Frobenius-twisted natural section used in characteristic two. -/
theorem invariants_frobeniusTwist_finrank_le_two_of_card_cube [Finite k] [CharP k 2]
    {H : Type*} [Group H] [Finite H] (f : H →* Sp k) (hf : Function.Injective f)
    (hH : Nat.card H = Nat.card k ^ 3) :
    Module.finrank k (invariants ((symplecticNatural 2).comp
      ((DiagramAutomorphisms.fieldAutomorphism (frobeniusEquiv k 2)).toMonoidHom.comp f))) ≤ 2 :=
  invariants_fieldTwist_finrank_le_two_of_card_cube f hf hH (frobeniusEquiv k 2)

end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry.MaximalNatural
