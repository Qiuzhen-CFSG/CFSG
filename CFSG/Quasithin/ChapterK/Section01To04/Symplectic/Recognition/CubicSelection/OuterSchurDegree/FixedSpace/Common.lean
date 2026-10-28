module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.FixedSpace.Interchange
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ByContra

/-!
# Common fixed space of interchange and a diagonal involution

Choose a moved vector `x` and a functional `l` with `l x = 1`, `l (f x) = 0`.
Such a functional is constructed from a dual vector on `f x - x`, using
characteristic two and the involution equation. The symmetric tensor
`z(v) = x tensor v + v tensor x - l(v) (x tensor x)` is fixed by interchange.
Contracting `(f tensor f - 1) z(v)` in its first factor gives
`l(f v) f x - v`. On `ker (l.comp f)` this detects `-v`, so the diagonal
involution moves at least `n - 1` dimensions inside the interchange-fixed
space. Rank-nullity and its dimension `n(n+1)/2` give the half-square bound.

This proves the two-actor tensor estimate used for Aschbacher--Smith K.3.4,
pp.456--457, and Guralnick--Malle, Classification of 2F-modules II, Section
3.5 and Proposition 6.2. It does not assume an involution-adapted basis or
any fixed-space estimate.
-/

@[expose] public section

open Module
open scoped TensorProduct
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur.FixedSpace.Tensor
section General
variable {F W : Type*} [Field F] [CharP F 2] [AddCommGroup W] [Module F W]


private lemma exists_separating_functional (f : Module.End F W) (h2 : f ^ 2 = 1) (hne : f ≠ 1) :
    ∃ (x : W) (l : Module.Dual F W), l x = 1 ∧ l (f x) = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ x := by
    by_contra! h
    exact hne (LinearMap.ext h)
  obtain ⟨a, ha⟩ := Module.Projective.exists_dual_eq_one F (sub_ne_zero.mpr hx)
  have hfx : f (f x) = x := by
    have hh := LinearMap.congr_fun h2 x
    simpa only [pow_two, Module.End.mul_apply, Module.End.one_apply] using hh
  let l : Module.Dual F W := a.comp f + a x • a.comp (f - 1)
  have ha' : a (f x) = 1 + a x := by
    exact sub_eq_iff_eq_add.mp (by simpa only [map_sub] using ha)
  refine ⟨x, l, ?_, ?_⟩
  · change a (f x) + a x * a (f x - x) = 1
    rw [ha, mul_one, ha', add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · change a (f (f x)) + a x * a (f (f x) - f x) = 0
    have ham : a (x - f x) = 1 := by
      rw [← neg_sub (f x) x, map_neg, ha, CharTwo.neg_eq]
    rw [hfx, ham, mul_one, CharTwo.add_self_eq_zero]
end General

section Bound
variable {F : Type*} [Field F] (n : ℕ)
variable (f : Module.End F (Fin n → F)) (x : Fin n → F) (l : Module.Dual F (Fin n → F))
  (hx : l x = 1) (hfx : l (f x) = 0)


private noncomputable def symmetricSeed : (Fin n → F) →ₗ[F] Space F n :=
  (TensorProduct.mk F _ _ x) + (TensorProduct.mk F _ _).flip x -
    (LinearMap.toSpanSingleton F (Space F n) (x ⊗ₜ[F] x)).comp l

private lemma symmetricSeed_apply (v : Fin n → F) : symmetricSeed n x l v =
    x ⊗ₜ[F] v + v ⊗ₜ[F] x - l v • (x ⊗ₜ[F] x) := rfl

private lemma symmetricSeed_fixed (v : Fin n → F) :
    symmetricSeed n x l v ∈ (flip F n - 1).ker := by
  change flip F n (symmetricSeed n x l v) - symmetricSeed n x l v = 0
  rw [sub_eq_zero]
  simp [symmetricSeed_apply, flip, add_comm]

private noncomputable def contract : Space F n →ₗ[F] (Fin n → F) :=
  (TensorProduct.lid F (Fin n → F)).toLinearMap.comp (TensorProduct.map l LinearMap.id)

private lemma contract_tmul (v w : Fin n → F) : contract n l (v ⊗ₜ[F] w) = l v • w := by
  simp [contract]
include hx hfx in

private lemma contract_displacement_seed (v : Fin n → F) :
    contract n l ((TensorProduct.map f f - 1) (symmetricSeed n x l v)) =
      l (f v) • f x - v := by
  simp [symmetricSeed_apply, contract_tmul, hx, hfx]


include hx hfx in

private lemma displacement_rank_lower (h2 : f ^ 2 = 1) :
    n ≤ finrank F ((TensorProduct.map f f - 1).domRestrict (flip F n - 1).ker).range + 1 := by
  let D := (TensorProduct.map f f - 1).domRestrict (flip F n - 1).ker
  let a := l.comp f
  let J : a.ker →ₗ[F] D.range :=
    (((TensorProduct.map f f - 1).comp (symmetricSeed n x l)).domRestrict a.ker).codRestrict
      D.range (fun v => ⟨⟨symmetricSeed n x l v, symmetricSeed_fixed n x l v⟩, rfl⟩)
  have hJ (v : a.ker) : contract n l (J v).val = -v.val := by
    change contract n l ((TensorProduct.map f f - 1) (symmetricSeed n x l v)) = -v.val
    rw [contract_displacement_seed n f x l hx hfx]
    have hv : l (f v.val) = 0 := v.property
    rw [hv, zero_smul, zero_sub]
  have hi : Function.Injective J := by
    intro v w h
    apply Subtype.ext
    apply neg_injective
    simpa only [hJ] using congrArg (fun z : D.range => contract n l z.val) h
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  have ha : a ≠ 0 := by
    intro hz
    have h := LinearMap.congr_fun hz (f x)
    have hh := LinearMap.congr_fun h2 x
    have hff : f (f x) = x := by
      simpa only [pow_two, Module.End.mul_apply, Module.End.one_apply] using hh
    change l (f (f x)) = 0 at h
    rw [hff, hx] at h
    exact one_ne_zero h
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero ha
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hk
  change n ≤ finrank F D.range + 1
  omega
end Bound

set_option backward.isDefEq.respectTransparency false in
/-- A nontrivial diagonal involution and interchange have common fixed
space of dimension at most half the tensor square. -/
theorem common_fixed_bound {F : Type*} [Field F] [CharP F 2] (n : ℕ) (hn : 2 ≤ n)
    (f : Module.End F (Fin n → F)) (h2 : f ^ 2 = 1) (hne : f ≠ 1) :
    2 * finrank F ↥((flip F n - 1).ker ⊓ (TensorProduct.map f f - 1).ker) ≤ n * n := by
  obtain ⟨x, l, hx, hfx⟩ := exists_separating_functional f h2 hne
  have hlower := displacement_rank_lower n f x l hx hfx h2
  let S := (flip F n - 1).ker
  let D : S →ₗ[F] Space F n := (TensorProduct.map f f - 1).domRestrict S
  let e : D.ker ≃ₗ[F] ↥(S ⊓ (TensorProduct.map f f - 1).ker) :=
    { toFun := fun v => ⟨v.val.val, v.val.property, v.property⟩
      invFun := fun v => ⟨⟨v.val, v.property.1⟩, v.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hd := LinearMap.finrank_range_add_finrank_ker (K := F) (V := S) (V₂ := Space F n) D
  have he := e.finrank_eq
  have hs := two_mul_finrank_ker_flip F n
  change finrank F D.range + finrank F D.ker = finrank F S at hd
  change 2 * finrank F S = n * (n + 1) at hs
  change n ≤ finrank F D.range + 1 at hlower
  change 2 * finrank F ↥(S ⊓ (TensorProduct.map f f - 1).ker) ≤ n * n
  nlinarith only [hd, he, hs, hlower, hn]
end CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur.FixedSpace.Tensor