module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Fintype.Prod
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith

/-!
# Dimensions for tensor interchange

Coordinates identify the displacement of interchange on a tensor square with
skew matrices having zero diagonal. Restriction to the strictly upper entries
is a linear equivalence, including in characteristic two. Thus the moved
dimension is `n.choose 2`, and twice the fixed dimension is `n * (n + 1)`.

This is the single-actor calculation used in the outer Schur-linear branch
of Aschbacher--Smith K.3.4, pp.456--457, and Guralnick--Malle, Classification
of 2F-modules II, Section 3.5 and Proposition 6.2. The common-fixed estimate also handles a nonidentity diagonal involution.

Adapted without changing the proofs from the completed CFSG symplectic
`OuterSchurDegree.FixedSpace.Interchange` and `.Common` development (fleet
attempt 64431f55976340f083f01c48a790299a). This reusable lower-layer copy is
consumed by the SL₃ tensor branch of K.3.2.
-/

@[expose] public section

open scoped TensorProduct
open Module
namespace Representation.TensorInterchange
variable (F : Type*) [Field F] (n : ℕ)

/-- The coordinate tensor square. -/
abbrev Space := (Fin n → F) ⊗[F] (Fin n → F)

private noncomputable def coords : Space F n ≃ₗ[F] (Fin n → Fin n → F) :=
  TensorProduct.piScalarRight F F (Fin n → F) (Fin n)

/-- The actual tensor interchange operator. -/
noncomputable def flip : Module.End F (Space F n) :=
  (TensorProduct.comm F _ _).toLinearMap

private lemma coords_flip (z : Space F n) (i j : Fin n) :
    coords F n (flip F n z) i j = coords F n z j i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [coords, flip, mul_comm]
  | add x y hx hy => simp [hx, hy]


private abbrev Pairs := {p : Fin n × Fin n // p.1 < p.2}

private noncomputable def upper : (flip F n - 1).range →ₗ[F] (Pairs n → F) where
  toFun z p := coords F n z.val p.val.1 p.val.2
  map_add' x y := by ext p; simp
  map_smul' c x := by ext p; simp

private lemma coords_range_diag (z : (flip F n - 1).range) (i : Fin n) :
    coords F n z.val i i = 0 := by
  obtain ⟨x, hx⟩ := z.property
  rw [← hx]
  simp [coords_flip]

private lemma coords_range_skew (z : (flip F n - 1).range) (i j : Fin n) :
    coords F n z.val i j = - coords F n z.val j i := by
  obtain ⟨x, hx⟩ := z.property
  rw [← hx]
  simp [coords_flip]

private lemma upper_injective : Function.Injective (upper F n) := by
  intro x y h
  apply Subtype.ext
  apply (coords F n).injective
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · exact congrFun h ⟨(i, j), hij⟩
  · subst j
    rw [coords_range_diag, coords_range_diag]
  · rw [coords_range_skew F n x i j, coords_range_skew F n y i j]
    exact congrArg Neg.neg (congrFun h ⟨(j, i), hij⟩)

private lemma upper_surjective : Function.Surjective (upper F n) := by
  intro a
  let M : Fin n → Fin n → F := fun i j => if h : j < i then a ⟨(j, i), h⟩ else 0
  let x := (coords F n).symm M
  refine ⟨⟨(flip F n - 1) x, ⟨x, rfl⟩⟩, ?_⟩
  ext p
  change coords F n ((flip F n - 1) x) p.val.1 p.val.2 = a p
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, Pi.sub_apply,
    coords_flip]
  simp only [x, LinearEquiv.apply_symm_apply]
  simp [M, p.property, not_lt_of_gt p.property]

/-- The exact moved dimension of tensor interchange, over any field. -/
theorem finrank_range_flip : Module.finrank F (flip F n - 1).range = n.choose 2 := by
  let e := LinearEquiv.ofBijective (upper F n) ⟨upper_injective F n, upper_surjective F n⟩
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp only [Pairs, Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]

/-- The dimension of the tensor square. -/
theorem finrank_space : Module.finrank F (Space F n) = n * n := by
  simp [Space]

/-- Twice the fixed dimension of interchange, without division by two in the field. -/
theorem two_mul_finrank_ker_flip :
    2 * Module.finrank F (flip F n - 1).ker = n * (n + 1) := by
  have hc : 2 * n.choose 2 + n = n * n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith
  have h := (flip F n - 1).finrank_range_add_finrank_ker
  rw [finrank_range_flip, finrank_space] at h
  nlinarith

end Representation.TensorInterchange

namespace Representation.TensorInterchange
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
end Representation.TensorInterchange