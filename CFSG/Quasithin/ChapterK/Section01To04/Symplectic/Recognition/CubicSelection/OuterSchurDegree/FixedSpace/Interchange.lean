module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Fintype.Prod
public import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.Linarith

/-!
# Dimensions for tensor interchange

Coordinates identify the displacement of interchange on a tensor square with
skew matrices having zero diagonal. Restriction to the strictly upper entries
is a linear equivalence, including in characteristic two. Thus the moved
dimension is `n.choose 2`, and twice the fixed dimension is `n * (n + 1)`.

This is the single-actor calculation used in the outer Schur-linear branch
of Aschbacher--Smith K.3.4, pp.456--457, and Guralnick--Malle, Classification
of 2F-modules II, Section 3.5 and Proposition 6.2. The two-actor estimate is
separate.
-/

@[expose] public section

open scoped TensorProduct
open Module
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur.FixedSpace.Tensor
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

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur.FixedSpace.Tensor
