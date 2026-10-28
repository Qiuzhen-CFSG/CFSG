module

public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

/-!
# Displacement of tensor products of involutions

In characteristic two the displacement `A - 1` is square-zero. A linear section
of its image, and a complement to that image inside its kernel, identify the
space with exchanged pairs plus a fixed summand. Tensoring an exchanged pair
with an involution on `W` contributes exactly `dim W` to displacement; tensoring
the fixed summand contributes its dimension times the second displacement rank.
Consequently, if the factor dimensions are `n, m` and their displacement ranks
are `r, s`, the tensor displacement rank is `m*r + n*s - 2*r*s`.

The six-dimensional corollary needs only `r,s ≥ 2`: square-zero displacement
also gives `r,s ≤ 3`, and the tensor displacement is sixteen or eighteen.
The actual natural G₂ pair consumes this corollary in `Inner.TensorRank`.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5,
manuscript pp.20,55–56 (the two-factor no-transvection step).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module
open scoped TensorProduct
open Representation.BinaryOffender.NaturalTensor
namespace Representation.TensorInvolutionDisplacement
variable {K U W : Type*} [Field K] [CharP K 2]
  [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W]

private theorem twice_zero {V : Type*} [AddCommGroup V] [Module K V] (v : V) : v + v = 0 := by
  rw [← two_smul K, CharTwo.two_eq_zero, zero_smul]

private theorem square_zero (A : Module.End K U) (hA : A * A = 1) :
    (A - 1) * (A - 1) = 0 := by
  calc
    (A - 1) * (A - 1) = (1 + 1) - (A + A) := by noncomm_ring [hA]
    _ = 0 := by rw [twice_zero (K := K) (1 : Module.End K U), twice_zero (K := K) A, sub_self]

/-- In characteristic two an involution is a direct sum of exchanged pairs and
fixed vectors. The space indexing the pairs is its actual displacement image. -/
theorem exists_swap_form (A : Module.End K U) (hA : A * A = 1) :
    ∃ H : Submodule K (LinearMap.ker (A - 1)),
      ∃ e : ((LinearMap.range (A - 1) × LinearMap.range (A - 1)) × H) ≃ₗ[K] U,
        ∀ x y z, A (e ((x, y), z)) = e ((y, x), z) := by
  let N := A - 1
  have hN : ∀ v, N (N v) = 0 := fun v => LinearMap.congr_fun (square_zero A hA) v
  let R := LinearMap.range N
  let Z := LinearMap.ker N
  let j : R →ₗ[K] Z := R.subtype.codRestrict Z (by
    rintro ⟨v, w, rfl⟩
    exact hN w)
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : Z => (z : U)) h)
  obtain ⟨H, hH⟩ := (LinearMap.range j).exists_isCompl
  let eZ : (R × H) ≃ₗ[K] Z :=
    (LinearEquiv.prodCongr (LinearEquiv.ofInjective j hj) (LinearEquiv.refl K H)).trans
      ((LinearMap.range j).prodEquivOfIsCompl H hH)
  have heZ (r : R) (z : H) : (eZ (r, z) : U) = (r : U) + (z : Z) := rfl
  obtain ⟨f, hf⟩ := N.rangeRestrict.exists_rightInverse_of_surjective N.range_rangeRestrict
  have hnf (r : R) : N (f r) = r := congrArg Subtype.val (LinearMap.congr_fun hf r)
  have hAf (r : R) : A (f r) = f r + (r : U) := by
    have hh := hnf r
    change A (f r) - f r = _ at hh
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  have hAz (z : H) : A ((z : Z) : U) = z := sub_eq_zero.mp (z : Z).property
  let L : ((R × R) × H) →ₗ[K] U :=
    (f.coprod (A.comp f)).coprod (Z.subtype.comp H.subtype)
  have hL (x y : R) (z : H) : L ((x, y), z) = f x + A (f y) + (z : Z) := rfl
  have hNL (x y : R) (z : H) : N (L ((x, y), z)) = ((x + y : R) : U) := by
    rw [hL, map_add, map_add, hAf, map_add, hnf, hnf]
    have hyr : N (y : U) = 0 := by obtain ⟨v,hv⟩ := y.property; rw [← hv, hN]
    rw [hyr, (z : Z).property, add_zero, add_zero]
    rfl
  have hLi : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    rintro ⟨⟨x, y⟩,z⟩ hv
    have hl : L ((x, y), z) = 0 := hv
    have hxy : x + y = 0 := by
      apply Subtype.ext
      have hh := congrArg N hl
      simpa only [hNL, map_zero, Submodule.coe_zero] using hh
    have hx : x = -y := eq_neg_of_add_eq_zero_left hxy
    have he : eZ (y, z) = 0 := by
      apply Subtype.ext
      rw [heZ]
      rw [hL, hx, map_neg, hAf] at hl
      simpa only [neg_add_cancel_left, Submodule.coe_zero] using hl
    have hyz : (y, z) = 0 := eZ.injective (by simpa using he)
    have hy : y = 0 := congrArg Prod.fst hyz
    have hz : z = 0 := congrArg Prod.snd hyz
    simp [hx,hy,hz]
  have hLs : Function.Surjective L := by
    intro u
    let r : R := N.rangeRestrict u
    let k : Z := ⟨u - f r, by change N (u - f r) = 0; rw [map_sub, hnf]; exact sub_self _⟩
    obtain ⟨⟨q, z⟩, hqz⟩ := eZ.surjective k
    refine ⟨((r - q, q), z), ?_⟩
    have hqz' : (q : U) + (z : Z) = u - f r := congrArg Subtype.val hqz
    rw [hL, map_sub, hAf]
    change f r - f q + (f q + (q : U)) + ((z : Z) : U) = u
    rw [← add_assoc, sub_add_cancel, add_assoc, hqz']
    abel
  refine ⟨H, LinearEquiv.ofBijective L ⟨hLi, hLs⟩, ?_⟩
  intro x y z
  change A (L ((x, y), z)) = L ((y, x), z)
  have hAA (v : U) : A (A v) = v := LinearMap.congr_fun hA v
  simp only [hL, map_add, hAA, hAz]
  rw [add_comm (A (f x)) (f y)]


variable [FiniteDimensional K U] [FiniteDimensional K W]

omit [CharP K 2] in
private theorem prod_displacement (A : Module.End K U) (B : Module.End K W) :
    operatorFixedCodim (A.prodMap B) = operatorFixedCodim A + operatorFixedCodim B := by
  have hmap : A.prodMap B - 1 = (A - 1).prodMap (B - 1) := by ext x <;> rfl
  let P := LinearMap.range (A - 1)
  let Q := LinearMap.range (B - 1)
  have hi : Function.Injective (P.subtype.prodMap Q.subtype) := by
    rintro ⟨x, y⟩ ⟨x',y'⟩ h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hd := LinearMap.finrank_range_of_inj (f := P.subtype.prodMap Q.subtype) hi
  rw [LinearMap.range_prodMap, Submodule.range_subtype, Submodule.range_subtype, Module.finrank_prod] at hd
  unfold operatorFixedCodim
  rw [hmap, LinearMap.range_prodMap]
  exact hd

omit [CharP K 2] in
private theorem lTensor_displacement (B : Module.End K W) :
    operatorFixedCodim (B.lTensor U) = finrank K U * operatorFixedCodim B := by
  have hd : B.lTensor U - 1 = (B - 1).lTensor U := by
    ext x y
    simp
  rw [operatorFixedCodim, hd, LinearMap.lTensor_range]
  rw [LinearMap.finrank_range_of_inj
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)]
  exact Module.finrank_tensorProduct

private def exchange (B : Module.End K U) : Module.End K (U × U) :=
  (B.comp (LinearMap.snd K U U)).prod (B.comp (LinearMap.fst K U U))

omit [CharP K 2] in
private theorem exchange_displacement (B : Module.End K U) (hB : B * B = 1) :
    operatorFixedCodim (exchange B) = finrank K U := by
  let J := B.prod (LinearMap.id : Module.End K U)
  have hi : Function.Injective J := by
    intro x y h
    exact congrArg Prod.snd h
  have hk : LinearMap.ker (exchange B - 1) = LinearMap.range J := by
    ext ⟨x, y⟩
    constructor
    · intro h
      have hh : (B y, B x) - (x, y) = 0 := h
      have h1 : B y = x := congrArg Prod.fst (sub_eq_zero.mp hh)
      exact ⟨y, Prod.ext h1 rfl⟩
    · rintro ⟨z, hz⟩
      rw [← hz]
      change (B z, B (B z)) - (B z, z) = 0
      rw [show B (B z) = z from LinearMap.congr_fun hB z, sub_self]
  have hnull := operatorFixedCodim_add_finrank (exchange B)
  rw [hk, LinearMap.finrank_range_of_inj hi, Module.finrank_prod] at hnull
  omega

/-- An involution in characteristic two moves at most half the space. -/
theorem twice_displacement_le (A : Module.End K U) (hA : A * A = 1) :
    2 * operatorFixedCodim A ≤ finrank K U := by
  have hi : LinearMap.range (A - 1) ≤ LinearMap.ker (A - 1) := by
    rintro v ⟨w,rfl⟩
    exact LinearMap.congr_fun (square_zero A hA) w
  have hd := Submodule.finrank_mono hi
  have hn := operatorFixedCodim_add_finrank A
  change operatorFixedCodim A ≤ _ at hd
  omega

/-- Tensor displacement formula, stated without truncated subtraction. -/
theorem tensor_displacement_formula (A : Module.End K U) (B : Module.End K W)
    (hA : A * A = 1) (hB : B * B = 1) :
    operatorFixedCodim (TensorProduct.map A B) +
      2 * operatorFixedCodim A * operatorFixedCodim B =
      finrank K W * operatorFixedCodim A + finrank K U * operatorFixedCodim B := by
  obtain ⟨H, e, he⟩ := exists_swap_form A hA
  let R := LinearMap.range (A - 1)
  let S : Module.End K ((R × R) × H) :=
    (LinearEquiv.prodComm K R R).toLinearMap.prodMap 1
  let C : Module.End K (R ⊗[K] W) := B.lTensor R
  let D := (TensorProduct.prodLeft K K (R × R) H W).trans
    ((TensorProduct.prodLeft K K R R W).prodCongr (LinearEquiv.refl K (H ⊗[K] W)))
  have hd := e.finrank_eq
  rw [Module.finrank_prod, Module.finrank_prod] at hd
  change operatorFixedCodim A + operatorFixedCodim A + finrank K H = finrank K U at hd
  have hfirst : operatorFixedCodim (k := K) (V := ((R × R) × H) ⊗[K] W) (TensorProduct.map S B) =
      operatorFixedCodim (TensorProduct.map A B) := by
    apply operatorFixedCodim_eq_of_equiv _ _ (e.rTensor W)
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      rcases x with ⟨⟨r, s⟩, z⟩
      change e ((s, r), z) ⊗ₜ[K] B y = A (e ((r, s), z)) ⊗ₜ[K] B y
      rw [he]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsecond : operatorFixedCodim (k := K) (V := ((R × R) × H) ⊗[K] W) (TensorProduct.map S B) =
      operatorFixedCodim (k := K) (V := ((R ⊗[K] W) × (R ⊗[K] W)) × (H ⊗[K] W))
        ((exchange C).prodMap (B.lTensor H)) := by
    apply operatorFixedCodim_eq_of_equiv _ _ D
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      rcases x with ⟨⟨r, s⟩, z⟩
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hC : C * C = 1 := by
    dsimp [C]
    rw [← LinearMap.lTensor_mul, hB]
    exact LinearMap.lTensor_id R W
  have hr : operatorFixedCodim (TensorProduct.map A B) =
      operatorFixedCodim A * finrank K W + finrank K H * operatorFixedCodim B := by
    rw [← hfirst, hsecond,
      prod_displacement (U := (R ⊗[K] W) × (R ⊗[K] W)) (W := H ⊗[K] W),
      exchange_displacement (U := R ⊗[K] W) C hC,
      Module.finrank_tensorProduct, lTensor_displacement (U := H)]
    rfl
  nlinarith [congrArg (fun n => n * operatorFixedCodim B) hd]

/-- Two six-dimensional involutions each moving at least two dimensions move
at least sixteen dimensions on their tensor product. -/
theorem sixteen_le_tensor_displacement
    (A : Module.End K U) (B : Module.End K W)
    (hU : finrank K U = 6) (hW : finrank K W = 6)
    (hA : A * A = 1) (hB : B * B = 1)
    (hrA : 2 ≤ operatorFixedCodim A) (hrB : 2 ≤ operatorFixedCodim B) :
    16 ≤ operatorFixedCodim (TensorProduct.map A B) := by
  have ha := twice_displacement_le A hA
  have hb := twice_displacement_le B hB
  have hf := tensor_displacement_formula A B hA hB
  rw [hU] at ha
  rw [hW] at hb
  rw [hU,hW] at hf
  have ha' : operatorFixedCodim A = 2 ∨ operatorFixedCodim A = 3 := by omega
  have hb' : operatorFixedCodim B = 2 ∨ operatorFixedCodim B = 3 := by omega
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
    rw [ha',hb'] at hf <;> omega

end Representation.TensorInvolutionDisplacement
