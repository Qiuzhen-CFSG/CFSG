module
public import Theory.Representation.TensorThreeFixedSpace
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.HermitianDescent
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.LargeFixed
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.OddExponent.LinearReduction

/-!
# The odd-element bound for the Hermitian source

A large fixed space first forces fixed-field linearity. Odd order then
kills the remaining quadratic coefficient automorphism, giving a literal
GL₃ congruence with an odd-order lift. Scalar extension identifies its
fixed matrices with the tensor action, where the eigenvalue calculation
bounds fixed dimension by five. Nonidentity scalar congruences fix no
nonzero vector. Restriction to the binary field yields codimension at
least 4n for every nonidentity odd actor, including composite order and n = 1.

The actual chosen-orbit consumer is in the Chapter 12 OddElements extension.
This discharges the beta input of 7.4.1. Ambient odd-normalizer control and
the remaining exclusion are still owned by
qt-d-1222-nonmathieu-hermitian-exclusion; no r-bound is asserted here.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.0.1,
the beta calculation in H.4.2, and 7.4.1, printed pp.377,382,699–700
(refs/quasithin.pdf).
-/

public noncomputable section
open scoped TensorProduct Classical
open Module Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open CFSG.Quasithin.ChapterK.Linear.Recognition.HermitianDescent
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
variable (n : ℕ) [NeZero n]

private def congruenceFixed (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) :
    Submodule (F n) (Space n) := ((congruence n g).toLinearMap - 1).ker

private theorem congruenceFixed_le_five_of_nonscalar
    (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (ho : Odd (orderOf g))
    (hs : ¬ ∃ c : E n, g.val = c • 1) :
    finrank (F n) (congruenceFixed n g) ≤ 5 := by
  let W := congruenceFixed n g
  let f := (scalarExtensionEquiv n).toLinearMap.comp (W.subtype.baseChange (E n))
  have hf : Function.Injective f := (scalarExtensionEquiv n).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap W.subtype Subtype.val_injective)
  have hp : g.val ^ orderOf g = 1 := by
    exact congrArg Units.val (pow_orderOf_eq_one g)
  have hp' : (g.val.map (sigma n)) ^ orderOf g = 1 := by
    change (g.val.map (sigma n).toRingHom) ^ orderOf g = 1
    rw [← Matrix.map_pow, hp]
    exact (sigma n).toRingHom.mapMatrix.map_one
  have hd := TensorThreeFixedSpace.matrix_fixed_finrank_le_five_of_odd
    g.val (g.val.map (sigma n)) (orderOf g) (orderOf g) ho ho hp hp' hs
    (TensorThreeFixedSpace.matrix_nonscalar_map (sigma n).toRingHom g.val hs) f hf (by
      intro u
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add u v hu hv => simp only [map_add, Matrix.mul_add, Matrix.add_mul, hu, hv]
      | tmul c X =>
        change g.val * (c • X.val.val) * adjoint n g.val = c • X.val.val
        rw [Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        have hx : congruence n g X.val = X.val := sub_eq_zero.mp X.property
        exact congrArg Subtype.val hx)
  rwa [Module.finrank_baseChange] at hd

/-- A nonidentity odd GL₃ congruence fixes at most five dimensions over the
actual fixed field. Its scalar kernel is retained. -/
theorem congruenceFixed_le_five
    (g : Matrix.GeneralLinearGroup (Fin 3) (E n)) (ho : Odd (orderOf g))
    (hne : binaryCongruence n g ≠ 1) :
    finrank (F n) (((congruence n g).toLinearMap - 1).ker) ≤ 5 := by
  change finrank (F n) (congruenceFixed n g) ≤ 5
  by_cases hs : ∃ c : E n, g.val = c • 1
  · obtain ⟨c,hc⟩ := hs
    have hscalar : g.val = Matrix.scalar (Fin 3) c := by
      rw [hc]
      ext i j
      by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
    have hnorm : c * sigma n c ≠ 1 := by
      intro hh
      apply hne
      apply LinearEquiv.ext
      intro X
      apply Subtype.ext
      change g.val * X.val * adjoint n g.val = X.val
      rw [hscalar, scalar_congruence, hh, one_smul]
    have hz : congruenceFixed n g = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro X hX
      have hx : congruence n g X = X := sub_eq_zero.mp hX
      have hh := congrArg Subtype.val hx
      change g.val * X.val * adjoint n g.val = X.val at hh
      rw [hscalar, scalar_congruence] at hh
      change X = 0
      apply Subtype.ext
      ext i j
      have hij := congrFun (congrFun hh i) j
      have hmul : (c * sigma n c - 1) * X.val i j = 0 := by
        change (c * sigma n c) * X.val i j = X.val i j at hij
        rw [sub_mul, one_mul, hij, sub_self]
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hnorm)
    rw [hz, finrank_bot]
    omega
  · exact congruenceFixed_le_five_of_nonscalar n g ho hs

/-- The beta estimate holds for every nonidentity odd actor in the complete
binary Hermitian normalizer, including composite order and half-degree one. -/
theorem odd_fixedCodim_ge_four_mul
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (x : M)
    (hx : x.val ∈ binaryNormalizer n) (ho : Odd (orderOf x)) (hne : x ≠ 1) :
    4*n ≤ fixedCodim (overgroupAction n M) (Subgroup.zpowers x) := by
  have hnull := fixedCodim_add_finrank (overgroupAction n M) (Subgroup.zpowers x)
  rw [finrank_binary] at hnull
  by_contra hbad
  have hlarge : 3*n < finrank (ZMod 2)
      (fixedSpace (overgroupAction n M) (Subgroup.zpowers x)) := by omega
  have hlin := (largeOddFixedSpaceLinearity n M x hx ho hlarge).1
  have ho' : Odd (orderOf x.val) := by rwa [Subgroup.orderOf_coe]
  obtain ⟨g,hg⟩ := OddExponent.mem_congruenceImage_of_odd_of_isFixedFieldLinear n x.val hx ho' hlin
  have hgo : Odd (orderOf g) := OddExponent.odd_orderOf_of_odd_binaryCongruence n g (hg.symm ▸ ho')
  have hgn : binaryCongruence n g ≠ 1 := by
    intro hh
    exact hne (Subtype.ext (hg.symm.trans hh))
  have hd := congruenceFixed_le_five n g hgo hgn
  let U := fixedSpace (overgroupAction n M) (Subgroup.zpowers x)
  let W := congruenceFixed n g
  have he : U = W.restrictScalars (ZMod 2) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    change x.val v = v ↔ congruence n g v - v = 0
    rw [← hg]
    exact sub_eq_zero.symm
  have hF : finrank (ZMod 2) (F n) = n := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    exact (FiniteField.pow_finrank_eq_natCard 2 (F n)).trans (card_F n)
  have hb : finrank (ZMod 2) U = n * finrank (F n) W := by
    rw [he]
    exact (Module.finrank_mul_finrank (ZMod 2) (F n) W).symm.trans (by rw [hF])
  change finrank (F n) W ≤ 5 at hd
  have hle := Nat.mul_le_mul_left n hd
  change _ + finrank (ZMod 2) U = _ at hnull
  omega

/-- The estimate transports through the original faithful automizer embedding. -/
theorem odd_fixedCodim_ge_four_mul_of_equivariant
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W)
    (j : H →* binaryNormalizer n) (hj : Function.Injective j)
    (e : W ≃ₗ[ZMod 2] Space n)
    (he : ∀ a v, e (ρ a v) = overgroupAction n (binaryNormalizer n) (j a) (e v))
    (a : H) (ho : Odd (orderOf a)) (hne : a ≠ 1) :
    4*n ≤ fixedCodim ρ (Subgroup.zpowers a) := by
  rw [fixedCodim_map_equivariant ρ (overgroupAction n (binaryNormalizer n)) j e he,
    MonoidHom.map_zpowers]
  exact odd_fixedCodim_ge_four_mul n (binaryNormalizer n) (j a) (j a).property
    (ho.of_dvd_nat (orderOf_map_dvd j a)) (fun h => hne (hj (h.trans j.map_one.symm)))

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
