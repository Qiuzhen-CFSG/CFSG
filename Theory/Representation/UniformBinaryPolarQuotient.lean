module
public import Theory.Representation.UniformBinaryPolar
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Quotients of the uniform binary polar form

The kernel of any surjective pullback map lies in the radical of the
uniform off-diagonal form. That radical consists of constant vectors and
has dimension at most one. Rank-nullity therefore leaves either all n
coordinates or n−1. The source radical maps onto the target radical.

For odd n the constant line is exactly the radical: the quotient either
kills it and becomes nondegenerate, or retains it and all n dimensions.
The final theorem applies this dichotomy to an actual spanning orbit
using the uniform-pairing criterion, with no classification premise.

Source application: the normal Bender branches of Aschbacher–Smith
14.2.16, printed pp.985–986.
-/

public section
open Module
namespace UniformBinaryPolar
variable {n : ℕ}

private theorem radical_constant (x : (form n).ker) (i j : Fin n) : x.val i = x.val j := by
  have h (k : Fin n) : (∑ a, x.val a) + x.val k = 0 := by
    have h0 : form n x.val (Pi.single k 1) = 0 := by
      have hz := congrArg (fun f : Module.Dual (ZMod 2) (V n) => f (Pi.single k 1)) x.property
      exact hz
    have hform := form_apply_basis x.val k
    exact hform.symm.trans h0
  exact add_left_cancel ((h i).trans (h j).symm)

private theorem radical_finrank_le (hn : 0 < n) : finrank (ZMod 2) (form n).ker ≤ 1 := by
  let j : Fin n := ⟨0,hn⟩
  let f : (form n).ker →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj j).comp (form n).ker.subtype
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact (radical_constant x i j).trans (hxy.trans (radical_constant y j i))
  simpa using LinearMap.finrank_le_finrank_of_injective hf

private theorem ker_le_form_ker
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (B : LinearMap.BilinForm (ZMod 2) W) (f : V n →ₗ[ZMod 2] W)
    (hpull : ∀ x y, form n x y = B (f x) (f y)) :
    f.ker ≤ (form n).ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro y
  rw [LinearMap.zero_apply,hpull x y,LinearMap.mem_ker.mp hx]
  simp

private def radicalMap
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (B : LinearMap.BilinForm (ZMod 2) W)
    (f : V n →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hpull : ∀ x y, form n x y = B (f x) (f y)) :
    (form n).ker →ₗ[ZMod 2] B.ker :=
  (f.domRestrict (form n).ker).codRestrict B.ker (by
    intro x
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro y
    rw [LinearMap.zero_apply]
    obtain ⟨z,rfl⟩ := hf y
    have hr : form n x.val z = 0 := by
      have hz := congrArg (fun q : Module.Dual (ZMod 2) (V n) => q z) x.property
      exact hz
    simpa only [hpull,LinearMap.domRestrict_apply] using hr)

private theorem radicalMap_surjective
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (B : LinearMap.BilinForm (ZMod 2) W)
    (f : V n →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hpull : ∀ x y, form n x y = B (f x) (f y)) :
    Function.Surjective (radicalMap B f hf hpull) := by
  intro w
  obtain ⟨x,hx⟩ := hf w.val
  have hxr : x ∈ (form n).ker := by
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro z
    rw [LinearMap.zero_apply,hpull x z,hx]
    have hz := congrArg (fun q : Module.Dual (ZMod 2) W => q (f z)) w.property
    exact hz
  exact ⟨⟨x,hxr⟩,Subtype.ext hx⟩

/-- A surjective orbit quotient retains all but at most one dimension, and
its induced polar has radical of dimension at most one. -/
theorem quotient_dimension_and_radical_bound
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (B : LinearMap.BilinForm (ZMod 2) W)
    (f : V n →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hpull : ∀ x y, form n x y = B (f x) (f y))
    (hn : 0 < n) :
    (finrank (ZMod 2) W = n ∨ finrank (ZMod 2) W + 1 = n) ∧
      finrank (ZMod 2) B.ker ≤ 1 := by
  have hrad := radical_finrank_le (n := n) hn
  have hfker : finrank (ZMod 2) f.ker ≤ 1 :=
    (Submodule.finrank_mono (ker_le_form_ker B f hpull)).trans hrad
  have hdim := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf,finrank_top] at hdim
  have hnV : finrank (ZMod 2) (V n) = n := by simp [V]
  rw [hnV] at hdim
  exact ⟨by omega, (LinearMap.finrank_le_finrank_of_surjective
    (radicalMap_surjective B f hf hpull)).trans hrad⟩

private theorem odd_radical_finrank (hn : Odd n) :
    finrank (ZMod 2) (form n).ker = 1 := by
  have hpos : 0 < n := hn.pos
  have hr : (fun _ : Fin n => (1 : ZMod 2)) ∈ (form n).ker := by
    apply LinearMap.mem_ker.mpr
    apply (Pi.basisFun (ZMod 2) (Fin n)).ext
    intro j
    simp only [Pi.basisFun_apply,LinearMap.zero_apply]
    rw [form_apply_basis]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      hn.natCast_zmod_two]
    decide
  have hne : (form n).ker ≠ ⊥ := by
    intro hb
    rw [hb] at hr
    have he := congrFun (show (fun _ : Fin n => (1 : ZMod 2)) = 0 from hr) ⟨0,hpos⟩
    exact one_ne_zero he
  exact Nat.le_antisymm (radical_finrank_le hpos)
    (Submodule.one_le_finrank_iff.mpr hne)

/-- In odd degree the quotient either kills the constant radical, giving
a nondegenerate space of dimension n−1, or retains all n dimensions and
a one-dimensional radical. -/
theorem odd_quotient_dimension_and_radical
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (B : LinearMap.BilinForm (ZMod 2) W)
    (f : V n →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hpull : ∀ x y, form n x y = B (f x) (f y))
    (hn : Odd n) :
    (finrank (ZMod 2) W + 1 = n ∧ B.ker = ⊥) ∨
      (finrank (ZMod 2) W = n ∧ finrank (ZMod 2) B.ker = 1) := by
  have hrad := odd_radical_finrank hn
  have hker := ker_le_form_ker B f hpull
  have hfker : finrank (ZMod 2) f.ker ≤ 1 :=
    (Submodule.finrank_mono hker).trans_eq hrad
  have hdim := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf,finrank_top] at hdim
  have hnV : finrank (ZMod 2) (V n) = n := by simp [V]
  rw [hnV] at hdim
  by_cases hk : f.ker = ⊥
  · have hfi : Function.Injective f := LinearMap.ker_eq_bot.mp hk
    right
    have hz : finrank (ZMod 2) f.ker = 0 := Submodule.finrank_eq_zero.mpr hk
    refine ⟨by omega,?_⟩
    have hgi : Function.Injective (radicalMap B f hf hpull) := by
      intro x y he
      exact Subtype.ext (hfi (congrArg Subtype.val he))
    have hlo := LinearMap.finrank_le_finrank_of_injective hgi
    have hhi := LinearMap.finrank_le_finrank_of_surjective (radicalMap_surjective B f hf hpull)
    omega
  · have hdker : finrank (ZMod 2) f.ker = 1 :=
      Nat.le_antisymm hfker (Submodule.one_le_finrank_iff.mpr hk)
    have he : f.ker = (form n).ker := Submodule.eq_of_le_of_finrank_eq hker (hdker.trans hrad.symm)
    left
    refine ⟨by omega,?_⟩
    apply eq_bot_iff.mpr
    intro w hw
    obtain ⟨x,hx⟩ := radicalMap_surjective B f hf hpull ⟨w,hw⟩
    have hxker : x.val ∈ f.ker := he.symm ▸ x.property
    have hz : f x.val = 0 := LinearMap.mem_ker.mp hxker
    exact (congrArg Subtype.val hx).symm.trans hz

/-- The exact quotient dichotomy for an actual spanning orbit with uniform
pairings, without requiring a separately supplied pullback identity. -/
theorem odd_invariant_orbit_dimension_and_radical
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.IsAlt) (hne : B ≠ 0)
    (f : V n →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hp : ∀ i j i' j' : Fin n, i ≠ j → i' ≠ j' →
      B (f (Pi.single i 1)) (f (Pi.single j 1)) =
      B (f (Pi.single i' 1)) (f (Pi.single j' 1)))
    (hn : Odd n) :
    (finrank (ZMod 2) W + 1 = n ∧ B.ker = ⊥) ∨
      (finrank (ZMod 2) W = n ∧ finrank (ZMod 2) B.ker = 1) := by
  apply odd_quotient_dimension_and_radical B f hf ?_ hn
  intro x y
  exact (congrArg (fun C : LinearMap.BilinForm (ZMod 2) (V n) => C x y)
    (pullback_eq_uniform B hB hne f hf hp)).symm

end UniformBinaryPolar
