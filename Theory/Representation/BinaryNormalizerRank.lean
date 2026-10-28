module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Excluding binary transvections from a linear normalizer

If a map of displacement rank at most one normalizes a subgroup, each of its
commutators with the subgroup has displacement rank at most two. A lower bound
of three on nonidentity subgroup elements therefore makes the map centralize
the subgroup. Over F₂ its one-dimensional displacement space would then be
pointwise fixed. Thus a trivial common fixed space excludes a transvection in
the normalizer, without any assertion that the normalizer is semilinear.

This is the linear normalizer argument used for the natural Ω₄⁺(4) module in
Aschbacher–Smith, 13.8.16(1), printed pp.952–953 (PDF pp.969–970).
-/

@[expose] public section
namespace Representation.BinaryNormalizerRank
open Module
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
  [FiniteDimensional k W]

/-- The displacement of a linear automorphism. -/
def displacement (g : W ≃ₗ[k] W) : W →ₗ[k] W := g.toLinearMap - LinearMap.id

/-- Displacement rank is subadditive under multiplication. -/
theorem rank_mul_le (g h : W ≃ₗ[k] W) :
    finrank k (LinearMap.range (displacement (g * h))) ≤
      finrank k (LinearMap.range (displacement g)) +
      finrank k (LinearMap.range (displacement h)) := by
  have he : displacement (g * h) =
      (displacement g).comp h.toLinearMap + displacement h := by
    ext v
    simp [displacement]
  rw [he]
  have hr := Submodule.finrank_mono
    (LinearMap.range_add_le ((displacement g).comp h.toLinearMap) (displacement h))
  have hs := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range ((displacement g).comp h.toLinearMap))
    (LinearMap.range (displacement h))
  rw [LinearMap.range_comp_of_range_eq_top _ h.range] at hr hs
  exact hr.trans hs

omit [FiniteDimensional k W] in
/-- Inversion preserves displacement rank. -/
theorem rank_inv (g : W ≃ₗ[k] W) :
    finrank k (LinearMap.range (displacement g⁻¹)) =
      finrank k (LinearMap.range (displacement g)) := by
  have he : displacement g⁻¹ = -((displacement g).comp g.symm.toLinearMap) := by
    ext v
    simp [displacement]
  rw [he, LinearMap.range_neg, LinearMap.range_comp_of_range_eq_top _ g.symm.range]

omit [FiniteDimensional k W] in
/-- Conjugation preserves displacement rank. -/
theorem rank_conj (g h : W ≃ₗ[k] W) :
    finrank k (LinearMap.range (displacement (g * h * g⁻¹))) =
      finrank k (LinearMap.range (displacement h)) := by
  have he : displacement (g * h * g⁻¹) =
      g.toLinearMap.comp ((displacement h).comp g.symm.toLinearMap) := by
    ext v
    simp [displacement]
  rw [he, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ g.symm.range]
  exact (Submodule.equivMapOfInjective g.toLinearMap g.injective
    (LinearMap.range (displacement h))).finrank_eq.symm

/-- A normalizing map of displacement rank at most one centralizes a subgroup
whose nonidentity elements have displacement rank at least three. -/
theorem commutes_of_normalizes_of_rank_gap (K : Subgroup (W ≃ₗ[k] W))
    (hgap : ∀ g ∈ K, g ≠ 1 → 3 ≤ finrank k (LinearMap.range (displacement g)))
    (t : W ≃ₗ[k] W) (hn : t ∈ Subgroup.normalizer (K : Set (W ≃ₗ[k] W)))
    (ht : finrank k (LinearMap.range (displacement t)) ≤ 1) :
    ∀ g ∈ K, t * g = g * t := by
  intro g hg
  have hm : t * g * t⁻¹ * g⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp hn g).mp hg) (K.inv_mem hg)
  have hr := rank_mul_le t (g * t⁻¹ * g⁻¹)
  rw [rank_conj, rank_inv] at hr
  have he : t * g * t⁻¹ * g⁻¹ = 1 := by
    by_contra hh
    have hl := hgap _ hm hh
    have ha : t * (g * t⁻¹ * g⁻¹) = t * g * t⁻¹ * g⁻¹ := by group
    rw [ha] at hr
    omega
  have := congrArg (fun a : W ≃ₗ[k] W => a * (g * t)) he
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, one_mul] using this

section Binary
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- A binary group with no common nonzero fixed vector and no nonidentity
element of displacement rank below three has no transvections in its normalizer. -/
theorem normalizer_no_rank_one (K : Subgroup (U ≃ₗ[ZMod 2] U))
    (hgap : ∀ g ∈ K, g ≠ 1 →
      3 ≤ finrank (ZMod 2) (LinearMap.range (displacement g)))
    (hfixed : ∀ v : U, (∀ g ∈ K, g v = v) → v = 0)
    (t : U ≃ₗ[ZMod 2] U) (hn : t ∈ Subgroup.normalizer (K : Set (U ≃ₗ[ZMod 2] U))) :
    finrank (ZMod 2) (LinearMap.range (displacement t)) ≠ 1 := by
  intro ht
  have hcomm := commutes_of_normalizes_of_rank_gap K hgap t hn ht.le
  let R := LinearMap.range (displacement t)
  have hR : R ≠ ⊥ := by
    intro hh
    have : finrank (ZMod 2) R = 0 := by rw [hh]; simp
    have htR : finrank (ZMod 2) R = 1 := ht
    omega
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff R).mp hR
  apply hv0
  apply hfixed v
  intro g hg
  have hgv : g v ∈ R := by
    obtain ⟨w, rfl⟩ := hv
    refine ⟨g w, ?_⟩
    have hc := LinearEquiv.congr_fun (hcomm g hg) w
    simpa [displacement] using congrArg (fun a : U => a - g w) hc
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one ht
    (show (⟨v, hv⟩ : R) ≠ 0 from fun he => hv0 (congrArg Subtype.val he))
    (⟨g v, hgv⟩ : R)
  have hc' : c • v = g v := congrArg Subtype.val hc
  fin_cases c
  · change (0 : ZMod 2) • v = g v at hc'
    simp only [zero_smul] at hc'
    exact False.elim (hv0 (g.injective (hc'.symm.trans g.map_zero.symm)))
  · change (1 : ZMod 2) • v = g v at hc'
    simpa only [one_smul] using hc'.symm

end Binary
end Representation.BinaryNormalizerRank
