module

public import Theory.GroupTheory.NormalizerComplementAction
public import Mathlib.FieldTheory.Finite.Basic

/-!
# A normalizer complement from additive and multiplicative coordinates

An embedded additive field group and an embedded group of field units give
an internal cyclic complement when scalar multiplication is their literal
conjugation action and their products cover the full normalizer. Evaluating
at the root parameter one proves faithfulness; division proves transitivity
on the nonidentity elements.

This is the coordinate construction used in the PGL₂(9) calculation underlying
Aschbacher, *Sporadic Groups* (1994), 47.3(3), printed p.262.
-/

public section

open Subgroup
open scoped Pointwise
noncomputable section
namespace GorensteinWalter.PGL2NineSylowNormalizer
variable {K G : Type*} [Field K] [Finite K] [Group G]

lemma action_of_coordinates
    (r : Multiplicative K →* G) (t : Kˣ →* G)
    (hr : Function.Injective r) (ht : Function.Injective t)
    (hc : ∀ (k : Kˣ) (x : K), t k * r (Multiplicative.ofAdd x) * (t k)⁻¹ =
      r (Multiplicative.ofAdd ((k : K) * x)))
    (hf : ∀ g ∈ normalizer (r.range : Set G), ∃ x k, r x * t k = g) :
    Nonempty (NormalizerComplementAction r.range (Nat.card K - 1)) := by
  classical
  have hn (k : Kˣ) : t k ∈ normalizer (r.range : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Multiplicative.ofAdd ((k : K) * x.toAdd), (hc k x.toAdd).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨Multiplicative.ofAdd ((↑k⁻¹ : K) * x.toAdd), ?_⟩
      rw [← hc]
      change t k⁻¹ * r x * (t k⁻¹)⁻¹ = g
      rw [hx, map_inv]
      simp [mul_assoc]
  let tn : Kˣ →* normalizer (r.range : Set G) := t.codRestrict _ hn
  let T := tn.range
  let e : Kˣ ≃* T := MulEquiv.ofBijective tn.rangeRestrict
    ⟨fun a b h => ht (congrArg (fun x : T => ((x : normalizer (r.range : Set G)) : G)) h),
      tn.rangeRestrict_surjective⟩
  have re (x : K) : r (Multiplicative.ofAdd x) ∈ r.range := ⟨_, rfl⟩
  have heq (k : Kˣ) (x : K) :
      r.range.normalizerMonoidHom (e k) ⟨r (Multiplicative.ofAdd x), re x⟩ =
        ⟨r (Multiplicative.ofAdd ((k : K) * x)), re _⟩ := by
    apply Subtype.ext
    exact hc k x
  have hcard : Nat.card T = Nat.card K - 1 := by
    rw [← Nat.card_congr e.toEquiv]
    let := Fintype.ofFinite K
    simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  refine ⟨⟨T, e.isCyclic.mp inferInstance, hcard, ?_, ?_, ?_⟩⟩
  · apply isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_def]
      intro g hg hgT
      obtain ⟨k, hk⟩ := hgT
      obtain ⟨x, hx⟩ := hg
      change r x = (g : G) at hx
      have hcomm : t k * r (Multiplicative.ofAdd (1 : K)) * (t k)⁻¹ =
          r (Multiplicative.ofAdd (1 : K)) := by
        have hkg : t k = (g : G) := congrArg Subtype.val hk
        rw [hkg, ← hx]
        rw [← map_mul, mul_comm x, map_mul]
        simp [mul_assoc]
      rw [hc] at hcomm
      have hk1 : k = 1 := Units.ext (by
        simpa using congrArg Multiplicative.toAdd (hr hcomm))
      apply Subtype.ext
      change (g : G) = 1
      rw [← congrArg Subtype.val hk, hk1, map_one]
      rfl
    · rw [Set.eq_univ_iff_forall]
      intro g
      obtain ⟨x, k, h⟩ := hf g g.property
      refine ⟨⟨r x, r.range.le_normalizer ⟨x, rfl⟩⟩, ?_, tn k, ⟨k, rfl⟩, ?_⟩
      · exact ⟨x, rfl⟩
      · exact Subtype.ext h
  · intro b d h
    obtain ⟨k, rfl⟩ := e.surjective b
    obtain ⟨l, rfl⟩ := e.surjective d
    apply congrArg e
    apply Units.ext
    have h' := congrArg (fun a : MulAut r.range =>
      a ⟨r (Multiplicative.ofAdd (1 : K)), re 1⟩) h
    change r.range.normalizerMonoidHom (e k) _ =
      r.range.normalizerMonoidHom (e l) _ at h'
    rw [heq, heq] at h'
    simpa using congrArg Multiplicative.toAdd (hr (congrArg Subtype.val h'))
  · intro u v hu hv
    obtain ⟨x, hx⟩ := u.property
    obtain ⟨y, hy⟩ := v.property
    have hx0 : x.toAdd ≠ 0 := by
      intro hx0
      apply hu
      apply Subtype.ext
      rw [← hx, show x = 1 from Multiplicative.toAdd.injective hx0, map_one]
      rfl
    have hy0 : y.toAdd ≠ 0 := by
      intro hy0
      apply hv
      apply Subtype.ext
      rw [← hy, show y = 1 from Multiplicative.toAdd.injective hy0, map_one]
      rfl
    let k : Kˣ := Units.mk0 (y.toAdd / x.toAdd) (div_ne_zero hy0 hx0)
    refine ⟨e k, ?_⟩
    apply Subtype.ext
    change t k * (u : G) * (t k)⁻¹ = (v : G)
    rw [← hx, ← hy]
    change t k * r (Multiplicative.ofAdd x.toAdd) * (t k)⁻¹ = r y
    rw [hc]
    congr 1
    apply Multiplicative.toAdd.injective
    exact div_mul_cancel₀ y.toAdd hx0
end GorensteinWalter.PGL2NineSylowNormalizer
