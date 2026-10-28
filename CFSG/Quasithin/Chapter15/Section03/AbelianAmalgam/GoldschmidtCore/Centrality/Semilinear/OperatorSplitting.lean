module
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.LinearAlgebra.Prod
/-!
# The binary splitting for an inverted cubic operator

For the bad-character application, β is conjugation by a nontrivial cubic
and τ is conjugation by an element of O₂(H) outside the character kernel.
Their relations β²+β+1=0, τ²=1 and τβ=β²τ imply
Fix(τ)=im(τ+1) and X=Fix(τ)⊕β Fix(τ). The explicit map is (u,v)↦u+βv.
In particular, an operator commuting with β is determined by its restriction
to Fix(τ). These facts hold in arbitrary dimension.

This extends the dimension-independent calculation used privately in
Theory.Representation.InvertedThreeCentralizer. The actual ambient action
relations must be supplied before applying this module; the order-sixteen
endpoint of that module is not used.

Source application: the repaired semilinear branch of Aschbacher–Smith
15.3.68, combined manuscript (1 March 2004), printed pp.1154–1155.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]

private theorem add_self_zero (x : X) : x + x = 0 := by
  have h := @two_smul (ZMod 2) X _ _ _ x
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_smul] at h
  exact h.symm

private theorem fixed_decomposition (β τ : Module.End (ZMod 2) X)
    (hβ : β ^ 2 + β + 1 = 0) (hτ : τ * τ = 1)
    (hinv : τ * β = β ^ 2 * τ) :
    ∀ x : X, ∃ u v : X, τ u = u ∧ τ v = v ∧ x = u + β v := by
  have hquad (x : X) : β (β x) + β x + x = 0 := LinearMap.congr_fun hβ x
  have htt (x : X) : τ (τ x) = x := LinearMap.congr_fun hτ x
  have hinv' (x : X) : τ (β x) = β (β (τ x)) := LinearMap.congr_fun hinv x
  have hsum (x : X) : β (β x) + β x = x := by
    exact add_right_cancel (show (β (β x) + β x) + x = x + x by
      rw [hquad, add_self_zero])
  intro x
  let v := x + τ x
  have hv : τ v = v := by simp [v, htt, add_comm]
  refine ⟨x + β v, v, ?_, hv, ?_⟩
  · rw [map_add, hinv', hv]
    have hh : β (β v) = v + β v := by
      apply add_right_cancel (b := β v)
      rw [hsum]
      simp only [add_assoc, add_self_zero, add_zero]
    rw [hh]
    dsimp [v]
    calc
      τ x + (x + τ x + β (x + τ x)) =
          x + β (x + τ x) + (τ x + τ x) := by abel
      _ = x + β (x + τ x) := by rw [add_self_zero, add_zero]
  · rw [add_assoc, add_self_zero, add_zero]

/-- The sum of the fixed subspace and its cubic translate, with its literal formula. -/
@[expose] def fixedPairMap (β τ : Module.End (ZMod 2) X) :
    (LinearMap.ker (τ - 1) × LinearMap.ker (τ - 1)) →ₗ[ZMod 2] X where
  toFun uv := uv.1 + β uv.2
  map_add' := by intros; simp; abel
  map_smul' := by intros; simp

/-- The cubic/involution relations prove both spanning and trivial intersection. -/
theorem fixedPairMap_bijective (β τ : Module.End (ZMod 2) X)
    (hβ : β ^ 2 + β + 1 = 0) (hτ : τ * τ = 1)
    (hinv : τ * β = β ^ 2 * τ) : Function.Bijective (fixedPairMap β τ) := by
  have hW (x : LinearMap.ker (τ - 1)) : τ (x : X) = x := by
    have hx := x.property
    change τ (x : X) - (x : X) = 0 at hx
    exact sub_eq_zero.mp hx
  constructor
  · apply (injective_iff_map_eq_zero (fixedPairMap β τ).toAddMonoidHom).2
    rintro ⟨u,v⟩ huv
    have hquad : β (β (v : X)) + β (v : X) + (v : X) = 0 :=
      LinearMap.congr_fun hβ v
    have hbtv : τ (β (v : X)) = β (β (v : X)) := by
      have h := LinearMap.congr_fun hinv (v : X)
      change τ (β (v : X)) = β (β (τ (v : X))) at h
      simpa only [hW] using h
    have htuv := congrArg τ huv
    change τ ((u : X) + β (v : X)) = τ 0 at htuv
    rw [map_add, map_zero, hW, hbtv] at htuv
    change (u : X) + β (v : X) = 0 at huv
    have hbu : β (v : X) = u := by
      exact add_left_cancel (show (u : X) + β (v : X) = (u : X) + u by
        rw [huv, add_self_zero])
    have hbb : β (β (v : X)) = u := by
      exact add_left_cancel (show (u : X) + β (β (v : X)) = (u : X) + u by
        rw [htuv, add_self_zero])
    have hvzero : (v : X) = 0 := by
      rw [hbb, hbu, add_self_zero, zero_add] at hquad
      exact hquad
    have huzero : (u : X) = 0 := by simpa [hvzero] using hbu.symm
    exact Prod.ext (Subtype.ext huzero) (Subtype.ext hvzero)
  · intro x
    obtain ⟨u,v,hu,hv,hx⟩ := fixed_decomposition β τ hβ hτ hinv x
    refine ⟨(⟨u,?_⟩,⟨v,?_⟩),hx.symm⟩
    · change τ u - u = 0
      rw [hu,sub_self]
    · change τ v - v = 0
      rw [hv,sub_self]

/-- The explicit two-summand splitting, without a dimension or cardinality assumption. -/
@[expose] noncomputable def fixedPairEquiv (β τ : Module.End (ZMod 2) X)
    (hβ : β ^ 2 + β + 1 = 0) (hτ : τ * τ = 1)
    (hinv : τ * β = β ^ 2 * τ) :
    (LinearMap.ker (τ - 1) × LinearMap.ker (τ - 1)) ≃ₗ[ZMod 2] X :=
  LinearEquiv.ofBijective (fixedPairMap β τ) (fixedPairMap_bijective β τ hβ hτ hinv)

/-- The splitting sends (u,v) to u+βv. -/
theorem fixedPairEquiv_apply (β τ : Module.End (ZMod 2) X)
    (hβ : β ^ 2 + β + 1 = 0) (hτ : τ * τ = 1)
    (hinv : τ * β = β ^ 2 * τ) (u v : LinearMap.ker (τ - 1)) :
    fixedPairEquiv β τ hβ hτ hinv (u,v) = (u : X) + β (v : X) := rfl

/-- The involution fixed space equals its displacement image. -/
theorem fixed_eq_displacement_range (β τ : Module.End (ZMod 2) X)
    (hβ : β ^ 2 + β + 1 = 0) (hτ : τ * τ = 1)
    (hinv : τ * β = β ^ 2 * τ) : LinearMap.ker (τ - 1) = LinearMap.range (τ + 1) := by
  apply le_antisymm
  · intro w hw
    have htw : τ w = w := sub_eq_zero.mp hw
    refine ⟨β w, ?_⟩
    have htw' : τ (β w) = β (β w) := by
      have h := LinearMap.congr_fun hinv w
      change τ (β w) = β (β (τ w)) at h
      rw [htw] at h
      exact h
    have hquad : β (β w) + β w + w = 0 := LinearMap.congr_fun hβ w
    change τ (β w) + β w = w
    rw [htw']
    exact add_right_cancel (show (β (β w) + β w) + w = w + w by rw [hquad, add_self_zero])
  · rintro _ ⟨x,rfl⟩
    change τ (τ x + x) - (τ x + x) = 0
    have htx : τ (τ x) = x := LinearMap.congr_fun hτ x
    rw [map_add,htx,add_comm x,sub_self]

/-- Commuting with β makes restriction to the fixed subspace determine an operator. -/
theorem commuting_operator_ext (β τ a c : Module.End (ZMod 2) X)
    (hβ : β ^ 2 + β + 1 = 0) (hτ : τ * τ = 1)
    (hinv : τ * β = β ^ 2 * τ)
    (ha : a * β = β * a) (hc : c * β = β * c)
    (he : ∀ x, τ x = x → a x = c x) : a = c := by
  ext x
  obtain ⟨u,v,hu,hv,rfl⟩ := fixed_decomposition β τ hβ hτ hinv x
  have hav : a (β v) = β (a v) := LinearMap.congr_fun ha v
  have hcv : c (β v) = β (c v) := LinearMap.congr_fun hc v
  rw [map_add,map_add,hav,hcv,he u hu,he v hv]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
