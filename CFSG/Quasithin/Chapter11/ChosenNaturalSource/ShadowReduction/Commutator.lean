module

public import CFSG.Quasithin.Chapter11.Section03
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Tactic.Group
/-!
# The literal commutator pairing in 11.3.9

For the three actual ambient subgroups W₁, W₂ and W₃, centrality of W₃
in their generated group makes the group commutator biadditive. Conjugation
by the two Cartan subgroups then makes it bilinear over the supplied common
field. Equivariance is proved from conjugation, and a nonzero paired vector
is derived from W₃ = [W₁,W₂] ≠ 1. The existing scalar obstruction therefore
excludes the source eigenvalues λ², λ and λ⁻¹.

The construction of these subgroups and their compatible field structures
in 11.3.3--8 is still required. This module does not assert Proposition
11.3.2 from its original hypotheses. In particular, no field compatibility
or eigenvalue hypothesis below is an additional hypothesis of that proposition.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Lemma 11.3.9 and the final paragraph of Proposition 11.3.2,
printed p.775. Conjugation is x*w*x⁻¹ throughout.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
variable {G : Type*} [Group G]
variable (W₁ W₂ W₃ : Subgroup G) [IsMulCommutative W₁]
  [IsMulCommutative W₂] [IsMulCommutative W₃]

private def commutatorHom
    (hc : ⁅W₁, W₂⁆ ≤ W₃)
    (hz : W₃ ≤ centralizer ((W₁ ⊔ W₂ : Subgroup G) : Set G)) :
    W₁ →* (W₂ →* W₃) where
  toFun u := {
    toFun v := ⟨⁅(u : G), (v : G)⁆, hc (commutator_mem_commutator u.property v.property)⟩
    map_one' := Subtype.ext (by simp)
    map_mul' v w := by
      apply Subtype.ext
      change ⁅(u : G), (v : G) * w⁆ = ⁅(u : G), (v : G)⁆ * ⁅(u : G), (w : G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hh := hz (hc (commutator_mem_commutator u.property w.property))
        v (show (v : G) ∈ W₁ ⊔ W₂ from (le_sup_right : W₂ ≤ W₁ ⊔ W₂) v.property)
      change (v : G) * ⁅(u : G), (w : G)⁆ = ⁅(u : G), (w : G)⁆ * v at hh
      rw [mul_assoc ⁅(u : G), (v : G)⁆, hh]
      group }
  map_one' := by
    apply MonoidHom.ext
    intro v
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply MonoidHom.ext
    intro w
    apply Subtype.ext
    change ⁅(u : G) * v, (w : G)⁆ = ⁅(u : G), (w : G)⁆ * ⁅(v : G), (w : G)⁆
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hh := hz (hc (commutator_mem_commutator v.property w.property))
      u (show (u : G) ∈ W₁ ⊔ W₂ from (le_sup_left : W₁ ≤ W₁ ⊔ W₂) u.property)
    change (u : G) * ⁅(v : G), (w : G)⁆ = ⁅(v : G), (w : G)⁆ * u at hh
    rw [hh, mul_inv_cancel_right]
    exact congrArg Subtype.val (mul_comm
      (⟨⁅(v : G), (w : G)⁆, hc (commutator_mem_commutator v.property w.property)⟩ : W₃)
      (⟨⁅(u : G), (w : G)⁆, hc (commutator_mem_commutator u.property w.property)⟩ : W₃))

private def commutatorAdd
    (hc : ⁅W₁, W₂⁆ ≤ W₃)
    (hz : W₃ ≤ centralizer ((W₁ ⊔ W₂ : Subgroup G) : Set G)) :
    Additive W₁ →+ (Additive W₂ →+ Additive W₃) where
  toFun u := (commutatorHom W₁ W₂ W₃ hc hz u.toMul).toAdditive
  map_zero' := by
    apply AddMonoidHom.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [commutatorHom]
  map_add' u v := by
    apply AddMonoidHom.ext
    intro w
    exact congrArg (fun f : W₂ →* W₃ => Additive.ofMul (f w.toMul))
      (map_mul (commutatorHom W₁ W₂ W₃ hc hz) u.toMul v.toMul)

variable {F : Type*} [Field F]

/-- Conjugation by the actual ambient element acts by the indicated scalar. -/
@[expose] def ScalarConjugation (W : Subgroup G) [IsMulCommutative W]
    [Module F (Additive W)] (x : G) (a : F) : Prop :=
  ∀ w : Additive W, (MulAut.conj x) (w.toMul : G) = ((a • w).toMul : G)

/-- Conjugation on the additive group of the actual invariant subgroup. -/
@[expose] def conjugateVector (W X : Subgroup G)
    (hX : X ≤ normalizer (W : Set G)) (x : X) : Additive W → Additive W :=
  (W.normalizerMonoidHom ⟨x, hX x.property⟩).toMonoidHom.toAdditive

variable [Module F (Additive W₁)] [Module F (Additive W₂)] [Module F (Additive W₃)]

/-- The literal group commutator becomes F-bilinear from the two Cartan
scalar symmetries. No pairing or equivariance is assumed. -/
theorem exists_bilinear_commutator
    (X : Subgroup G) (hc : ⁅W₁, W₂⁆ ≤ W₃)
    (hz : W₃ ≤ centralizer ((W₁ ⊔ W₂ : Subgroup G) : Set G))
    (hX₁ : X ≤ normalizer (W₁ : Set G))
    (hX₂ : X ≤ normalizer (W₂ : Set G))
    (hX₃ : X ≤ normalizer (W₃ : Set G))
    (hleft : ∀ a : F, a ≠ 0 → ∃ x ∈ X,
      ScalarConjugation W₁ x a ∧ ScalarConjugation W₂ x (1 : F) ∧
      ScalarConjugation W₃ x a)
    (hright : ∀ a : F, a ≠ 0 → ∃ x ∈ X,
      ScalarConjugation W₁ x (1 : F) ∧ ScalarConjugation W₂ x a ∧
      ScalarConjugation W₃ x a) :
    ∃ b : Additive W₁ →ₗ[F] Additive W₂ →ₗ[F] Additive W₃,
      (∀ u v, ((b u v).toMul : G) = ⁅(u.toMul : G), (v.toMul : G)⁆) ∧
      (∀ x : X, ∀ u v,
        b (conjugateVector W₁ X hX₁ x u) (conjugateVector W₂ X hX₂ x v) =
          conjugateVector W₃ X hX₃ x (b u v)) := by
  let c := commutatorAdd W₁ W₂ W₃ hc hz
  let r₁ := conjugateVector W₁ X hX₁
  let r₂ := conjugateVector W₂ X hX₂
  let r₃ := conjugateVector W₃ X hX₃
  have heq (x : X) (u : Additive W₁) (v : Additive W₂) :
      c (r₁ x u) (r₂ x v) = r₃ x (c u v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (map_commutatorElement (MulAut.conj (x : G)) (u.toMul : G) (v.toMul : G)).symm
  have scalar (W : Subgroup G) [IsMulCommutative W] [Module F (Additive W)]
      (hX : X ≤ normalizer (W : Set G)) (x : X) (a : F)
      (ha : ScalarConjugation W (x : G) a) :
      ∀ w, conjugateVector W X hX x w = a • w := by
    intro w
    apply Additive.toMul.injective
    exact Subtype.ext (ha w)
  obtain ⟨b, hb⟩ := ScalarEquivariantBilinear.exists_bilinear_of_scalar_actions
    c r₁ r₂ r₃ heq (fun a ha => by
      obtain ⟨x, hx, h₁, h₂, h₃⟩ := hleft a ha
      exact ⟨⟨x, hx⟩, scalar W₁ hX₁ ⟨x, hx⟩ a h₁,
        by simpa using scalar W₂ hX₂ ⟨x, hx⟩ 1 h₂,
        scalar W₃ hX₃ ⟨x, hx⟩ a h₃⟩) (fun a ha => by
      obtain ⟨x, hx, h₁, h₂, h₃⟩ := hright a ha
      exact ⟨⟨x, hx⟩, by simpa using scalar W₁ hX₁ ⟨x, hx⟩ 1 h₁,
        scalar W₂ hX₂ ⟨x, hx⟩ a h₂, scalar W₃ hX₃ ⟨x, hx⟩ a h₃⟩)
  refine ⟨b, ?_, ?_⟩
  · intro u v
    rw [hb]
    rfl
  · intro x u v
    simpa only [hb] using heq x u v
/-- The terminal shadow obstruction, now using actual ambient commutators.
The nonzero value is derived from W₃ = [W₁,W₂] ≠ 1. -/
theorem false_of_cartan_commutator [CharP F 2]
    (X : Subgroup G) (hc : ⁅W₁, W₂⁆ = W₃) (hne : W₃ ≠ ⊥)
    (hz : W₃ ≤ centralizer ((W₁ ⊔ W₂ : Subgroup G) : Set G))
    (hX₁ : X ≤ normalizer (W₁ : Set G))
    (hX₂ : X ≤ normalizer (W₂ : Set G))
    (hX₃ : X ≤ normalizer (W₃ : Set G))
    (hleft : ∀ a : F, a ≠ 0 → ∃ x ∈ X,
      ScalarConjugation W₁ x a ∧ ScalarConjugation W₂ x (1 : F) ∧
      ScalarConjugation W₃ x a)
    (hright : ∀ a : F, a ≠ 0 → ∃ x ∈ X,
      ScalarConjugation W₁ x (1 : F) ∧ ScalarConjugation W₂ x a ∧
      ScalarConjugation W₃ x a)
    {n : ℕ} (hn : 1 < n) {a : F} (ha : a ≠ 0)
    (horder : orderOf a = 2 ^ n - 1) (y : X)
    (hy₁ : ScalarConjugation W₁ (y : G) (a ^ 2))
    (hy₂ : ScalarConjugation W₂ (y : G) a)
    (hy₃ : ScalarConjugation W₃ (y : G) a⁻¹) : False := by
  obtain ⟨b, hb, heq⟩ := exists_bilinear_commutator W₁ W₂ W₃ X hc.le hz
    hX₁ hX₂ hX₃ hleft hright
  obtain ⟨u, v, huv⟩ : ∃ u : Additive W₁, ∃ v : Additive W₂, b u v ≠ 0 := by
    by_contra! hall
    apply hne
    apply bot_unique
    rw [← hc]
    apply commutator_le.mpr
    intro u hu v hv
    have he := hb (Additive.ofMul ⟨u, hu⟩) (Additive.ofMul ⟨v, hv⟩)
    rw [hall] at he
    exact he.symm
  apply Section03.no_shadow_eigenvalue_configuration b
    (conjugateVector W₁ X hX₁ y) (conjugateVector W₂ X hX₂ y)
    (conjugateVector W₃ X hX₃ y) (heq y) hn ha horder huv
  · apply Additive.toMul.injective
    exact Subtype.ext (hy₁ u)
  · apply Additive.toMul.injective
    exact Subtype.ext (hy₂ v)
  · apply Additive.toMul.injective
    exact Subtype.ext (hy₃ (b u v))
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction
