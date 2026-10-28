module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Eigenspaces

/-!
# Bilinearity from the two compatible conjugation actions

For the actual ambient commutator, [u,v] is u minus its v-conjugate in V,
and the u-conjugate of v minus v in P. Thus the first expression is
linear in u and the second is linear in v. Agreement of the two scalar
structures on P intersect V makes both expressions take values in the
same field subspace. This constructs the literal bilinear commutator
without needing separate Cartan scalar families. Conjugation equivariance
then gives the terminal eigenvalue obstruction.

Source: Aschbacher--Smith, 11.3.8–9 and the final paragraph of Proposition
11.3.2, printed p.775. This is a direct proof of the needed bilinearity
using the two full field-linear actions already available after 11.3.8.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
variable {G F : Type*} [Group G] [Field F] {P V L Y : Subgroup G}
  [IsMulCommutative P] [IsMulCommutative V]
  [Module F (Additive P)] [Module F (Additive V)]

/-- The inclusion of an actual field subgroup into its ambient module. -/
def subgroupFieldInclusion (U : Submodule F (Additive P)) :
    let := subgroupFieldModule U rfl
    Additive (ambientSubgroup U) →ₗ[F] Additive P := by
  let := subgroupFieldModule U rfl
  exact U.subtype.comp ((subgroupFieldCoordinates U rfl).linearEquiv F).toLinearMap

/-- Compatible scalars make the commutator bilinear directly: its displacement
formula in V is linear in the first argument, and its formula in P is linear
in the second argument. Both formulas use literal ambient conjugation. -/
theorem exists_bilinear_commutator_of_linear_actions
    (hcommon : ∀ (a : F) (b : Additive (P ⊓ V : Subgroup G)),
      ((a • (inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
      ((a • (inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G))
    (τ : Representation F L (Additive V))
    (hτ : ∀ (l : L) (v : Additive V),
      ((τ l v).toMul : G) = MulAut.conj (l : G) (v.toMul : G))
    (σ : Representation F Y (Additive P))
    (hσ : ∀ (y : Y) (p : Additive P),
      ((σ y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G))
    (U₁ : Submodule F (Additive V)) (U₂ C : Submodule F (Additive P))
    (h₁ : ambientSubgroup U₁ ≤ Y) (h₂ : ambientSubgroup U₂ ≤ L)
    (hc : ambientSubgroup C = ⁅ambientSubgroup U₁,ambientSubgroup U₂⁆)
    (hCV : ambientSubgroup C ≤ V) :
    let := subgroupFieldModule U₁ rfl
    let := subgroupFieldModule U₂ rfl
    let := subgroupFieldModule C rfl
    ∃ b : Additive (ambientSubgroup U₁) →ₗ[F]
        Additive (ambientSubgroup U₂) →ₗ[F] Additive (ambientSubgroup C),
      ∀ u v, ((b u v).toMul : G) = ⁅(u.toMul : G),(v.toMul : G)⁆ := by
  let := subgroupFieldModule U₁ rfl
  let := subgroupFieldModule U₂ rfl
  let := subgroupFieldModule C rfl
  let i₁ := subgroupFieldInclusion U₁
  let i₂ := subgroupFieldInclusion U₂
  let iP := subgroupFieldInclusion C
  let iV : Additive (ambientSubgroup C) →ₗ[F] Additive V := {
    toFun := (inclusion hCV).toAdditive
    map_add' := map_add _
    map_smul' := by
      intro a c
      apply Additive.toMul.injective
      apply Subtype.ext
      exact subgroupFieldModule_smul_common hcommon C rfl hCV a c }
  have hPinj : Function.Injective iP := by
    intro a b hab
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun p : Additive P => (p.toMul : G)) hab
  have hVinj : Function.Injective iV := by
    intro a b hab
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun v : Additive V => (v.toMul : G)) hab
  let c : Additive (ambientSubgroup U₁) → Additive (ambientSubgroup U₂) →
      Additive (ambientSubgroup C) := fun u v => Additive.ofMul
        ⟨⁅(u.toMul : G),(v.toMul : G)⁆,
          hc.symm ▸ commutator_mem_commutator u.toMul.property v.toMul.property⟩
  have hp (u : Additive (ambientSubgroup U₁)) (v : Additive (ambientSubgroup U₂)) :
      iP (c u v) = σ ⟨u.toMul,h₁ u.toMul.property⟩ (i₂ v) - i₂ v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [sub_eq_add_neg]
    change ⁅(u.toMul : G),(v.toMul : G)⁆ =
      ((σ ⟨u.toMul,h₁ u.toMul.property⟩ (i₂ v)).toMul : G) * (v.toMul : G)⁻¹
    rw [hσ]
    rfl
  have hv (u : Additive (ambientSubgroup U₁)) (v : Additive (ambientSubgroup U₂)) :
      iV (c u v) = i₁ u - τ ⟨v.toMul,h₂ v.toMul.property⟩ (i₁ u) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [sub_eq_add_neg]
    change ⁅(u.toMul : G),(v.toMul : G)⁆ =
      (u.toMul : G) * ((τ ⟨v.toMul,h₂ v.toMul.property⟩ (i₁ u)).toMul : G)⁻¹
    rw [hτ]
    change ⁅(u.toMul : G),(v.toMul : G)⁆ =
      (u.toMul : G) * (MulAut.conj (v.toMul : G) (u.toMul : G))⁻¹
    simp only [commutatorElement_def, MulAut.conj_apply]
    group
  refine ⟨{
    toFun := fun u => {
      toFun := c u
      map_add' := by
        intro v w
        apply hPinj
        simp only [hp,map_add]
        abel
      map_smul' := by
        intro a v
        apply hPinj
        simp only [hp,map_smul,smul_sub,RingHom.id_apply] }
    map_add' := by
      intro u w
      apply LinearMap.ext
      intro v
      apply hVinj
      change iV (c (u+w) v) = iV (c u v + c w v)
      simp only [hv,map_add]
      abel
    map_smul' := by
      intro a u
      apply LinearMap.ext
      intro v
      apply hVinj
      change iV (c (a • u) v) = iV (a • c u v)
      simp only [hv,map_smul,smul_sub] },fun _ _ => rfl⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan


namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
variable {G F : Type*} [Group G] [Field F] [CharP F 2] {P V L Y X : Subgroup G}
  [IsMulCommutative P] [IsMulCommutative V]
  [Module F (Additive P)] [Module F (Additive V)]

/-- The literal conjugation-equivariant commutator excludes the terminal source
weights whenever both original ambient actions are linear over compatible fields. -/
theorem false_of_compatible_linear_actions
    (hcommon : ∀ (a : F) (b : Additive (P ⊓ V : Subgroup G)),
      ((a • (inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
      ((a • (inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G))
    (τ : Representation F L (Additive V))
    (hτ : ∀ (l : L) (v : Additive V),
      ((τ l v).toMul : G) = MulAut.conj (l : G) (v.toMul : G))
    (σ : Representation F Y (Additive P))
    (hσ : ∀ (y : Y) (p : Additive P),
      ((σ y p).toMul : G) = MulAut.conj (y : G) (p.toMul : G))
    (U₁ : Submodule F (Additive V)) (U₂ C : Submodule F (Additive P))
    (h₁ : ambientSubgroup U₁ ≤ Y) (h₂ : ambientSubgroup U₂ ≤ L)
    (hc : ambientSubgroup C = ⁅ambientSubgroup U₁,ambientSubgroup U₂⁆)
    (hCV : ambientSubgroup C ≤ V) (hne : ambientSubgroup C ≠ ⊥)
    (hn₁ : X ≤ normalizer (ambientSubgroup U₁ : Set G))
    (hn₂ : X ≤ normalizer (ambientSubgroup U₂ : Set G))
    {n : ℕ} (hn : 1 < n) {a : F} (ha : a ≠ 0)
    (horder : orderOf a = 2^n-1) (y : X) :
    let := subgroupFieldModule U₁ rfl
    let := subgroupFieldModule U₂ rfl
    let := subgroupFieldModule C rfl
    ScalarConjugation (ambientSubgroup U₁) (y : G) (a^2) →
    ScalarConjugation (ambientSubgroup U₂) (y : G) a →
    ScalarConjugation (ambientSubgroup C) (y : G) a⁻¹ → False := by
  let := subgroupFieldModule U₁ rfl
  let := subgroupFieldModule U₂ rfl
  let := subgroupFieldModule C rfl
  dsimp only
  intro hy₁ hy₂ hy₃
  obtain ⟨b,hb⟩ := exists_bilinear_commutator_of_linear_actions hcommon τ hτ σ hσ
    U₁ U₂ C h₁ h₂ hc hCV
  have hn₃ : X ≤ normalizer (ambientSubgroup C : Set G) :=
    hc.symm ▸ normalizes_commutator hn₁ hn₂
  have heq (x : X) (u : Additive (ambientSubgroup U₁))
      (v : Additive (ambientSubgroup U₂)) :
      b (conjugateVector _ X hn₁ x u) (conjugateVector _ X hn₂ x v) =
        conjugateVector _ X hn₃ x (b u v) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hb]
    change ⁅MulAut.conj (x : G) (u.toMul : G),MulAut.conj (x : G) (v.toMul : G)⁆ =
      MulAut.conj (x : G) ((b u v).toMul : G)
    rw [hb]
    exact (map_commutatorElement (MulAut.conj (x : G)) _ _).symm
  obtain ⟨u,v,huv⟩ : ∃ u v, b u v ≠ 0 := by
    by_contra! hall
    apply hne
    apply bot_unique
    rw [hc]
    apply commutator_le.mpr
    intro u hu v hv
    have he := hb (Additive.ofMul ⟨u,hu⟩) (Additive.ofMul ⟨v,hv⟩)
    rw [hall] at he
    exact he.symm
  apply Section03.no_shadow_eigenvalue_configuration b
    (conjugateVector _ X hn₁ y) (conjugateVector _ X hn₂ y)
    (conjugateVector _ X hn₃ y) (heq y) hn ha horder huv
  · apply Additive.toMul.injective
    exact Subtype.ext (hy₁ u)
  · apply Additive.toMul.injective
    exact Subtype.ext (hy₂ v)
  · apply Additive.toMul.injective
    exact Subtype.ext (hy₃ (b u v))
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
