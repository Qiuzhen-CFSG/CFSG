module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Model
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Forms
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.FormActors
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Quadratic-actor containment in the actual SL₃(4) component

A faithful binary action with the specified natural-plus-dual coordinates
embeds the ambient group into GL₁₂(2). Normality puts its entire image in the
normalizer of the concrete SL₃(4) image. The inverse image of that component
is exactly the original subgroup, and the actor retains elementary structure,
quadraticity, rank and fixed codimension.

The computed binary centralizer yields the semilinear normalizer forms in
`NormalizerReduction.Forms`. The calculation in `NormalizerReduction.FormActors`
excludes an exchanging or field-twisted actor: quadraticity would force the
actor subgroup to have order at most two, while its fixed codimension is at
least six. An untwisted involution has determinant and dual scalar one.
Combining these results proves component containment for every elementary
quadratic actor whose fixed codimension is at most twice its rank. Transport
then gives containment in the original normal subgroup. No upper bound on
the actor rank is needed; the final wrapper retains the rank-four source input.

Source: Aschbacher--Smith, proof of 13.8.20, printed p.955 (PDF p.972),
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
open BinaryOffender
variable {J U : Type*} [Group J] [AddCommGroup U] [Module (ZMod 2) U]

/-- The original ambient action in the given concrete module coordinates. -/
def coordinateAction (ρ : Representation (ZMod 2) J U) (E : U ≃ₗ[ZMod 2] V) :
    J →* BinaryGL :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
    ((Units.mapEquiv E.conjRingEquiv.toMulEquiv).toMonoidHom.comp ρ.asGroupHom)

lemma coordinateAction_apply (ρ : Representation (ZMod 2) J U)
    (E : U ≃ₗ[ZMod 2] V) (j : J) (v : V) :
    coordinateAction ρ E j v = E (ρ j (E.symm v)) := rfl

lemma coordinateAction_equivariant (ρ : Representation (ZMod 2) J U)
    (E : U ≃ₗ[ZMod 2] V) (j : J) (u : U) :
    E (ρ j u) = binaryRepresentation (coordinateAction ρ E j) (E u) := by
  change E (ρ j u) = E (ρ j (E.symm (E u)))
  rw [E.symm_apply_apply]

lemma coordinateAction_injective (ρ : Representation (ZMod 2) J U)
    (hρ : Function.Injective ρ) (E : U ≃ₗ[ZMod 2] V) :
    Function.Injective (coordinateAction ρ E) := by
  intro g h he
  apply hρ
  apply LinearMap.ext
  intro u
  apply E.injective
  have hh := LinearEquiv.congr_fun he (E u)
  simpa only [coordinateAction_apply, E.symm_apply_apply] using hh

lemma coordinateAction_on_component (ρ : Representation (ZMod 2) J U)
    (K : Subgroup J) (eK : K ≃* SL) (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u)) (k : K) :
    coordinateAction ρ E k = linearAction (eK k) := by
  apply LinearEquiv.ext
  intro v
  change E (ρ k (E.symm v)) = representation (eK k) v
  rw [hE, E.apply_symm_apply]

/-- The specified component maps onto precisely the determinant-one model image. -/
lemma component_eq_map (ρ : Representation (ZMod 2) J U)
    (K : Subgroup J) (eK : K ≃* SL) (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u)) :
    component = K.map (coordinateAction ρ E) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨eK.symm g, (eK.symm g).property, ?_⟩
    rw [coordinateAction_on_component ρ K eK E hE, eK.apply_symm_apply]
  · rintro ⟨k, hk, rfl⟩
    exact ⟨eK ⟨k, hk⟩, (coordinateAction_on_component ρ K eK E hE ⟨k, hk⟩).symm⟩

/-- Faithfulness identifies the full inverse image, so no centralizing kernel is lost. -/
lemma comap_component (ρ : Representation (ZMod 2) J U) (hρ : Function.Injective ρ)
    (K : Subgroup J) (eK : K ≃* SL) (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u)) :
    component.comap (coordinateAction ρ E) = K := by
  rw [component_eq_map ρ K eK E hE]
  exact Subgroup.comap_map_eq_self_of_injective (coordinateAction_injective ρ hρ E) K

/-- Ambient normality gives actual normalization of the matrix-action image. -/
lemma coordinateAction_mem_normalizer (ρ : Representation (ZMod 2) J U)
    (K : Subgroup J) [K.Normal] (eK : K ≃* SL) (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u)) (j : J) :
    coordinateAction ρ E j ∈ normalizer := by
  change coordinateAction ρ E j ∈ Subgroup.normalizer (component : Set BinaryGL)
  rw [component_eq_map ρ K eK E hE]
  apply Subgroup.le_normalizer_map (coordinateAction ρ E)
  exact Subgroup.mem_map_of_mem _ (by rw [K.normalizer_eq_top]; trivial)

lemma coordinateActor_elementary (ρ : Representation (ZMod 2) J U)
    (hρ : Function.Injective ρ) (E : U ≃ₗ[ZMod 2] V) (A : Subgroup J)
    (hA : IsElementaryTwo A) : IsElementaryTwo (A.map (coordinateAction ρ E)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.2
  refine ⟨?_, IsElementaryAbelian.map _⟩
  intro hb
  apply hA.1
  apply Subgroup.map_injective (coordinateAction_injective ρ hρ E)
  simpa only [Subgroup.map_bot] using hb

lemma coordinateActor_quadratic (ρ : Representation (ZMod 2) J U)
    (E : U ≃ₗ[ZMod 2] V) (A : Subgroup J) (hA : IsQuadratic ρ A) :
    IsQuadratic binaryRepresentation (A.map (coordinateAction ρ E)) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  obtain ⟨u, rfl⟩ := E.surjective v
  change E (ρ a (E.symm (E (ρ b (E.symm (E u))) - E u))) =
    E (ρ b (E.symm (E u))) - E u
  rw [E.symm_apply_apply]
  have he : E.symm (E (ρ b u) - E u) = ρ b u - u := by simp
  rw [he, hA a ha b hb u, map_sub]

lemma coordinateActor_rank (ρ : Representation (ZMod 2) J U)
    (hρ : Function.Injective ρ) (E : U ≃ₗ[ZMod 2] V) (A : Subgroup J) :
    rank (A.map (coordinateAction ρ E)) = rank A :=
  rank_map_injective _ (coordinateAction_injective ρ hρ E) A

lemma coordinateActor_fixedCodim (ρ : Representation (ZMod 2) J U)
    (E : U ≃ₗ[ZMod 2] V) (A : Subgroup J) :
    fixedCodim binaryRepresentation (A.map (coordinateAction ρ E)) = fixedCodim ρ A :=
  (fixedCodim_map_equivariant ρ binaryRepresentation _ E
    (coordinateAction_equivariant ρ E) A).symm

/-- Containment of the concrete action image is equivalent to containment
in the original component, using faithfulness and the given equivariance. -/
theorem coordinateActor_le_component_iff (ρ : Representation (ZMod 2) J U)
    (hρ : Function.Injective ρ) (K : Subgroup J) (eK : K ≃* SL)
    (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u))
    (A : Subgroup J) : A.map (coordinateAction ρ E) ≤ component ↔ A ≤ K := by
  rw [Subgroup.map_le_iff_le_comap, comap_component ρ hρ K eK E hE]

/-- Every elementary quadratic actor of action ratio at most two in the actual
binary normalizer lies in the determinant-one natural-plus-dual component.
The normalizer forms and their outer-actor exclusion are both discharged. -/
theorem le_component_of_le_normalizer (B : Subgroup BinaryGL)
    (hBN : B ≤ normalizer) (hB : IsElementaryTwo B)
    (hq : IsQuadratic binaryRepresentation B)
    (hoff : fixedCodim binaryRepresentation B ≤ 2 * rank B) : B ≤ component :=
  le_component_of_hasStandardForm B
    (fun b hb => hasStandardForm_of_mem_normalizer b (hBN hb)) hB hq hoff

/-- Faithful natural-plus-dual coordinates on a normal SL₃(4) subgroup force
every elementary quadratic actor of action ratio at most two into that subgroup.
The module equivalence is an input; no normalizer classification or actor
containment is assumed. -/
theorem actor_le_of_equivariant (ρ : Representation (ZMod 2) J U)
    (hρ : Function.Injective ρ) (K : Subgroup J) [K.Normal] (eK : K ≃* SL)
    (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u))
    (A : Subgroup J) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hoff : fixedCodim ρ A ≤ 2 * rank A) : A ≤ K := by
  apply (coordinateActor_le_component_iff ρ hρ K eK E hE A).mp
  apply le_component_of_le_normalizer (A.map (coordinateAction ρ E))
  · rintro _ ⟨a, _, rfl⟩
    exact coordinateAction_mem_normalizer ρ K eK E hE a
  · exact coordinateActor_elementary ρ hρ E A hA
  · exact coordinateActor_quadratic ρ E A hq
  · rw [coordinateActor_fixedCodim, coordinateActor_rank ρ hρ]
    exact hoff

/-- The finite, rank-at-most-four normalizer reduction used in the SL₃(4)
branch of the proof of 13.8.20. It is a specialization of the rank-free result. -/
theorem small_actor_le_of_equivariant [Finite J]
    (ρ : Representation (ZMod 2) J U) (hρ : Function.Injective ρ)
    (K : Subgroup J) [K.Normal] (eK : K ≃* SL) (E : U ≃ₗ[ZMod 2] V)
    (hE : ∀ (k : K) u, E (ρ k u) = representation (eK k) (E u))
    (A : Subgroup J) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hoff : fixedCodim ρ A ≤ 2 * rank A) (_hrank : rank A ≤ 4) : A ≤ K :=
  actor_le_of_equivariant ρ hρ K eK E hE A hA hq hoff

end Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
