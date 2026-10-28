module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.NormalizerTheta
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.CubicSubgroups
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LocalExclusion
public import Theory.GroupTheory.PrimeOrderClosurePerfect
/-!
# The exact theta alternatives for the original seed normalizer

Cubic generation puts the selected X inside theta(N_K(V₃)). The earlier
normalizer bound puts this theta subgroup inside L₁. Its T-invariance,
two-perfectness and the marked local subgroup classification force it
to be L₁ or the covered L₁,+. In the contained-L₁ case equality with L₁
holds without a rank premise. The actual cubic closure is solvable.

Source: Aschbacher–Smith, proof of13.7.5(4–6), printed p.938. Solvability
here concerns theta itself; the separate prime-to-three residual statement
of clause(6) is not asserted by this module.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Containment of L₁ identifies the entire theta subgroup, without a rank input. -/
theorem seed_normalizer_theta_eq_of_one_le
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) (hL₁K : sourceOne L T V₁ ≤ K) :
    closure {x : G | x ∈ K ⊓ normalizer (V₃ : Set G) ∧ orderOf x = 3} = sourceOne L T V₁ := by
  apply le_antisymm (seed_normalizer_theta_le d h hH hcentral hKH)
  rw [← point_residual_cubic_generated d]
  apply Subgroup.closure_mono
  intro x hx
  exact ⟨⟨hL₁K hx.1, point_residual_normalizes_seed d hx.1⟩, hx.2⟩

/-- The original covered case has exactly the two printed theta alternatives. -/
theorem seed_normalizer_theta_alternatives_of_plus_le
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hplusK : plus L T V₁ ≤ K) :
    let Y := closure {x : G | x ∈ K ⊓ normalizer (V₃ : Set G) ∧ orderOf x = 3}
    Y = plus L T V₁ ∨ Y = sourceOne L T V₁ := by
  dsimp only
  let N := K ⊓ normalizer (V₃ : Set G)
  let Y := closure {x : G | x ∈ N ∧ orderOf x = 3}
  have hY : Y ≤ sourceOne L T V₁ := seed_normalizer_theta_le d h hH hcentral hKH
  have hKn := (component_normal_and_span_of_plus_le d hH hF9 hcover hKH hK hplusK).1
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) := by
    apply le_trans ?_ (normalizer_le_primeOrderClosure_normalizer 3 N)
    apply le_trans ?_ inf_normalizer_le_normalizer_inf
    exact le_inf (hF9.T_le_H.trans hKn)
      (d.seed_stable.trans (normalizer (V₃ : Set G)).le_normalizer)
  have hplusY : plus L T V₁ ≤ Y := by
    rw [← point_subgroup_cubic_generated d (plus_le_one L T V₁ d.line_stable)
      (residual_isPPerfect _)]
    apply Subgroup.closure_mono
    intro x hx
    exact ⟨⟨hplusK hx.1, point_residual_normalizes_seed d
      (plus_le_one L T V₁ d.line_stable hx.1)⟩, hx.2⟩
  have hnotcentral : ¬ Y ≤ centralizer (V₃ : Set G) := by
    intro hc
    have he : ⁅V₃, plus L T V₁⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (hplusY.trans hc)
    rw [seed_commutator_plus d hcover] at he
    have hc := d.seed_card
    rw [he, card_bot] at hc
    norm_num at hc
  rcases covered_point_subgroup_alternatives d hcover hY
    (primeOrderClosure_isPPerfect (by decide : Nat.Coprime 2 3) N) hTY with hb | hz | hp | ho
  · exact (hnotcentral (hb ▸ bot_le)).elim
  · apply False.elim
    apply hnotcentral
    rw [hz]
    exact (residual_le (centralPreimage L)).trans
      ((NaturalModels.centralPreimage_centralizes d).trans (centralizer_le d.seed_le))
  · exact Or.inl hp
  · exact Or.inr ho

/-- The literal cubic closure of the original seed normalizer is solvable. -/
theorem seed_normalizer_theta_solvable
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) :
    Group.IsSolvable (closure {x : G | x ∈ K ⊓ normalizer (V₃ : Set G) ∧ orderOf x = 3}) := by
  let := point_residual_solvable d
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion (seed_normalizer_theta_le d h hH hcentral hKH)) (inclusion_injective _)

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
