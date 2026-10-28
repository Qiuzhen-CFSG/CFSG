module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SelfNormalizer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ComponentwiseInner
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.TorusControl
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.LieBorels
public import Theory.GroupTheory.SylowNormalizerCommutingFamily.SelfNormalizing
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.BinaryModels
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.BinaryOuter
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.LinearField
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.RankTwoField

/-!
# Borel collapse and componentwise inner action

Under source noncontainment, the torus-action calculations exclude every
nonbinary Lie alternative. The defining exponent is therefore one.

Self-normalization of the selected component's Sylow subgroups passes to
all its T-conjugates, their commuting product, and the whole star closure.
The actual star projection then lifts that equality to B = T₀. Outer
orders transport to each conjugate separately, so their inner actions can
be combined without a claim about the outer group of the full product.

`collapse_and_factor_data` supplies the collapsed Borel and every input
of the componentwise inner-action assembly on the actual conjugate family.
`containment_of_lie_model` completes the conditional containment argument
for all Lie alternatives. Only the genuine source setup, quasisimplicity,
the concrete Lie model and solvability of the relative Borel remain inputs.
Their construction and the exceptional component alternatives belong to
the source-theorem owner; this module does not assert all of 15.3.49(k).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
`refs/quasithin.pdf`, printed p.1144, proof of 15.3.49(k).
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse
open ModelSelection LieBorels
universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

/-- Lift component Sylow self-normalization through every conjugate and the actual two-core quotient. -/
theorem borel_eq_of_component_self_normalizing
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hN : ∀ P : Sylow 2 (starImage H L), normalizer (P : Set (starImage H L)) = P) :
    relativeBorel L T = sylowIntersection L T := by
  classical
  let _ := Fintype.ofFinite ↥(conjugateFactors H L T)
  have hf (C : ↥(conjugateFactors H L T)) (P : Sylow 2 (factor C)) :
      normalizer (P : Set (factor C)) = P :=
    Sylow.self_normalizing_of_surjective (factorEquiv d C).toMonoidHom
      (factorEquiv d C).surjective hN P
  have hn := Sylow.self_normalizing_of_commuting_family
    (factor (H := H) (L := L) (T := T)) (factor_commute d hq) (factor_sup d) hf
    (closureSylow d)
  change normalizer ((closureSylow d : Subgroup (starImage H (localSpan L T))) :
    Set (starImage H (localSpan L T))) = _ at hn
  rw [closureSylow_coe] at hn
  change normalizer ((starImage H (sylowIntersection L T)).subgroupOf
    (starImage H (localSpan L T)) : Set (starImage H (localSpan L T))) =
    (starImage H (sylowIntersection L T)).subgroupOf (starImage H (localSpan L T)) at hn
  have hi : (relativeBorel L T).subgroupOf (localSpan L T) =
      (sylowIntersection L T).subgroupOf (localSpan L T) := by
    unfold relativeBorel
    rw [← starProjection_normalizer_comap H (localSpan L T) (sylowIntersection L T)
      (closure_le d) inf_le_right (closure_projection_ker_le_inter d), hn,
      ← starProjection_map H (localSpan L T) (sylowIntersection L T) (closure_le d) inf_le_right]
    exact comap_map_eq_self (closure_projection_ker_le_inter d)
  have he := congrArg (Subgroup.map (localSpan L T).subtype) hi
  simpa only [map_subgroupOf_eq_of_le (show relativeBorel L T ≤ localSpan L T from inf_le_left),
    map_subgroupOf_eq_of_le (show sylowIntersection L T ≤ localSpan L T from inf_le_right)] using he

/-- The actual equivalence with each conjugate transports the individual outer-order bound. -/
theorem conjugateFactors_outer_three_free
    (hout : ¬ 3 ∣ Nat.card (MulAut.Outer (starImage H L)))
    (C : Subgroup (H ⧸ pCore 2 H)) (hC : C ∈ conjugateFactors H L T) :
    ¬ 3 ∣ Nat.card (MulAut.Outer C) := by
  obtain ⟨e⟩ := (conjugateFactors_properties d C hC).2.2.2
  rwa [← Nat.card_congr (MulAut.outerCongr e).toEquiv]

/-- Self-normalization and the selected component’s outer order supply all the closure assembly inputs. -/
theorem containment_of_component_automorphisms
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hN : ∀ P : Sylow 2 (starImage H L), normalizer (P : Set (starImage H L)) = P)
    (hout : ¬ 3 ∣ Nat.card (MulAut.Outer (starImage H L))) : Y0 ≤ localSpan L T := by
  let _ := d.solvable
  exact Y0_le_closure_of_inner_star_action H M Y0 L T d.replacement d.sylow_le
    d.theta_eq d.solvable_control (d.theta_eq ▸ ComponentIntersection.theta_isPPerfect _)
    d.cubic_quotient d.sylow_normalizes d.commutator_eq
    (component_star_nontrivial H L (localSpan L T) d.component_in_H (le_conjugateSpanBy L T))
    (closure_star_center_eq_bot_of_self_normalizing H L Y0 T d.replacement
      d.commutator_eq d.sylow_normalizes (borel_eq_of_component_self_normalizing d hq hN))
    (inner_star_of_factor_outer_three_free H M Y0 (localSpan L T) d.theta_eq
      (conjugateFactors H L T) (conjugateFactors_sup d)
      (fun C hC D hD hne => conjugateFactors_commute d hq C D hC hD hne)
      (fun C hC => (conjugateFactors_properties d C hC).2.2.1)
      (conjugateFactors_outer_three_free d hout))

/-- The Borel of the whole closure collapses for every binary Lie alternative. -/
theorem binary_borel_eq
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hmodel : LieComponentModel (starImage H L) 1) :
    relativeBorel L T = sylowIntersection L T :=
  borel_eq_of_component_self_normalizing d hq
    (BinaryModels.binary_model_self_normalizing hmodel)

/-- After binary specialization only the individual outer-order bound remains. -/
theorem containment_of_binary_model
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hmodel : LieComponentModel (starImage H L) 1)
    (hout : ¬ 3 ∣ Nat.card (MulAut.Outer (starImage H L))) : Y0 ≤ localSpan L T :=
  containment_of_component_automorphisms d hq
    (BinaryModels.binary_model_self_normalizing hmodel) hout

/-- Complete the binary PSL₄ and PSL₅ branches, retaining all conjugate factors. -/
theorem binary_linear_containment
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : starImage H L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :
    Y0 ≤ localSpan L T := by
  apply containment_of_binary_model d hq (.binary_linear rfl n hn ⟨e⟩)
  rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
  exact BinaryModels.binary_linear_outer_three_free hn

/-- Complete the derived binary symplectic branch using its actual A₆ equivalence. -/
theorem binary_symplectic_containment
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (e : starImage H L ≃* commutator (Matrix.symplecticGroup (Fin 2) F)) :
    Y0 ≤ localSpan L T := by
  apply containment_of_binary_model d hq
    (.symplectic (by decide) F (by simpa using hF) ⟨e⟩)
  rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
  exact BinaryModels.binary_symplectic_outer_three_free hF

/-- The source action on the Borel quotient excludes every nonbinary
alternative, retaining the exact defining exponent of the supplied model. -/
theorem exponent_eq_one [Group.IsSolvable (relativeBorel L T)]
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hout : ¬ Y0 ≤ localSpan L T)
    {e : ℕ} (hmodel : LieComponentModel (starImage H L) e) : e = 1 := by
  cases hmodel with
  | linear_two he F hF m =>
      exact (LinearField.false_of_linear_two d hq hout he hF m).elim
  | linear_three he F hF m =>
      by_contra hne
      exact LinearField.false_of_linear_three d hq hout (by omega) hF m
  | symplectic he F hF m =>
      by_contra hne
      obtain ⟨f⟩ := m
      exact RankTwoField.symplectic_exclusion d hq hout hF (by omega) f
  | g2 he F hF m =>
      by_contra hne
      obtain ⟨f⟩ := m
      exact RankTwoField.g2_exclusion d hq hout hF (by omega) f
  | binary_linear he n hn m => exact he

/-- All model inputs for the collapsed-Borel and componentwise assembly.
The witness consists of every actual T-conjugate star image, including
all component orbits. No outer-order bound on their full product is used. -/
theorem collapse_and_factor_data [Group.IsSolvable (relativeBorel L T)]
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hout : ¬ Y0 ≤ localSpan L T)
    {e : ℕ} (hmodel : LieComponentModel (starImage H L) e) :
    e = 1 ∧ relativeBorel L T = sylowIntersection L T ∧
      ∃ s : Finset (Subgroup (H ⧸ pCore 2 H)),
        s.sup id = starImage H (localSpan L T) ∧
        (∀ C ∈ s, ∀ D ∈ s, C ≠ D → C ≤ centralizer (D : Set (H ⧸ pCore 2 H))) ∧
        (∀ C ∈ s, starImage H Y0 ≤ normalizer (C : Set (H ⧸ pCore 2 H))) ∧
        (∀ C ∈ s, ¬ 3 ∣ Nat.card (MulAut.Outer C)) := by
  have he := exponent_eq_one d hq hout hmodel
  have hb : LieComponentModel (starImage H L) 1 := he ▸ hmodel
  refine ⟨he, binary_borel_eq d hq hb, conjugateFactors H L T,
    conjugateFactors_sup d, ?_, ?_, ?_⟩
  · exact fun C hC D hD hne => conjugateFactors_commute d hq C D hC hD hne
  · exact fun C hC => (conjugateFactors_properties d C hC).2.2.1
  · exact conjugateFactors_outer_three_free d (BinaryModels.binary_model_outer_three_free hb)

/-- The Lie-model branch of 15.3.49(k), conditional only on the earlier
source setup, quasisimple model selection and solvability of the relative Borel.
The field collapse, centerlessness and inner action are all derived. -/
theorem containment_of_lie_model [Group.IsSolvable (relativeBorel L T)]
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    {e : ℕ} (hmodel : LieComponentModel (starImage H L) e) : Y0 ≤ localSpan L T := by
  by_contra hout
  obtain ⟨_, hB, s, hspan, hcomm, hn, houter⟩ := collapse_and_factor_data d hq hout hmodel
  let _ := d.solvable
  exact hout (Y0_le_closure_of_inner_star_action H M Y0 L T d.replacement d.sylow_le
    d.theta_eq d.solvable_control (d.theta_eq ▸ ComponentIntersection.theta_isPPerfect _)
    d.cubic_quotient d.sylow_normalizes d.commutator_eq
    (component_star_nontrivial H L (localSpan L T) d.component_in_H (le_conjugateSpanBy L T))
    (closure_star_center_eq_bot_of_self_normalizing H L Y0 T d.replacement
      d.commutator_eq d.sylow_normalizes hB)
    (inner_star_of_factor_outer_three_free H M Y0 (localSpan L T) d.theta_eq
      s hspan hcomm hn houter))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse
