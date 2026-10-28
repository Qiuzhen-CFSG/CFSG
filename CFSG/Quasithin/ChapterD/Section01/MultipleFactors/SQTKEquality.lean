module
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceEquality
public import CFSG.Quasithin.ChapterD.Section01.SourceMultiple
/-!
# Equality for the actual SQTK multiple-chief-factor branch

The original SQTK group supplies the chief-action lower bounds, without a
solvability assumption on that group or on an arbitrary quotient. Equality
in the generator estimates forces two noncentral factors, both rank
identities, equality of the centralizers in the conjugate span, and equality
on every literal conjugate of V. The first generator is prescribed to obtain
the last conclusion for each conjugate.
Source: Aschbacher--Smith D.1.3(3), 3.1.9(1--3), and its application in
15.1.12, printed pp.174--175,576--577,1089--1090.
-/
public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}
theorem source_sqtk_multiple_equalities
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn G₂)
    (hG₂ : IsSQTK KnownSimple.IsKnownSimple G₂)
    (hq : letI := d.module_elementary
      quadraticRatio (imageRepresentation G₁ V d.module_normalized) = 2) :
    let U := (conjugateSpan G₂ V).subgroupOf G₂
    letI := d.module_elementary
    letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le G₂))
    ∀ (S : Sylow 2 G₂), (S : Subgroup G₂).map G₂.subtype = T →
    ∀ (s : SeriesOn U), 1 < s.noncentralCount →
    ∀ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G₂),
      IsQuadratic (normalRepresentation U) A → ¬ A ≤ centralizer (U : Set G₂) →
      s.noncentralCount = 2 ∧
      2 * Nat.log 2 ((pCore 2 G₂).relIndex A) = fixedCodim (normalRepresentation U) A ∧
      fixedCodim (normalRepresentation U) A =
        2 * Nat.log 2 ((centralizer (U : Set G₂)).relIndex (A ⊓ pCore 2 G₂)) ∧
      U ⊓ centralizer (A : Set G₂) = U ⊓ centralizer (A ⊓ pCore 2 G₂ : Set G₂) ∧
      (∀ i, ¬ s.Central i →
        Nat.log 2 ((pCore 2 G₂).relIndex A) = fixedCodim (s.factorRepresentation i) A) ∧
      ∀ g : G₂,
        (fixedCodim (conjugateGenerator d (A ⊓ pCore 2 G₂) inf_le_right g).toRepresentation ⊤ : ℝ) =
          2 * (Nat.log 2 (subspaceKernel ((normalRepresentation U).comp (A ⊓ pCore 2 G₂).subtype)
            (conjugateGenerator d (A ⊓ pCore 2 G₂) inf_le_right g).toSubmodule ⊤).index : ℝ) := by
  let := d.finite_right
  let := d.module_elementary
  have hnf := source_notFF_of_ratio_two d hq
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan G₂ V).subgroupOf G₂
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le G₂))
  dsimp only
  intro S hS s hc A hA hquad hnc
  have hAR : ¬ A ≤ pCore 2 G₂ := fun h => hnc (source_max_actor_in_core_centralizes d hnf S hS A hA h)
  have hUS : U ≤ S := by
    intro u hu
    have ht : (u : G) ∈ T := (right_core_le_sylow d) ((span_le_right_core d hV) hu)
    rw [← hS] at ht
    obtain ⟨s,hs,he⟩ := ht
    exact G₂.subtype_injective he ▸ hs
  have hk : A ⊓ centralizer (U : Set G₂) ≤ pCore 2 G₂ :=
    (inf_le_inf_right _ hA.1).trans (source_span_centralizer_sylow_le_core d hne hV hnf S hS)
  have hf := source_sqtk_chief_actions d hne hV hnf hG₂ S hS s
  have hx (g : G₂) :
      s.noncentralCount = 2 ∧
      2 * Nat.log 2 ((pCore 2 G₂).relIndex A) = fixedCodim (normalRepresentation U) A ∧
      fixedCodim (normalRepresentation U) A =
        2 * Nat.log 2 ((centralizer (U : Set G₂)).relIndex (A ⊓ pCore 2 G₂)) ∧
      U ⊓ centralizer (A : Set G₂) = U ⊓ centralizer (A ⊓ pCore 2 G₂ : Set G₂) ∧
      (∀ i, ¬ s.Central i →
        Nat.log 2 ((pCore 2 G₂).relIndex A) = fixedCodim (s.factorRepresentation i) A) ∧
      (fixedCodim (conjugateGenerator d (A ⊓ pCore 2 G₂) inf_le_right g).toRepresentation ⊤ : ℝ) =
        2 * (Nat.log 2 (subspaceKernel ((normalRepresentation U).comp (A ⊓ pCore 2 G₂).subtype)
          (conjugateGenerator d (A ⊓ pCore 2 G₂) inf_le_right g).toSubmodule ⊤).index : ℝ) := by
    obtain ⟨n,W,hn,h₀,hgen,hgenRatio⟩ := exists_conjugateGenerator_sequence_first d hV
      (A ⊓ pCore 2 G₂) inf_le_right g
    have hr : ∀ i < n, 2 ≤ quadraticRatio (Representation.BinaryOffender.imageRepresentation
        (W i).toRepresentation) := by
      intro i hi
      rw [← hq]
      exact hgenRatio i hi
    have he := MultipleFactors.rank_equality_of_action_images U s S A (pCore 2 G₂)
      hUS hA hAR hc hquad hk (fun i hi => (hf i).2 hi A hA.1)
      (fun i _ => (hf i).1) W n hgen hr
    refine ⟨he.1,he.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2.1,?_⟩
    have hl := he.2.2.2.2.2 hn
    have hcod := congrArg (fun J : Subrepresentation ((normalRepresentation U).comp
      (A ⊓ pCore 2 G₂).subtype) => (fixedCodim J.toRepresentation ⊤ : ℝ)) h₀
    have hker := congrArg (fun J : Subrepresentation ((normalRepresentation U).comp
      (A ⊓ pCore 2 G₂).subtype) =>
      2 * (Nat.log 2 (subspaceKernel ((normalRepresentation U).comp
        (A ⊓ pCore 2 G₂).subtype) J.toSubmodule ⊤).index : ℝ)) h₀
    exact hcod.symm.trans (hl.trans hker)
  have he := hx 1
  exact ⟨he.1,he.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2.1,fun g => (hx g).2.2.2.2.2⟩
end CFSG.Quasithin.ChapterD.UniqueFactor
