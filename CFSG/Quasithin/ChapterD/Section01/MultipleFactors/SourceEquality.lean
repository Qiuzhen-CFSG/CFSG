module
public import CFSG.Quasithin.ChapterD.Section01.SourceSolvable
public import Theory.Representation.BinaryOffender.InternalGenerators.PrescribedFirst

/-!
# Equality in the solvable multiple-factor qrc branch

When the original ratio is two, the exact source estimates force two
noncentral chief factors, both rank equalities, and equality of the actual
centralizers in U. Each chosen conjugate of V can be placed first in the
generating filtration, so equality holds on every literal conjugate action.

The theorem quantifies the source family of maximal elementary actors with
nontrivial quadratic action; the existing source actor theorem proves that
family nonempty. Solvability is the precise specialization used to establish
the noncentral chief ratios. No numerical or generator input is assumed.
Source: Aschbacher–Smith D.1.3(3), and the numerical part of 3.1.9(1–3),
printed pp.174–175 and 576–577.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}

theorem source_max_actor_in_core_centralizes
    (d : QRCConfiguration G₁ G₂ T V)
    (hnf : letI := d.module_elementary
      ¬ IsFFModule (imageRepresentation G₁ V d.module_normalized))
    (S : Sylow 2 G₂) (hS : (S : Subgroup G₂).map G₂.subtype = T)
    (A : Subgroup G₂) (hA : A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G₂))
    (hAN : A ≤ pCore 2 G₂) :
    A ≤ centralizer ((conjugateSpan G₂ V).subgroupOf G₂ : Set G₂) := by
  have hall : ∀ D ∈ elementaryAbelianMaxSubgroups T, D ≤ centralizer (V : Set G) := by
    intro D hD
    have hd : D ≤ elementaryAbelianMaxJ T := le_sSup hD
    rw [source_thompson_eq_of_notFF d hnf] at hd
    have hr : elementaryAbelianMaxJ (twoCoreIn G₁) ≤ twoCoreIn G₁ := sSup_le fun _ he => he.1
    exact (hd.trans hr).trans (d.core_eq_centralizer ▸ inf_le_right)
  have hAm : A.map G₂.subtype ∈ elementaryAbelianMaxSubgroups T := by
    rw [← hS]
    exact (maxFamily_map_injective_iff G₂.subtype G₂.subtype_injective S A).mpr hA
  have hcent := maxElementary_inside_centralizes_conjugateSpan T (twoCoreIn G₂) V G₂
    (A.map G₂.subtype) (right_core_le_sylow d) (twoCore_normalized G₂) hall hAm
    (map_mono hAN)
  rw [← conjugateSpan_eq] at hcent
  intro a ha u hu
  exact Subtype.ext (hcent (mem_map_of_mem G₂.subtype ha) u hu)

variable (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
  [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 ((conjugateSpan G₂ V).subgroupOf G₂)]

include hV in
theorem exists_conjugateGenerator_sequence_first
    (B : Subgroup G₂) (hB : B ≤ pCore 2 G₂) (g : G₂) :
    ∃ (n : ℕ) (W : ℕ → Subrepresentation
        ((normalRepresentation ((conjugateSpan G₂ V).subgroupOf G₂)).comp B.subtype)),
      0 < n ∧ W 0 = conjugateGenerator d B hB g ∧
      generatingSpan _ W n = ⊤ ∧
        ∀ i < n, quadraticRatio (imageRepresentation G₁ V d.module_normalized) ≤
          quadraticRatio (Representation.BinaryOffender.imageRepresentation (W i).toRepresentation) := by
  let := d.finite_right
  let U := (conjugateSpan G₂ V).subgroupOf G₂
  have hg : (⨆ g : G₂, conjugateGenerator d B hB g) = ⊤ :=
    iSup_internalGenerator_eq_top U B (fun g => conjugateSeed (V := V) g)
      (fun g => hB.trans (conjugateSeed_core_normalized d g))
      (fun g => conjugateSeed_le_span g) (iSup_conjugateSeed d hV)
  obtain ⟨n,a,hn,h₀,ha⟩ := exists_generatingSequence_start _ (conjugateGenerator d B hB) hg g
  exact ⟨n,fun i => conjugateGenerator d B hB (a i),hn,by simp [h₀],ha,
    fun i _ => conjugateGenerator_ratio d hV B hB (a i)⟩
end CFSG.Quasithin.ChapterD.UniqueFactor

namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}

theorem source_notFF_of_ratio_two
    (d : QRCConfiguration G₁ G₂ T V)
    (hq : letI := d.module_elementary
      quadraticRatio (imageRepresentation G₁ V d.module_normalized) = 2) :
    letI := d.module_elementary
    ¬ IsFFModule (imageRepresentation G₁ V d.module_normalized) := by
  let := d.finite_left
  let := d.module_elementary
  let : Finite V := Finite.of_injective (inclusion d.module_le) (inclusion_injective d.module_le)
  let f := actionHom G₁ V d.module_normalized
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  intro hff
  have he := (isFFModule_iff_quadraticRatio_le_one (imageRepresentation G₁ V d.module_normalized)).mp hff
  rw [hq] at he
  norm_num at he

theorem source_solvable_multiple_equalities
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn G₂)
    (hs : Group.IsSolvable G₂)
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
  have hf := source_solvable_chief_actions d hne hV hnf hs S hS s
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
