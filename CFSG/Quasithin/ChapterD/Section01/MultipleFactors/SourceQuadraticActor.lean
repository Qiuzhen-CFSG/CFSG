module
public import CFSG.Quasithin.ChapterD.Section01.SourceElementary
public import CFSG.Quasithin.ChapterB.Section02.QuadraticActors
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import Theory.GroupTheory.MaxElementaryConjugateSpan
public import Stellmacher.ElementaryAbelianMaxFamilyMap

/-!
# The quadratic maximal actor in the original qrc span

Under the original non-FF and inside-core hypotheses, the actual span U is
elementary and G₂ is a minimal parabolic. Its residual moves U, so B.6.8
puts the centralizer inside the maximal core and bounds C_S(U) by O₂(G₂).
Since J(S) escapes O₂(G₂), a maximum elementary subgroup moves U.

Every maximum elementary subgroup inside O₂(G₂) centralizes U: all its
G₂-conjugates remain maximum inside S, and J(T)=J(R) centralizes V.
The quadratic replacement theorem therefore gives a maximum elementary
actor outside O₂(G₂), with quadratic action on this same U. No quadratic
actor or generator-ratio premise is assumed.

Source: Aschbacher–Smith, D.1.3(2), printed p.173. This proves the existential
actor needed by D.1.3(1); it does not assert the stronger statement about
every subgroup with minimal nontrivial image modulo O₂(G₂).
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}
theorem source_span_centralizer_sylow_le_core
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn G₂)
    (hnf : letI := d.module_elementary
      ¬ IsFFModule (imageRepresentation G₁ V d.module_normalized))
    (S : Sylow 2 G₂) (hS : (S : Subgroup G₂).map G₂.subtype = T) :
    (S : Subgroup G₂) ⊓ centralizer ((conjugateSpan G₂ V).subgroupOf G₂ : Set G₂) ≤
      pCore 2 G₂ := by
  let := d.finite_right
  let U := conjugateSpan G₂ V
  let U0 := U.subgroupOf G₂
  have hUG : U ≤ G₂ := (span_le_right_core d hV).trans (twoCore_le G₂)
  have hP := source_intrinsic_minimalParabolic_of_notFF d hne hnf S hS
  have hnot : ¬ pResidual 2 G₂ ≤ centralizer (U0 : Set G₂) := by
    intro hh
    have hu : U ≤ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) := by
      intro u hu k hk
      obtain ⟨k,hk,rfl⟩ := hk
      exact congrArg G₂.subtype ((hh hk) ⟨u,hUG hu⟩ hu).symm
    exact residual_commutator_ne_bot d hne (commutator_eq_bot_iff_le_centralizer.mpr hu)
  have hc := ChapterB.minimalParabolic_normal_le_core_of_residual_not_le S hP
    (centralizer (U0 : Set G₂)) hnot
  exact (inf_le_inf_left (S : Subgroup G₂) hc).trans_eq
    (ChapterB.minimalParabolic_sylow_inf_core S hP)

theorem source_quadratic_max_actor
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn G₂)
    (hnf : letI := d.module_elementary
      ¬ IsFFModule (imageRepresentation G₁ V d.module_normalized))
    (S : Sylow 2 G₂) (hS : (S : Subgroup G₂).map G₂.subtype = T) :
    let U := (conjugateSpan G₂ V).subgroupOf G₂
    letI := source_elementary_span_of_notFF d hV hnf
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le G₂))
    ∃ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G₂), ¬ A ≤ pCore 2 G₂ ∧
      IsQuadratic (normalRepresentation U) A := by
  let := d.finite_right
  let U := (conjugateSpan G₂ V).subgroupOf G₂
  have hUG : conjugateSpan G₂ V ≤ G₂ :=
    (span_le_right_core d hV).trans (twoCore_le G₂)
  let := source_elementary_span_of_notFF d hV hnf
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUG
  dsimp only
  have hUS : U ≤ S := by
    intro u hu
    have ht : (u : G) ∈ T := (right_core_le_sylow d) ((span_le_right_core d hV) hu)
    rw [← hS] at ht
    obtain ⟨s,hs,he⟩ := ht
    exact G₂.subtype_injective he ▸ hs
  have hall : ∀ D ∈ elementaryAbelianMaxSubgroups T, D ≤ centralizer (V : Set G) := by
    intro D hD
    have hd : D ≤ elementaryAbelianMaxJ T := le_sSup hD
    rw [source_thompson_eq_of_notFF d hnf] at hd
    have hr : elementaryAbelianMaxJ (twoCoreIn G₁) ≤ twoCoreIn G₁ := sSup_le fun _ he => he.1
    exact (hd.trans hr).trans (d.core_eq_centralizer ▸ inf_le_right)
  have hinside : ∀ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G₂),
      A ≤ pCore 2 G₂ → A ≤ centralizer (U : Set G₂) := by
    intro A hA hAN
    have hAm : A.map G₂.subtype ∈ elementaryAbelianMaxSubgroups T := by
      rw [← hS]
      exact (maxFamily_map_injective_iff G₂.subtype G₂.subtype_injective S A).mpr hA
    have hcent := maxElementary_inside_centralizes_conjugateSpan T (twoCoreIn G₂) V G₂
      (A.map G₂.subtype) (right_core_le_sylow d) (twoCore_normalized G₂) hall hAm
      (map_mono hAN)
    rw [← conjugateSpan_eq] at hcent
    intro a ha u hu
    exact Subtype.ext (hcent (mem_map_of_mem G₂.subtype ha) u hu)
  apply ChapterB.maxElementary_exists_quadratic_outside U S (pCore 2 G₂) hUS hinside
  by_contra! hn
  have hJc : elementaryAbelianMaxJ (S : Subgroup G₂) ≤ centralizer (U : Set G₂) :=
    sSup_le hn
  have hJS : elementaryAbelianMaxJ (S : Subgroup G₂) ≤ S := sSup_le fun _ hA => hA.1
  have hJ2 : elementaryAbelianMaxJ (S : Subgroup G₂) ≤ pCore 2 G₂ :=
    (le_inf hJS hJc).trans (source_span_centralizer_sylow_le_core d hne hV hnf S hS)
  have hm := map_mono (f := G₂.subtype) hJ2
  rw [← elementaryAbelianMaxJ_map_injective G₂.subtype G₂.subtype_injective, hS,
    source_thompson_eq_of_notFF d hnf] at hm
  exact source_thompson_core_not_le_right_core_of_notFF d hne hnf hm
end CFSG.Quasithin.ChapterD.UniqueFactor
