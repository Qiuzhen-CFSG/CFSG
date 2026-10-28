module
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.SourceEquality
public import CFSG.Quasithin.ChapterB.Section02.MinimalQuadraticActors

/-!
# A minimal quadratic actor on the original qrc span

The actual conjugate span lies in the second two-core. Its Sylow centralizer
lies there too, while every maximum elementary subgroup in that core fixes
the span. Quadratic replacement therefore selects an actor outside the core
whose image modulo the core has minimum order among all such actors.
This supplies the literal minimality used in the final Thompson argument
of 15.1.12(4), rather than assuming a preferred quadratic actor.

Source: Aschbacher--Smith D.1.3(2) and 15.1.12(4), printed pp.173,1090.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}

theorem source_quadratic_minimal_max_actor
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn G₂)
    (hnf : letI := d.module_elementary
      ¬ IsFFModule (imageRepresentation G₁ V d.module_normalized))
    (S : Sylow 2 G₂) (hS : (S : Subgroup G₂).map G₂.subtype = T) :
    let U := (conjugateSpan G₂ V).subgroupOf G₂
    letI := source_elementary_span_of_notFF d hV hnf
    letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
      ((span_le_right_core d hV).trans (twoCore_le G₂))
    ∃ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G₂), ¬ A ≤ pCore 2 G₂ ∧
      IsQuadratic (normalRepresentation U) A ∧
      ∀ B ∈ elementaryAbelianMaxSubgroups (S : Subgroup G₂),
        ¬ B ≤ pCore 2 G₂ → (pCore 2 G₂).relIndex A ≤ (pCore 2 G₂).relIndex B := by
  let := d.finite_right
  let U := (conjugateSpan G₂ V).subgroupOf G₂
  let := source_elementary_span_of_notFF d hV hnf
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le G₂))
  dsimp only
  have hUN : U ≤ pCore 2 G₂ := by
    intro u hu
    obtain ⟨x,hx,he⟩ := span_le_right_core d hV hu
    exact G₂.subtype_injective he ▸ hx
  have hUS : U ≤ S := by
    intro u hu
    have ht : (u : G) ∈ T := (right_core_le_sylow d) ((span_le_right_core d hV) hu)
    rw [← hS] at ht
    obtain ⟨s,hs,he⟩ := ht
    exact G₂.subtype_injective he ▸ hs
  apply ChapterB.maxElementary_exists_quadratic_minimal_outside U S (pCore 2 G₂) hUS hUN
    (source_span_centralizer_sylow_le_core d hne hV hnf S hS)
    (source_max_actor_in_core_centralizes d hnf S hS)
  obtain ⟨A,hA,hAN,_⟩ := source_quadratic_max_actor d hne hV hnf S hS
  exact ⟨A,hA,hAN⟩
end CFSG.Quasithin.ChapterD.UniqueFactor
