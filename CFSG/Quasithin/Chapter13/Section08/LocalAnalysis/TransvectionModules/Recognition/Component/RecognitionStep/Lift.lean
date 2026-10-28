module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Actor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Models
public import Theory.GroupTheory.CComponent.RadicalFree

/-!
# Lifting the selected component and its section

A simple perfect normal subgroup of the self-generated subnormal actor lifts
to a relative C-component of H. Mapping its commutator identity preserves the
original transvection in H*. The section transport retains the canonical
component-star equivalence on every representative.

These lemmas perform the group and section transports; they do not assume or
assert that a component has already been recognized from the source hypotheses.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the first
paragraph of 13.8.5, printed p.947, and A.3.3(2), printed p.42.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

variable {G : Type*} [Group G] [Finite G]

/-- Lift a specified C-component, preserving its literal starred image. -/
theorem exists_lift_star_component (H : Subgroup G)
    (C : Subgroup (Source.Hstar H)) (hC : C.IsCComponent) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      Source.starImage H K = C := by
  let := pCore_isNilpotent (p := 2) (G := H)
  obtain ⟨D, hD, he⟩ := hC.exists_map_quotient_eq (pCore 2 H)
  have hd : (D.map H.subtype).subgroupOf H = D :=
    comap_map_eq_self_of_injective H.subtype_injective D
  refine ⟨D.map H.subtype, map_subtype_le D, hd.symm ▸ hD, ?_⟩
  unfold Source.starImage
  rw [hd, he]

/-- The normal simple subgroup supplied by a concrete model gives the full
self-commutator identity, not merely noncentrality, in the original H*. -/
theorem lift_simple_normal_self_commutator (H : Subgroup G)
    (J : Subgroup (Source.Hstar H)) (hJ : J.IsSubnormal)
    (t : J) (hgen : normalClosure ({t} : Set J) = ⊤)
    (C : Subgroup J) [C.Normal] [IsSimpleGroup C] [Group.IsPerfect C]
    (hnc : ¬ IsMulCommutative C) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      Source.starImage H K = C.map J.subtype ∧
      ⁅Source.starImage H K, zpowers (t : Source.Hstar H)⁆ = Source.starImage H K ∧
      Source.starImage H K ≠ ⊥ := by
  have hc : C.IsCComponent :=
    isCComponent_of_isSimpleGroup_of_isPerfect (inferInstance : C.Normal).isSubnormal
  have hc' := hc.map_subtype hJ
  obtain ⟨K, hKH, hK, he⟩ := exists_lift_star_component H _ hc'
  refine ⟨K, hKH, hK, he, ?_, he.symm ▸ hc'.ne_bot⟩
  rw [he]
  have hm := congrArg (map J.subtype) (simple_normal_self_commutator C hnc t hgen)
  simpa only [map_commutator, MonoidHom.map_zpowers, coe_subtype] using hm

variable {H V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Transfer the linear section model to the literal source section, with the
same actor identification through `Components.componentStarEquiv`. -/
theorem hasSectionModel_of_star_model
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    {B F : Type*} [Group B] [AddCommGroup F] [Module (ZMod 2) F]
    (σ : Representation (ZMod 2) B F) (eC : Source.starImage H K ≃* B)
    (hm : HasCentralSectionModel ρ (Source.starImage H K) σ eC) :
    HasSectionModel H V₃ V₁ ρ K hKH σ
      ((Components.componentStarEquiv H K hKH hK).trans eC) := by
  unfold HasCentralSectionModel at hm
  dsimp only at hm
  rw [← commutatorImage_eq_subspaceCommutator K hKH ρ hρ] at hm
  obtain ⟨hs, e, he⟩ := hm
  refine ⟨commutatorImage_invariant K hKH ρ hρ, e, ?_⟩
  intro k v
  exact he (Components.componentStarEquiv H K hKH hK
    (QuotientGroup.mk' (pCore 2 K) k)) v

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

end
