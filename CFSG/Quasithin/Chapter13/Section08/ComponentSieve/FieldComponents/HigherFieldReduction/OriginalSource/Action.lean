module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.External
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison.Action

/-!
# The original external cubic action on every source section

The normal external subgroup X moves the original seed. Propagating that
identity through the H-conjugate span and its literal quotient gives
Ũ_H=[Ũ_H,X*]. The constructed S₃ centralizing K* then acts with a fixed-free
cubic, and this identity descends through every invariant subspace and its
quotient. The existing paired and tensor coordinate theorems consequently
apply to the actual source sections.

The source application constructs its faithful conjugation representation
from F.9 and discharges the group-theoretic and seed premises through the
original Borel reduction. The external FF classification and both final
contradictions remain with qt-d-138-fields-source; the original context
retains its preceding source producers through qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.20(a), printed p.954 (1 March 2004 manuscript).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalBorel LocalBorel.CentralizingCalculation
open ExternalModules
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

omit [Finite G] in
/-- The external source data and the original cubic seed identity construct
fixed-point-free S₃ coordinates on the literal source quotient. -/
theorem source_external_cubic_action
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (act : LinearThree.SourceAction H V₃ V₁)
    (X : Subgroup G) (ha : ExternalXAlternative H K X)
    (hs : ExternalSourceData H K X) (hseed : V₃ = ⁅V₃,X⁆) :
    ∃ s : Equiv.Perm (Fin 3) →* Source.Hstar H,
      Function.Injective s ∧
      s.range ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
      (alternatingGroup (Fin 3)).map s = Source.starImage H X ∧
      subspaceCommutator act.representation ⊤ (Source.starImage H X) = ⊤ ∧
      (∀ v, act.representation (s InvertedCubicTensor.cubic) v = v → v = 0) ∧
      ∀ (A B : Subrepresentation act.representation) v,
        sectionRepresentation act.representation A B (s InvertedCubicTensor.cubic) v = v →
          v = 0 := by
  obtain ⟨_,_,_,_,_,_,_,_,s,hi,hc,hm⟩ := hs
  let : (X.subgroupOf H).Normal := ha.2.2.2.1
  have hg := Structure.source_commutator_generation H X V₃ V₁ ha.1
    act.representation act.conjugation hseed
  exact ⟨s,hi,hc,hm,hg,
    Structure.cubic_fixedFree act.representation (Source.starImage H X) s hm hg,
    Structure.section_cubic_fixedFree act.representation (Source.starImage H X) s hm hg⟩

/-- The original higher-field setup supplies its literal faithful action and,
in the external branch, a commuting cubic with no fixed vectors on any
invariant section. Every extra group-theoretic premise is discharged. -/
theorem source_higher_field_action
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    letI : IsElementaryAbelian 2 (Source.UH H V₃) :=
      c.localSetup.uh_elementary c.component.local_overgroup
    ∃ act : LinearThree.SourceAction H V₃ V₁,
      Function.Injective act.representation ∧
      ((∃ (X : Subgroup G) (s : Equiv.Perm (Fin 3) →* Source.Hstar H),
          ExternalXAlternative H K X ∧ ExternalSourceData H K X ∧
          Function.Injective s ∧
          s.range ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
          (alternatingGroup (Fin 3)).map s = Source.starImage H X ∧
          subspaceCommutator act.representation ⊤ (Source.starImage H X) = ⊤ ∧
          (∀ v, act.representation (s InvertedCubicTensor.cubic) v = v → v = 0) ∧
          ∀ (A B : Subrepresentation act.representation) v,
            sectionRepresentation act.representation A B (s InvertedCubicTensor.cubic) v = v →
              v = 0) ∨
        ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
          ExceptionalOuterAlternative.{u,0} H K
            (QuotientGroup.mk' (pCore 2 H)
              ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩)) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) :=
    c.localSetup.uh_elementary c.component.local_overgroup
  have hF9 := c.f9 H c.component.local_overgroup
  let act := Comparison.conjugationAction (c.localSetup.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  refine ⟨act,f9_section_faithful _ hF9 (Comparison.sourceSection act hF9.H_centralizes),?_⟩
  obtain ⟨_,_,_,X,t,_,_,hseed,hb⟩ := source_borel_structure c hfield
  rcases hb with ⟨hx,_,hs⟩ | ho
  · obtain ⟨s,hi,hc,hm,hgen,hf,hsf⟩ := source_external_cubic_action act X hx.1 hs hseed
    exact Or.inl ⟨X,s,hx.1,hs,hi,hc,hm,hgen,hf,hsf⟩
  · exact Or.inr ⟨t,ho⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
