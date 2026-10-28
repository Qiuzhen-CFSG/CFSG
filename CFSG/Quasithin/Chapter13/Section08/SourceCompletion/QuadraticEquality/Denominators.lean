module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.QuadraticEquality


/-!
# The literal critical denominators in the F.9 equality case

Faithfulness on the original D_H image puts every Uγ element centralizing
D_H in Dγ. In the standing A₆ source configuration, the proved critical
geometry gives the reverse containment. The resulting equality is
C_{Uγ}(D_H)=Dγ. The actor-image cardinality is also identified with the
literal relative index |Uγ:Dγ|, so the two original denominator ranks are
equal, without substituting an abstract section or subgroup model.

Source: Aschbacher–Smith, proof of F.9.16(2), printed p.324;
application in the original Section 13.8 configuration, pp.946–949.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G E:Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

theorem f9_equality_centralizer_le_Dgamma (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length)
    [IsElementaryAbelian 2 D.UH]
    {ρ:Representation (ZMod 2) (Source.Hstar D.H) E}
    (s:ConjugationSection D.H D.UH D.V₁ ρ)
    (hcomparison:Reorientation.denominatorRank D.Vplus D.V₁ c≤rank (Source.starImage D.H (c.Ugamma D.Vplus)))
    (he:fixedCodim ρ (Source.starImage D.H (c.Ugamma D.Vplus))=
      2*rank (Source.starImage D.H (c.Ugamma D.Vplus))) :
    c.Ugamma D.Vplus ⊓ centralizer (Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁):Set G) ≤
      Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁ := by
  let Ug:=c.Ugamma D.Vplus
  let Dh:=Source.DH D.UH Ug (c.Aone D.V₁)
  have huv:D.UH≤Source.VH D.H D.V:=conjugateSpanBy_mono h.plus_le le_rfl
  have hUgH:Ug≤D.H := (map_mono huv).trans (f9_endpoint_spans D h c hb).2
  have hk:subspaceKernel ρ (s.image Dh) (Source.starImage D.H Ug)=⊥ :=
    (f9_denominator_equality_kernel D h c hb s hcomparison he).2
  rw [s.Dgamma_eq_inf_core Ug hUgH (f9_section_faithful D h s)]
  intro x hx
  refine ⟨hx.1,?_⟩
  let a:D.H:=⟨x,hUgH hx.1⟩
  have hi:QuotientGroup.mk' (pCore 2 D.H) a ∈ Source.starImage D.H Ug := ⟨a,hx.1,rfl⟩
  have hfix:∀v∈s.image Dh,ρ (QuotientGroup.mk' (pCore 2 D.H) a) v=v := by
    intro v hv
    obtain ⟨u,hu,rfl⟩:=(s.mem_image Dh v).mp hv
    apply sub_eq_zero.mp
    rw [s.displacement]
    apply (s.quotient_eq_zero_iff _).mpr
    have hc:⁅x,(u:G)⁆=1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((mem_centralizer_iff.mp hx.2 u hu).symm)
    change ⁅x,(u:G)⁆∈D.V₁
    rw [hc]
    exact D.V₁.one_mem
  have hq:QuotientGroup.mk' (pCore 2 D.H) a=1 :=
    (subspaceKernel_eq_bot_iff _ _ _).mp hk _ hi hfix
  exact ⟨a,(QuotientGroup.eq_one_iff a).mp hq,rfl⟩

open TransvectionRecognition.Component.ModelExtension
/-- The literal two relative-index ranks are equal, and Dγ is exactly
C_{Uγ}(D_H), in the unchanged original standing source groups. -/
theorem local_equality_denominators
    {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
    (d:LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH:H∈Source.Hz (sourceOne L T V₁) (T:Subgroup G) G₁ M)
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c:CriticalPair L (T:Subgroup G) H V)
    {ρ:Representation (ZMod 2) (Source.Hstar H) E}
    (s:ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hcomparison:Reorientation.denominatorRank V₃ V₁ c≤rank (Source.starImage H (c.Ugamma V₃)))
    (he:fixedCodim ρ (Source.starImage H (c.Ugamma V₃))=2*rank (Source.starImage H (c.Ugamma V₃))) :
    Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)) =
      Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex (Source.UH H V₃)) ∧
    c.Ugamma V₃ ⊓ centralizer (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁):Set G) =
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ := by
  let : IsElementaryAbelian 2 (Source.UH H V₃):=d.uh_elementary hH
  let : IsElementaryAbelian 2 (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH :=
    show IsElementaryAbelian 2 (Source.UH H V₃) from inferInstance
  have hg:=local_earlierGeometry d hF9 c
  have huv:Source.UH H V₃≤Source.VH H V:=conjugateSpanBy_mono d.seed_le le_rfl
  have hUgH:c.Ugamma V₃≤H := (map_mono huv).trans hg.Vgamma_H
  have hr:Reorientation.denominatorRank V₃ V₁ c=rank (Source.starImage H (c.Ugamma V₃)) :=
    (local_denominator_equality_kernel d hH hF9 c s hcomparison he).1
  refine ⟨?_,le_antisymm (f9_equality_centralizer_le_Dgamma _ hF9 c hg.length s hcomparison he) ?_⟩
  · rw [s.Dgamma_relIndex _ hUgH (f9_section_faithful _ hF9 s)]
    exact hr.symm
  · apply le_inf (commutatorPreimage_le _ _ _)
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [commutator_comm]
    exact hg.cross_centralizes

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion

end
