module

public import Theory.Representation.BinaryOffender.CommonCenterEquality
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.QuadraticBound
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.LocalModels.ChosenGeometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Action


/-!
# The equality case of F.9.16 on the original critical denominator

The actual Uγ-star action stabilizes the image of D_H in U_H/V₁,
with displacement in the image of A₁ and with that line fixed. Equality
in the doubled codimension bound forces equal denominator and actor
ranks, and makes the action on that same D_H image faithful. Nonidentity
actors have explicit transvection forms whose centers lie in the original
A₁ image. The corresponding literal action kernel is therefore trivial.

The standing 13.8 consumer derives the critical length and elementary
section hypotheses from its genuine earlier source setup. No kernel,
faithfulness or transvection conclusion is an added premise.
Source: Aschbacher–Smith, F.9.16(2), equality addendum, printed pp.323–324;
application to the original 13.8 critical-pair configuration, pp.946–949.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G E:Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

theorem f9_denominator_action (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length)
    {ρ:Representation (ZMod 2) (Source.Hstar D.H) E}
    (s:ConjugationSection D.H D.UH D.V₁ ρ) :
    ∃ W:Subrepresentation (ρ.comp (Source.starImage D.H (c.Ugamma D.Vplus)).subtype),
      W.toSubmodule=s.image (Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁)) ∧
      Module.finrank (ZMod 2) (s.image (c.Aone D.V₁))≤1 ∧
      (∀ b:Source.starImage D.H (c.Ugamma D.Vplus),∀v∈W.toSubmodule,
        ρ b v-v∈s.image (c.Aone D.V₁)) ∧
      (∀ b:Source.starImage D.H (c.Ugamma D.Vplus),∀z∈s.image (c.Aone D.V₁),ρ b z=z) := by
  let Ug:=c.Ugamma D.Vplus
  let A:=c.Aone D.V₁
  let Dh:=Source.DH D.UH Ug A
  let B:=Source.starImage D.H Ug
  have huv:D.UH≤Source.VH D.H D.V:=conjugateSpanBy_mono h.plus_le le_rfl
  have hends:=f9_endpoint_spans D h c hb
  have hUgH:Ug≤D.H := (map_mono huv).trans hends.2
  have hUA:D.UH≤normalizer (A:Set G) := by
    apply le_trans (huv.trans hends.1)
    change vertexGroup _ _ _ c.gamma≤normalizer (c.Aone D.V₁:Set G)
    rw [c.vertexGroup_gamma,CriticalPair.Aone,←map_equiv_normalizer_eq]
    exact map_mono (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hUgA:Ug≤centralizer (A:Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    change ⁅D.UH.map (MulAut.conj (c.gb:G)).toMonoidHom,D.V₁.map (MulAut.conj (c.gb:G)).toMonoidHom⁆=⊥
    rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr (h.UH_le_H.trans h.H_centralizes),Subgroup.map_bot]
  have hn:Ug≤normalizer (Dh:Set G) :=
    commutatorPreimage_normalized _ _ _ _ hUA (hUgH.trans s.normalizes)
      Ug.le_normalizer (hUgA.trans (Subgroup.centralizer_le_normalizer _))
  let τ:=ρ.comp B.subtype
  let W:Subrepresentation τ := {
    toSubmodule:=s.image Dh
    apply_mem_toSubmodule:=by
      rintro ⟨b,hb⟩ v hv
      obtain ⟨a,ha,rfl⟩:=hb
      obtain ⟨u,hu,rfl⟩:=(s.mem_image Dh v).mp hv
      change ρ (QuotientGroup.mk' (pCore 2 D.H) a) (s.quotient u).toAdd∈s.image Dh
      rw [s.conjugates]
      exact ⟨_,(mem_normalizer_iff.mp (hn ha) u).mp hu,rfl⟩ }
  have hcardA:Nat.card A=2 := by
    exact (Nat.card_congr ((MulAut.conj (c.gb:G)).subgroupMap D.V₁).toEquiv.symm).trans h.point_card
  obtain ⟨hdim,hdisp⟩:=s.critical_line_displacement Ug A hUA hcardA
  have hfixed:∀b:B,∀z∈s.image A,τ b z=z := by
    rintro ⟨b,hb⟩ z hz
    obtain ⟨a,ha,rfl⟩:=hb
    obtain ⟨u,hu,rfl⟩:=(s.mem_image A z).mp hz
    apply sub_eq_zero.mp
    change ρ (QuotientGroup.mk' (pCore 2 D.H) a) (s.quotient u).toAdd-(s.quotient u).toAdd=0
    rw [s.displacement]
    apply (s.quotient_eq_zero_iff _).mpr
    have hc:⁅(a:G),(u:G)⁆=1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((hUgA ha) u hu).symm
    change ⁅(a:G),(u:G)⁆∈D.V₁
    rw [hc]
    exact D.V₁.one_mem
  exact ⟨W,rfl,hdim,(fun b v hv=>hdisp b b.property v hv),hfixed⟩

theorem f9_denominator_equality (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length)
    [IsElementaryAbelian 2 D.UH]
    {ρ:Representation (ZMod 2) (Source.Hstar D.H) E}
    (s:ConjugationSection D.H D.UH D.V₁ ρ)
    (hcomparison:Reorientation.denominatorRank D.Vplus D.V₁ c≤rank (Source.starImage D.H (c.Ugamma D.Vplus)))
    (he:fixedCodim ρ (Source.starImage D.H (c.Ugamma D.Vplus))=
      2*rank (Source.starImage D.H (c.Ugamma D.Vplus))) :
    ∃ W:Subrepresentation (ρ.comp (Source.starImage D.H (c.Ugamma D.Vplus)).subtype),
      W.toSubmodule=s.image (Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁)) ∧
      Reorientation.denominatorRank D.Vplus D.V₁ c=rank (Source.starImage D.H (c.Ugamma D.Vplus)) ∧
      Function.Injective W.toRepresentation ∧
      ∀b:Source.starImage D.H (c.Ugamma D.Vplus),b≠1 →
        ∃ (f:Module.Dual (ZMod 2) W.toSubmodule) (z:W.toSubmodule),
          f≠0 ∧ z≠0 ∧ (z:E)∈s.image (c.Aone D.V₁) ∧ f z=0 ∧
          ∀v,W.toRepresentation b v=v+f v • z := by
  let Ug:=c.Ugamma D.Vplus
  let A:=c.Aone D.V₁
  let Dh:=Source.DH D.UH Ug A
  let B:=Source.starImage D.H Ug
  have huv:D.UH≤Source.VH D.H D.V:=conjugateSpanBy_mono h.plus_le le_rfl
  have hUgH:Ug≤D.H := (map_mono huv).trans (f9_endpoint_spans D h c hb).2
  let : IsElementaryAbelian 2 (Source.UH D.H D.Vplus):=‹IsElementaryAbelian 2 D.UH›
  let : IsElementaryAbelian 2 Ug:=IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B:=starImage_isElementaryAbelian D.H Ug hUgH
  let τ:=ρ.comp B.subtype
  obtain ⟨W,hW,hZ,hd,hz⟩:=f9_denominator_action D h c hb s
  have hcodim:fixedCodim τ ⊤=fixedCodim ρ B := by
    change Module.finrank (ZMod 2) (E ⧸ fixedSpace (ρ.comp B.subtype) ⊤)=_
    rw [fixedSpace_comp_map,←MonoidHom.range_eq_map,B.range_subtype]
    rfl
  have hdenom:Module.finrank (ZMod 2) (E ⧸ W.toSubmodule)=Reorientation.denominatorRank D.Vplus D.V₁ c := by
    rw [hW]
    exact s.quotient_finrank Dh (s.line_le_DH Ug A hUgH)
  obtain ⟨hr,hfaith⟩:=CommonCenter.equality_of_doubled_bound τ W (s.image A) hZ hd hz
    (by rw [hdenom];exact hcomparison) (by rw [hcodim];exact he)
  refine ⟨W,hW,hdenom.symm.trans hr,hfaith,?_⟩
  intro b hb1
  let Z':Submodule (ZMod 2) W.toSubmodule:=(s.image A).comap W.toSubmodule.subtype
  have hZ':Module.finrank (ZMod 2) Z'≤1 := by
    have hh:Module.finrank (ZMod 2) Z'=Module.finrank (ZMod 2)
        (W.toSubmodule⊓s.image A : Submodule (ZMod 2) E) := by
      rw [←Submodule.finrank_map_subtype_eq,Submodule.map_comap_subtype]
    exact hh.le.trans ((Submodule.finrank_mono inf_le_right).trans hZ)
  exact CommonCenter.common_center_form_of_ne_one W.toRepresentation Z' hZ'
    (fun b v=>hd b v v.property) (fun b z hz'=>Subtype.ext (hz b z hz')) hfaith b hb1

theorem f9_denominator_equality_kernel (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length)
    [IsElementaryAbelian 2 D.UH]
    {ρ:Representation (ZMod 2) (Source.Hstar D.H) E}
    (s:ConjugationSection D.H D.UH D.V₁ ρ)
    (hcomparison:Reorientation.denominatorRank D.Vplus D.V₁ c≤rank (Source.starImage D.H (c.Ugamma D.Vplus)))
    (he:fixedCodim ρ (Source.starImage D.H (c.Ugamma D.Vplus))=
      2*rank (Source.starImage D.H (c.Ugamma D.Vplus))) :
    Reorientation.denominatorRank D.Vplus D.V₁ c=rank (Source.starImage D.H (c.Ugamma D.Vplus)) ∧
      subspaceKernel ρ (s.image (Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁)))
        (Source.starImage D.H (c.Ugamma D.Vplus))=⊥ := by
  obtain ⟨W,hW,hr,hfaith,_⟩:=f9_denominator_equality D h c hb s hcomparison he
  refine ⟨hr,(subspaceKernel_eq_bot_iff _ _ _).mpr ?_⟩
  intro b hb hfix
  have hh:W.toRepresentation (⟨b,hb⟩:Source.starImage D.H (c.Ugamma D.Vplus))=W.toRepresentation 1 := by
    rw [map_one]
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact hfix v (hW ▸ v.property)
  exact congrArg Subtype.val (hfaith hh)



/-- The explicit forms give the existing transvection predicate on the
same denominator module, while retaining its exact source-subspace mark. -/
theorem f9_denominator_transvections (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length)
    [IsElementaryAbelian 2 D.UH]
    {ρ:Representation (ZMod 2) (Source.Hstar D.H) E}
    (s:ConjugationSection D.H D.UH D.V₁ ρ)
    (hcomparison:Reorientation.denominatorRank D.Vplus D.V₁ c≤rank (Source.starImage D.H (c.Ugamma D.Vplus)))
    (he:fixedCodim ρ (Source.starImage D.H (c.Ugamma D.Vplus))=
      2*rank (Source.starImage D.H (c.Ugamma D.Vplus))) :
    ∃ W:Subrepresentation (ρ.comp (Source.starImage D.H (c.Ugamma D.Vplus)).subtype),
      W.toSubmodule=s.image (Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁)) ∧
      Function.Injective W.toRepresentation ∧
      ∀b:Source.starImage D.H (c.Ugamma D.Vplus),b≠1 →
        TransvectionRecognition.IsTransvection W.toRepresentation b := by
  obtain ⟨W,hW,_,hf,hforms⟩:=f9_denominator_equality D h c hb s hcomparison he
  refine ⟨W,hW,hf,?_⟩
  intro b hb1
  obtain ⟨f,z,hf0,hz0,_,hfz,heq⟩:=hforms b hb1
  exact ⟨f,z,hf0,hz0,hfz,heq⟩

open TransvectionRecognition.Component.ModelExtension
/-- The standing 13.8 setup supplies the length and elementary section
hypotheses for the literal faithful-denominator conclusion. -/
theorem local_denominator_equality_kernel
    {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
    (d:LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH:H∈Source.Hz (sourceOne L T V₁) (T:Subgroup G) G₁ M)
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c:CriticalPair L (T:Subgroup G) H V)
    {ρ:Representation (ZMod 2) (Source.Hstar H) E}
    (s:ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hcomparison:Reorientation.denominatorRank V₃ V₁ c≤rank (Source.starImage H (c.Ugamma V₃)))
    (he:fixedCodim ρ (Source.starImage H (c.Ugamma V₃))=2*rank (Source.starImage H (c.Ugamma V₃))) :
    Reorientation.denominatorRank V₃ V₁ c=rank (Source.starImage H (c.Ugamma V₃)) ∧
      subspaceKernel ρ (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)))
        (Source.starImage H (c.Ugamma V₃))=⊥ := by
  let : IsElementaryAbelian 2 (Source.UH H V₃):=d.uh_elementary hH
  let : IsElementaryAbelian 2 (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH :=
    show IsElementaryAbelian 2 (Source.UH H V₃) from inferInstance
  exact f9_denominator_equality_kernel _ hF9 c
    (local_earlierGeometry d hF9 c).length s hcomparison he

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion

end
