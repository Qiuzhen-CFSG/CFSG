module

public import Theory.Representation.BinaryOffender.CommonCenterBound
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EarlierGeometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Selection

/-!
# The source F.9.16 codimension bound and quadratic selection

On the image of DH in UH/V1, the actual U-gamma star action has displacement
in the image of A1 and fixes that line. The common-center dimension bound
therefore gives fixed codimension at most the actor rank plus the original
denominator rank. The source numerical comparison gives the factor-two
bound. Faithfulness is derived from the F.9.2 kernel equality.

The NaturalSetup consumer derives elementary abelianness from the genuine
abelian full V-span. In the strict-denominator branch it applies the existing
actual reversal and rank selection, with every geometry, faithfulness,
quadratic-action and codimension callback discharged. The earlier 13.7.8
and 13.5.7 inputs remain precisely as in the source.

Source: Aschbacher--Smith, F.9.16(2), first assertion, and (4), applied in
the strict branch of 13.8.8, printed pp.323--324,949. This module does not
assert the additional equality-case conclusions of F.9.16(2).
-/

public section
open Subgroup Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open CriticalGeometry
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G E:Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

omit [FiniteDimensional (ZMod 2) E] in
theorem f9_section_faithful (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    {ρ:Representation (ZMod 2) (Source.Hstar D.H) E}
    (s:ConjugationSection D.H D.UH D.V₁ ρ) : Function.Injective ρ := by
  apply ρ.ker_eq_bot_iff.mp
  apply bot_unique
  intro a ha
  obtain ⟨x,rfl⟩:=QuotientGroup.mk'_surjective (pCore 2 D.H) a
  change ρ (QuotientGroup.mk' (pCore 2 D.H) x)=1 at ha
  have hx:(x:G)∈h.kernel D.UH := by
    apply (h.mem_kernel_iff h.UH_le_H).mpr
    refine ⟨x.property,fun u hu=>?_⟩
    have hc:⁅(x:G),u⁆∈D.V₁ := by
      apply (s.quotient_eq_zero_iff ⟨⁅(x:G),u⁆,s.commutator_mem x ⟨u,hu⟩⟩).mp
      rw [←s.displacement x ⟨u,hu⟩,ha]
      exact sub_self _
    simpa only [commutatorElement_inv] using D.V₁.inv_mem hc
  rw [h.kernel_UH_eq_QH] at hx
  obtain ⟨y,hy,he⟩:=hx
  have hyx:y=x:=Subtype.ext he
  exact (QuotientGroup.eq_one_iff x).mpr (hyx ▸ hy)

theorem f9_fixedCodim_le_rank_add_denominator (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length)
    [IsElementaryAbelian 2 D.UH]
    {ρ:Representation (ZMod 2) (Source.Hstar D.H) E}
    (s:ConjugationSection D.H D.UH D.V₁ ρ) :
    fixedCodim ρ (Source.starImage D.H (c.Ugamma D.Vplus))≤
      rank (Source.starImage D.H (c.Ugamma D.Vplus))+
        Reorientation.denominatorRank D.Vplus D.V₁ c := by
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
  let : IsElementaryAbelian 2 (Source.UH D.H D.Vplus):=‹IsElementaryAbelian 2 D.UH›
  let : IsElementaryAbelian 2 Ug:=IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B:=starImage_isElementaryAbelian D.H Ug hUgH
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
  have hbound:=CommonCenter.fixedCodim_top_le_rank_add_codim τ W (s.image A) hdim
    (fun b v hv=>hdisp b b.property v hv) hfixed
  have hcodim:fixedCodim τ ⊤=fixedCodim ρ B := by
    change Module.finrank (ZMod 2) (E ⧸ fixedSpace (ρ.comp B.subtype) ⊤)=_
    rw [fixedSpace_comp_map,←MonoidHom.range_eq_map,B.range_subtype]
    rfl
  rw [hcodim] at hbound
  have hdenom:Module.finrank (ZMod 2) (E ⧸ W.toSubmodule)=Reorientation.denominatorRank D.Vplus D.V₁ c :=
    s.quotient_finrank Dh (s.line_le_DH Ug A hUgH)
  rw [hdenom] at hbound
  exact hbound

theorem f9_fixedCodim_le_twice_rank (D:ChapterF.Section09.Setup G) (h:D.Hypothesis)
    (c:CriticalPair D.L (D.T:Subgroup G) D.H D.V) (hb:3≤c.path.length)
    [IsElementaryAbelian 2 D.UH]
    {ρ:Representation (ZMod 2) (Source.Hstar D.H) E}
    (s:ConjugationSection D.H D.UH D.V₁ ρ)
    (hcomparison:Reorientation.denominatorRank D.Vplus D.V₁ c≤rank (Source.starImage D.H (c.Ugamma D.Vplus))) :
    fixedCodim ρ (Source.starImage D.H (c.Ugamma D.Vplus))≤
      2*rank (Source.starImage D.H (c.Ugamma D.Vplus)) := by
  have hh:=f9_fixedCodim_le_rank_add_denominator D h c hb s
  omega

namespace NaturalSetup
variable {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}

theorem fixedCodim_le_twice_rank (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hspan:IsMulCommutative (conjugateSpanBy V G₁))
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {ρ:Representation (ZMod 2) (Source.Hstar H) E}
    (s:ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (c:CriticalPair L (T:Subgroup G) H V)
    (hcomparison:Reorientation.denominatorRank V₃ V₁ c≤rank (Source.starImage H (c.Ugamma V₃))) :
    fixedCodim ρ (Source.starImage H (c.Ugamma V₃))≤2*rank (Source.starImage H (c.Ugamma V₃)) := by
  have hHG:H≤G₁ := by
    rw [d.first_normalizer]
    exact hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  let : IsMulCommutative (conjugateSpanBy V G₁):=hspan
  let : IsElementaryAbelian 2 V:=hF9.elementary
  let : IsElementaryAbelian 2 V₃:=IsElementaryAbelian.of_le d.seed_le
  let : IsMulCommutative (conjugateSpanBy V₃ H):=
    conjugateSpanBy_isMulCommutative_of_le d.seed_le hHG
  let : IsElementaryAbelian 2 (Source.UH H V₃):=
    conjugateSpanBy_elementary_of_commutative V₃ H
  let : IsElementaryAbelian 2 (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).UH :=
    show IsElementaryAbelian 2 (Source.UH H V₃) from inferInstance
  exact f9_fixedCodim_le_twice_rank _ hF9 c (d.earlierGeometry hspan hF9 c).length s hcomparison

/-- The strict branch selects an actual positive quadratic actor, with the
F.9.16 estimate and all geometric prerequisites proved on the source data. -/
theorem exists_quadratic_selection (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hspan:IsMulCommutative (conjugateSpanBy V G₁))
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    {ρ:Representation (ZMod 2) (Source.Hstar H) E}
    (s:ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (c:CriticalPair L (T:Subgroup G) H V)
    (hDH:Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)<Source.UH H V₃)
    (hDγ:Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁<c.Ugamma V₃) :
    ∃c':CriticalPair L (T:Subgroup G) H V,
      Source.DH (Source.UH H V₃) (c'.Ugamma V₃) (c'.Aone V₁)<Source.UH H V₃ ∧
      Source.Dgamma (c'.Ugamma V₃) (Source.UH H V₃) V₁<c'.Ugamma V₃ ∧
      0<rank (Source.starImage H (c'.Ugamma V₃)) ∧
      Reorientation.denominatorRank V₃ V₁ c'≤rank (Source.starImage H (c'.Ugamma V₃)) ∧
      Reorientation.QuadraticMember ρ (Source.starImage H (c'.Ugamma V₃)) := by
  have hHG:H≤G₁ := by
    rw [d.first_normalizer]
    exact hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  let : IsMulCommutative (conjugateSpanBy V G₁):=hspan
  let : IsElementaryAbelian 2 V:=hF9.elementary
  let : IsMulCommutative (conjugateSpanBy V H):=
    conjugateSpanBy_isMulCommutative_of_le le_rfl hHG
  let : IsElementaryAbelian 2 (Source.VH H V):=
    conjugateSpanBy_elementary_of_commutative V H
  let : IsElementaryAbelian 2 (conjugateSpanBy V H):=‹IsElementaryAbelian 2 (Source.VH H V)›
  let : IsElementaryAbelian 2 (Source.UH H V₃):=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono d.seed_le (show H≤H from le_rfl))
  have hg:=d.earlierGeometry hspan hF9 c
  exact Reorientation.exists_quadratic_selection V₃ V₁ c s (f9_section_faithful _ hF9 s)
    hg.length d.seed_le (fun c'=>(d.earlierGeometry hspan hF9 c').Vgamma_H)
    ((conjugateSpanBy_mono d.seed_le le_rfl).trans hg.VH_endpoint) hg.first_kernel hDH hDγ
    (fun c'=>(c'.quadratic_star_on_Utilde V₃ V₁ s d.seed_le
      (d.earlierGeometry hspan hF9 c').VH_endpoint).2)
    (fun c' _ hc=>d.fixedCodim_le_twice_rank hspan hF9 s c' hc)

end NaturalSetup
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
