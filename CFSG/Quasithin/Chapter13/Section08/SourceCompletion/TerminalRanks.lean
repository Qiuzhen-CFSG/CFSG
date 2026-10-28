module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal.RankSourceActions

/-!
# The source rank and line conclusions at the original critical pair

The original F.9 geometry places an H-conjugate of Vγ in O₂(E), where
E = (L ⊔ T) ∩ H is the literal base edge. Its two-residual is the
parabolic residual used by 13.8.34. The actual normal C-component supplies
endpoint generation, and the source natural flag supplies noncentrality,
the kernel identity and the centralizer commutator bound. The action on
V_H/U_H and its quadraticity are constructed by `Terminal.RankSourceActions`.
Thus the marked A₆/S₆ theorem supplies the line containments and both ranks.

No comparison of the denominator indices is assumed. If that comparison
fails at the original pair, its genuine reversal exchanges the two strict
denominators. The rank-one conclusion at this reversed pair forces both
indices to be two, contradicting the failure of comparison. This returns
the conclusions for the original pair and its original transported line.

The terminal consumer removes its three separate 13.8.34 inputs. The
remaining Section 13.8 premises are the strict denominators selected after
13.8.33, the normal component and its supplement, the earlier marked plane
and natural/cover models, H = G₁, and the original fixed-pair point-normalizer
model. Their source producers must still discharge them in final assembly.
The F.9 and earlier ambient hypotheses remain those of the original setup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.27–34 and the final paragraph of 13.8.1, printed pp.963–969;
F.9.13–17, printed pp.322–324.
-/

public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalRanks
open CriticalGeometry CriticalGeometry.Reorientation
open TransvectionRecognition.Component.ModelExtension
open A6Endgame A6Endgame.IntersectionBalance
open Theory.SpecificGroups.SymmetricSix
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The actual base-edge marking. In the symmetric branch the same actor
coordinates identify the natural or augmentation module and the V₃ image.
The action witness is the literal conjugation action on U_H/V₁. -/
@[expose] def MarkedModels (H E V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)] : Prop :=
  ∃ a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁,
    (∃ e : Source.Hstar H ≃* alternatingGroup (Fin 6),
      (Source.starImage H E).map e.toMonoidHom = a6SynthemeStabilizer) ∨
    (∃ e : Source.Hstar H ≃* Equiv.Perm (Fin 6),
      (Source.starImage H E).map e.toMonoidHom = BinaryFlags.H2 ∧
      CompatibleModel H V₃ V₁ a e)

private theorem conclusions_of_comparison
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (models : MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (hcomparison : (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃) ≤
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)) :
    (c.Aone V₁ ≤ Source.UH H V₃ ∧ V₁ ≤ c.Ugamma V₃) ∧
    rank (Source.starImage H (c.Ugamma V₃)) = 1 ∧
    rank (Source.starImage H c.Vgamma) ≤ 2 := by
  let : IsElementaryAbelian 2 V := hF9.elementary
  have hg := local_earlierGeometry d hF9 c
  have hflag : normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ M := by
    have hh := Section05.PointAction.normalizer_intersection_source (localNaturalSetup d) hcentral
    simpa only [d.first_normalizer] using hh.trans inf_le_left
  have hnc := Section07.source_noncentral_VH_quotient_of_earlier_geometry
    (localNaturalSetup d) hF9 inferInstance hHz.2.1 hHz.2.2 hflag hcomm
  obtain ⟨h, _, hplace, _⟩ := exists_second_to_base c (sourceOne L T V₁)
    ((sourceOne L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) ((by decide : 2 ≤ 3).trans hg.length)
    (Comparison.local_edge d hF9) (f9_endpoint_edge_cores _ hF9 c hg.length).2 le_rfl
  have hEH : H ⊓ (L ⊔ (T : Subgroup G)) = sourceOne L T V₁ ⊔ (T : Subgroup G) :=
    (inf_comm _ _).trans (Comparison.local_edge d hF9)
  have hplace' : c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤
      (H ⊓ (L ⊔ (T : Subgroup G))).pCoreIn 2 := by
    rwa [hEH]
  obtain ⟨a, hm⟩ := models
  have hm' :
      (∃ e : Source.Hstar H ≃* alternatingGroup (Fin 6),
        (Source.starImage H (H ⊓ (L ⊔ (T : Subgroup G)))).map e.toMonoidHom =
          a6SynthemeStabilizer) ∨
      (∃ e : Source.Hstar H ≃* Equiv.Perm (Fin 6),
        (Source.starImage H (H ⊓ (L ⊔ (T : Subgroup G)))).map e.toMonoidHom =
          BinaryFlags.H2 ∧ CompatibleModel H V₃ V₁ a e) := by
    simpa only [inf_comm H] using hm
  obtain ⟨b, hb⟩ := Terminal.exists_rank_section_action d hF9 hHz.2.1 hcomm
  have hc : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ V₁ := by
    rw [commutator_comm]
    exact Section07.centralizer_UH_commutator (localNaturalSetup d) hF9
  have he : ⁅(L ⊔ (T : Subgroup G)) ⊓ H, V⁆ ≤ Source.UH H V₃ := by
    rw [Comparison.local_edge d hF9]
    exact Comparison.local_seed_commutator d hF9 hnc c
  have hkernel : Source.QH H = commutatorPreimage H (Source.UH H V₃) V₁ := by
    have hh := f9_commutatorPreimage_eq _ hF9 H le_rfl
    exact (hh.trans (inf_eq_right.mpr (map_subtype_le _))).symm
  have hh := A6Endgame.lemma_13_8_34 c (L ⊔ (T : Subgroup G))
    ((pResidual 2 ↥(H ⊓ (L ⊔ (T : Subgroup G)))).map (H ⊓ (L ⊔ (T : Subgroup G))).subtype)
    V₃ V₁ ((c.Ugamma V₃).map (MulAut.conj (h : G)).toMonoidHom)
    (c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom)
    d.seed_le (Comparison.local_seed_index d) hF9.V_le_H (d.line_le_uh H) d.line_card
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hc
    hkernel hnc (inf_le_right.trans d.normalizes_V) rfl
    hg.length hg.first_kernel hg.Vgamma_H hg.VH_endpoint
    (Section07.VH_le_core (localNaturalSetup d) hF9
      (show IsMulCommutative (Source.UH H V₃) from inferInstance)) he
    (fun c' _ hs => Terminal.component_generation d hF9 c' hgen hK hN hqs
      (Source.UH H V₃) le_rfl (not_le_of_gt hs))
    hstrict hDstrict hcomparison h rfl rfl hplace' a
    (SolvableExclusion.Three.Supercritical.Offenders.linearAction b) hb
    (Terminal.rank_section_quadratic d hF9 b c h) hm'
  exact ⟨hh.1, hh.2.1, hh.2.2.2⟩

/-- The two line containments and both rank conclusions of 13.8.34 on the
unchanged source critical pair. All action, core-placement, generation and
index-comparison inputs of the marked theorem are discharged here. -/
theorem rank_and_lines_of_source
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (models : letI := d.uh_elementary hHz
      MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃) :
    (c.Aone V₁ ≤ Source.UH H V₃ ∧ V₁ ≤ c.Ugamma V₃) ∧
    rank (Source.starImage H (c.Ugamma V₃)) = 1 ∧
    rank (Source.starImage H c.Vgamma) ≤ 2 := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hHz.2.1)
  have hc := conclusions_of_comparison d hHz hF9 hgen hK hN hqs hcentral hcomm models
  apply hc c hstrict hDstrict
  by_contra hn
  obtain ⟨r⟩ := local_exists_reversal_of_strict d hF9 c hDstrict
  have hg := local_earlierGeometry d hF9 c
  have hz := hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hUV : Source.UH H V₃ ≤ Source.VH H V := conjugateSpanBy_mono d.seed_le le_rfl
  have hγH := (map_mono hUV).trans hg.Vgamma_H
  have hUA := (hUV.trans hg.VH_endpoint).trans (SectionActions.CriticalPair.normalizes_Aone c V₁ hz)
  obtain ⟨hD, hDγ⟩ := denominators r V₃ V₁ hz hγH hUA
  have hreturn := return_map r (Source.UH H V₃) (le_normalizer_conjugateSpanBy V₃ H)
  have hend := endpoint_map r (Source.UH H V₃) (le_normalizer_conjugateSpanBy V₃ H)
  change (c.Ugamma V₃).map _ = Source.UH H V₃ at hreturn
  change r.pair.Ugamma V₃ = _ at hend
  have hrstrict : Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃) (r.pair.Aone V₁) <
      Source.UH H V₃ := by
    rw [hD]
    exact ((map_lt_map_iff_of_injective (MulAut.conj (transporter r : G)).injective).mpr
      hDstrict).trans_eq hreturn
  have hrDstrict : Source.Dgamma (r.pair.Ugamma V₃) (Source.UH H V₃) V₁ <
      r.pair.Ugamma V₃ := by
    rw [hDγ, hend]
    exact (map_lt_map_iff_of_injective (MulAut.conj (transporter r : G)).injective).mpr hstrict
  obtain ⟨hiH, hiγ⟩ := LineContainments.reversal_indices c r V₃ V₁ hz hγH hUA
  have hcomp : (Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃) (r.pair.Aone V₁)).relIndex
        (Source.UH H V₃) ≤
      (Source.Dgamma (r.pair.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (r.pair.Ugamma V₃) := by
    rw [hiH, hiγ]
    omega
  have hr := hc r.pair hrstrict hrDstrict hcomp
  have hgr := local_earlierGeometry d hF9 r.pair
  let : IsElementaryAbelian 2 (r.pair.Ugamma V₃) :=
    LineContainments.EndpointSource.elementary_Ugamma r.pair V₃
  obtain ⟨hrγ, hrH⟩ := LineContainments.indices_of_star_rank_one H (Source.UH H V₃)
    (r.pair.Ugamma V₃) (r.pair.Aone V₁) V₁ ((map_mono hUV).trans hgr.Vgamma_H)
    hr.2.1 hgr.Dgamma_kernel hrstrict hcomp
  omega

/-- The actual terminal contradiction with the three rank/line premises
removed. The point-normalizer model belongs to the same original pair;
no model for an independently chosen reversed pair is required. -/
theorem contradiction_of_marked_source
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hH : H = G₁)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hstrict : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hDstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (models : letI := d.uh_elementary hHz
      MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁)
    (point_model :
      Nonempty (Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≃* a6DuadStabilizer) ∨
      Nonempty (Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≃* duadStabilizer)) : False := by
  obtain ⟨hline, hrank, hsmall⟩ := rank_and_lines_of_source d hHz hF9 hgen hK hN hqs
    hcentral hcomm models c hstrict hDstrict
  exact Terminal.contradiction_of_point_normalizer d hHz hF9 c hH hgen hK hN hqs
    hcentral hcomm hstrict hline.2 hrank hsmall point_model

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalRanks
