module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison.Geometry
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.MarkedParabolic
public import CFSG.Quasithin.Chapter13.Section07.SpanGrowth
public import CFSG.Quasithin.Chapter13.Section05.PointAction

/-!
# The literal terminal contradiction in Section 13.8

The equality H = G₁ identifies the actual terminal vertex with the full
normalizer of the transported order-two line A₁. Consequently the images
Uγ* and Vγ* are relatively normal in its image in H/O₂(H); neither ambient
normality nor an unproved equality with a module stabilizer is used.

The actual C-component supplies endpoint generation for every subgroup
outside D_H. Applied to U_H, this proves Uγ* < Vγ* from V₁ ≤ Uγ, using
13.8.11(1). The natural source flag and the earlier ambient centralizer
and commutator assumptions discharge noncentrality of V_H/U_H. The
13.8.34 ranks give |Uγ*| = 2 and |Vγ*| ≤ 4, contradicting the normal
subgroups of the A₆ or S₆ point parabolic.

This is a conditional terminal consumer, not a proof of 13.8.1. Its
Section 13.8 inputs remain H = G₁, the normal component supplement and
its quasisimple star image, strictness of D_H, the three indicated
13.8.34 conclusions, and an actual model of the line-normalizer image.
In particular the last model must still be obtained from the recognized
natural or cover action with its correct marking. The original earlier
F.9, 13.5.4 and 13.7.8 inputs remain explicit through LocalSetup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.18(1), 13.8.27 and the final paragraph of 13.8.1,
printed pp.953,963,968–969 (PDF pp.970,980,985–986).
-/

public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal
open CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The terminal vertex is the full normalizer of the original transported
line when 13.8.27 gives H = G₁. -/
theorem endpoint_eq_line_normalizer
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁) :
    vertexGroup L (T : Subgroup G) H c.gamma = normalizer (c.Aone V₁ : Set G) := by
  rw [c.vertexGroup_gamma, CriticalPair.Aone, ← map_equiv_normalizer_eq]
  exact congrArg (Subgroup.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hH.trans d.first_normalizer)

omit [Finite G] in
private theorem star_normalizes (A B : Subgroup G)
    (hn : A ≤ normalizer (B : Set G)) :
    Source.starImage H A ≤ normalizer (Source.starImage H B : Set (Source.Hstar H)) := by
  apply (map_mono (show A.subgroupOf H ≤ normalizer (B.subgroupOf H : Set H) from ?_)).trans
    (le_normalizer_map _)
  apply le_normalizer_iff.mpr
  intro a ha b hb
  exact le_normalizer_iff.mp hn a ha b hb

/-- Both actual star subgroups are normal in the image of the line
normalizer. The intersection with H is retained by `starImage`. -/
theorem endpoint_star_normality
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁) :
    Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≤
        normalizer (Source.starImage H (c.Ugamma V₃) : Set (Source.Hstar H)) ∧
    Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≤
        normalizer (Source.starImage H c.Vgamma : Set (Source.Hstar H)) := by
  rw [← endpoint_eq_line_normalizer d c hH]
  exact ⟨star_normalizes _ _ (c.normalizes_Ugamma V₃),
    star_normalizes _ _ (c.normalizes_Ugamma V)⟩

/-- The every-F generation assertion of 13.8.18(1) on the original
critical pair. Endpoint normality, two-perfectness and the quotient
comparison are transported from the actual source component. -/
theorem component_generation
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K)) :
    ∀ F : Subgroup G, F ≤ Source.UH H V₃ →
      ¬ F ≤ Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) →
      vertexGroup L (T : Subgroup G) H c.gamma =
        conjugateSpanBy F (vertexGroup L (T : Subgroup G) H c.gamma) ⊔
          edgeGroup L (T : Subgroup G) H c.gamma c.previous := by
  let := hK.perfect
  have hKH : K ≤ H := hgen ▸ le_sup_left
  have hg := local_earlierGeometry d hF9 c
  have hc := Comparison.component_conjugate H K hKH hN hqs (MulAut.conj (c.gb : G))
  have hu : Source.UH H V₃ ≤
      (edgeGroup L (T : Subgroup G) H c.gamma c.previous).pCoreIn 2 := by
    have hh := (f9_endpoint_edge_cores _ hF9 c hg.length).1
    change Source.VH H V ≤ (vertexGroup _ _ _ c.previous ⊓ vertexGroup _ _ _ c.gamma).pCoreIn 2 at hh
    rw [inf_comm] at hh
    exact (conjugateSpanBy_mono d.seed_le le_rfl).trans hh
  exact c.generation_all (sourceOne L T V₁) K V₃ V₁ hgen (Comparison.local_edge d hF9)
    (by rw [c.vertexGroup_gamma]; exact hc.1)
    (by rw [c.vertexGroup_gamma]; exact hc.2.1)
    (by rw [c.vertexGroup_gamma]; exact hc.2.2) hu hg.DH_kernel

/-- The last paragraph of 13.8.1, applied to the literal critical pair.
The component and selected-pair conclusions are earlier Section 13.8
inputs. Only the actual image of the transported line normalizer may be
identified with the point parabolic; an abstract H-star model is insufficient. -/
theorem contradiction_of_point_normalizer
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
    (hline : V₁ ≤ c.Ugamma V₃)
    (hrank : rank (Source.starImage H (c.Ugamma V₃)) = 1)
    (hsmall : rank (Source.starImage H c.Vgamma) ≤ 2)
    (model :
      Nonempty (Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≃* a6DuadStabilizer) ∨
      Nonempty (Source.starImage H (normalizer (c.Aone V₁ : Set G)) ≃* duadStabilizer)) : False := by
  let : IsElementaryAbelian 2 V := hF9.elementary
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁) := d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hHz.2.1)
  let : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have hg := local_earlierGeometry d hF9 c
  have hUV : Source.UH H V₃ ≤ Source.VH H V := conjugateSpanBy_mono d.seed_le le_rfl
  have hUgH : c.Ugamma V₃ ≤ H := (map_mono hUV).trans hg.Vgamma_H
  have hne : Source.starImage H (c.Ugamma V₃) ≠ ⊥ := by
    intro he
    rw [he, Representation.BinaryOffender.rank_bot] at hrank
    contradiction
  have hflag : normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤ M := by
    have hh := Section05.PointAction.normalizer_intersection_source (localNaturalSetup d) hcentral
    simpa only [d.first_normalizer] using hh.trans inf_le_left
  have hnoncentral := Section07.source_noncentral_VH_quotient_of_earlier_geometry
    (localNaturalSetup d) hF9 inferInstance hHz.2.1 hHz.2.2 hflag hcomm
  have hgenerate := component_generation d hF9 c hgen hK hN hqs
    (Source.UH H V₃) le_rfl (not_le_of_gt hstrict)
  have hlt := (SectionActions.CriticalPair.strict_star_of_line_or_no_v_transvection c
    V₃ V₁ d.seed_le hF9.V_le_H hg.Vgamma_H (hUV.trans hg.VH_endpoint)
    (d.line_le_uh H) (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point d.line_card hgenerate
    (c.edge_commutator_le_of_flag V₃ d.seed_le (Comparison.local_seed_index d)
      hnoncentral (inf_le_left.trans d.normalizes_V)) hnoncentral hne (Or.inl hline)).1
  have hVP : Source.starImage H c.Vgamma ≤
      Source.starImage H (normalizer (c.Aone V₁ : Set G)) := by
    apply map_mono (subgroupOf_mono H ?_)
    rw [← endpoint_eq_line_normalizer d c hH, c.vertexGroup_gamma]
    exact map_mono (conjugateSpanBy_le_self hF9.V_le_H)
  have hU : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)) :=
    ⟨hne, starImage_isElementaryAbelian H _ hUgH⟩
  have hV : IsElementaryTwo (Source.starImage H c.Vgamma) :=
    ⟨fun he => hne (bot_unique (hlt.le.trans_eq he)),
      starImage_isElementaryAbelian H _ hg.Vgamma_H⟩
  have hcU : Nat.card (Source.starImage H (c.Ugamma V₃)) = 2 := by
    simpa only [hrank, pow_one] using hU.card_eq_two_pow_rank
  have hcV : Nat.card (Source.starImage H c.Vgamma) ≤ 4 := by
    rw [hV.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hsmall
  have hn := endpoint_star_normality d c hH
  exact A6Endgame.no_small_relative_normal_pair _ _ _ model hVP hn.1 hn.2 hcU hlt hcV

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal
