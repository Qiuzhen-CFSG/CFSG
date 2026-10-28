module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalWholeCubic
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations

/-!
# The original L-side chief-filtration budget

For the same cubic actor, V and U_L/V each contribute one, the literal
Q/C_Q(U_L) contributes at most one, and the original point-parabolic
core quotient contributes one. The actual chain therefore has length
at most 4+k. Containment of its unknown interval in H_C/U_H gives k ≤ j,
without asserting normality of U_L in H_C.

The final application constructs the actor and preserves both parabolic
markings from the original full-denominator hypotheses. It gives the whole
L-side bound n ≤ 4+j. The matching H-side value 5+j, central-seed 13.4.1
application and strict-denominator/13.8.34 assembly remain obligations;
no numerical chief-factor premise is assumed here.
Source: Aschbacher--Smith, 13.8.33, printed p.968.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
open A6Endgame.ActionAnalysis33.ChiefModels
open Representation.BinaryFixedPoints
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

theorem full_denominators_noncentral_left_filtration
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁)
    (hnc : ¬ Source.U1 H K V₃ ≤
      centralizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G))
    (hpar : ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf (L ⊔ (T : Subgroup G))).map
      (Section07.NaturalAction.permutation (localNaturalSetup d))) =
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1)
    (A : Subgroup G) (hAP : A ≤ (L ⊔ (T : Subgroup G)) ⊓ H) (hA : IsPGroup 3 A)
    (f : A →* cubicActor) (hf : Function.Surjective f)
    (hmark : ∀ b : A, Section07.NaturalAction.permutation (localNaturalSetup d)
      (inclusion (hAP.trans inf_le_left) b) = (cubicActorEquiv (f b) : Equiv.Perm (Fin 6))) :
    A6Endgame.ActionAnalysis33.filtrationN A (sourceOne L T V₁) (T : Subgroup G) ≤
      4 + A6Endgame.ActionAnalysis33.filtrationK A ((L ⊔ (T : Subgroup G)).pCoreIn 2) L H V₃ ∧
    A6Endgame.ActionAnalysis33.filtrationK A ((L ⊔ (T : Subgroup G)).pCoreIn 2) L H V₃ ≤
      A6Endgame.ActionAnalysis33.filtrationJ A H V₃ := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQ := isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))
  obtain ⟨hab,hlt,_,_,_⟩ := full_denominators_whole_permutation
    d h c hDH hDg hH hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  let _ := hab
  have hULQ : Source.UL L H V₃ ≤ Q := Section07.span_UH_L_le_core (localNaturalSetup d) h
    (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  let lq := original_parabolic_quotient d h eL hpar A hAP f hmark
  let _ := conjMulDistribMulActionOfLeNormalizer duadCubicActor
    (Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1.pCoreIn 2)
    duadCubicActor_normalizes_parabolic_core
  let lc := lq.coreSection hQ duadCubicActor_normalizes_parabolic_core
  have htop : A6Endgame.ActionAnalysis33.filtrationTop (sourceOne L T V₁) (T : Subgroup G) =
      ((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2 := by
    unfold A6Endgame.ActionAnalysis33.filtrationTop
    rw [original_point_parabolic_eq d hH]
  have hQR : Q ≤ A6Endgame.ActionAnalysis33.filtrationTop (sourceOne L T V₁) (T : Subgroup G) := by
    rw [htop]
    exact lc.le
  have hv := opposite_section_length .natural
    (original_natural_section d A (hAP.trans inf_le_left) f hmark) hA
    (hQ.to_le (hlt.le.trans hULQ)) hf
  have hu := full_denominators_span_cubic_length d h c hDH hDg hH hcentral hHz K hK hprod
    eL a e model earlier1354 earlier1376 chief A (hAP.trans inf_le_left) hA f hf hmark
  have hc := full_denominators_noncentral_centralizer_length_le_one d h c hDH hDg hH
    hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief hnc
    A (hAP.trans inf_le_left) hA f hf hmark
  have hl := duad_core_section_length lc hA (isPGroup_pCoreIn 2 _) hf
  have hleft := A6Endgame.ActionAnalysis33.leftFiltration_total A Q L H V₃ V
    (sourceOne L T V₁) (T : Subgroup G) hlt.le hULQ hQR
  simp only [sectionCubicLength,conjugationCubicLength_bot,Nat.sub_zero] at hv
  have hl' : sectionCubicLength A Q
      (A6Endgame.ActionAnalysis33.filtrationTop (sourceOne L T V₁) (T : Subgroup G)) = 1 := by
    rw [htop]
    exact hl
  have hQH : Q ≤ H := lq.kernel_le.trans inf_le_right
  constructor
  · change A6Endgame.ActionAnalysis33.filtrationN A (sourceOne L T V₁) (T : Subgroup G) ≤
      4 + A6Endgame.ActionAnalysis33.filtrationK A Q L H V₃
    rw [hv,hu,hl'] at hleft
    change sectionCubicLength A (A6Endgame.ActionAnalysis33.CQUL Q L H V₃) Q ≤ 1 at hc
    omega
  · exact A6Endgame.ActionAnalysis33.filtrationK_le_filtrationJ A Q L H V₃ hULQ hQH

/-- The original hypotheses construct the common cubic actor, both original
parabolic markings, and the complete L-side upper bound. -/
theorem full_denominators_noncentral_filtration_budget
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁)
    (hnc : ¬ Source.U1 H K V₃ ≤
      centralizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) :
    ∃ d' : LocalSetup T L V V₁ V₂ V₃ M G₁,
      ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf (L ⊔ (T : Subgroup G))).map
        (Section07.NaturalAction.permutation (localNaturalSetup d'))) =
          Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1 ∧
      (((BarQuotients.sourceResidual L (T : Subgroup G) V₂ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map
        (Section07.NaturalAction.permutation (localNaturalSetup d'))) =
          Theory.SpecificGroups.SymmetricSix.BinaryFlags.H2 ∧
      ∃ (A : Subgroup G) (hAP : A ≤ (L ⊔ (T : Subgroup G)) ⊓ H), IsPGroup 3 A ∧
        ∃ f : A →* cubicActor, Function.Surjective f ∧
          (∀ b : A, Section07.NaturalAction.permutation (localNaturalSetup d')
            (inclusion (hAP.trans inf_le_left) b) = (cubicActorEquiv (f b) : Equiv.Perm (Fin 6))) ∧
          A6Endgame.ActionAnalysis33.filtrationN A (sourceOne L T V₁) (T : Subgroup G) ≤
            4 + A6Endgame.ActionAnalysis33.filtrationJ A H V₃ := by
  obtain ⟨d',hpar,hplane,A,hAP,hA,f,hf,hmark,_⟩ :=
    full_denominators_noncentral_cubic_comparison d h c hDH hDg hH hcentral hHz
      K hK hprod eL a e model earlier1354 earlier1376 chief hnc
  obtain ⟨hb,hkj⟩ := full_denominators_noncentral_left_filtration
    d' h c hDH hDg hH hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief hnc
    hpar A hAP hA f hf hmark
  exact ⟨d',hpar,hplane,A,hAP,hA,f,hf,hmark,hb.trans (Nat.add_le_add_left hkj 4)⟩
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
