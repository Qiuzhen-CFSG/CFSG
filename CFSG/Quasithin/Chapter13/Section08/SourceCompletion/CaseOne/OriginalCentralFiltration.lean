module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalRightFiltration

/-!
# Excluding both full denominators in the original ordinary A₆ branch

The same cubic filtration closes the central-seed case directly. Centrality
of U₁ in Q = O₂(LT), together with U₀ = U_L, gives C_Q(U_L) = Q. Its
quotient contribution is zero, so the L-side bound improves to n ≤ 3+k
with k ≤ j. The H-side value on the identical actor and literal sections
is still 5+j. This contradicts full denominators also in the central case.

Thus the original noncentral and central cases are both excluded. The
argument replaces the source's central-case invocation of 13.4.1 by a
stronger filtration bound under these same ambient hypotheses; it does
not assert or require the universal 13.4.1 theorem. The constant covering
line and the full central-duality denominator are retained. No normality
of U_L in H_C is asserted.

The original earlier 13.5.4, 13.7.6 and ordinary 13.8.27 setup remain
explicit. Denominator symmetry and the terminal application are connected
in OriginalStrictDenominators. Source: Aschbacher--Smith, 13.8.33,
printed pp.967--968.
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

theorem full_denominators_central_left_filtration
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
    (hseed : Source.U1 H K V₃ ≤
      centralizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G))
    (hpar : ((((L ⊔ (T : Subgroup G)) ⊓ H).subgroupOf (L ⊔ (T : Subgroup G))).map
      (Section07.NaturalAction.permutation (localNaturalSetup d))) =
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1)
    (A : Subgroup G) (hAP : A ≤ (L ⊔ (T : Subgroup G)) ⊓ H) (hA : IsPGroup 3 A)
    (f : A →* cubicActor) (hf : Function.Surjective f)
    (hmark : ∀ b : A, Section07.NaturalAction.permutation (localNaturalSetup d)
      (inclusion (hAP.trans inf_le_left) b) = (cubicActorEquiv (f b) : Equiv.Perm (Fin 6))) :
    A6Endgame.ActionAnalysis33.filtrationN A (sourceOne L T V₁) (T : Subgroup G) ≤
      3 + A6Endgame.ActionAnalysis33.filtrationK A ((L ⊔ (T : Subgroup G)).pCoreIn 2) L H V₃ ∧
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
  have hnorm : L ≤ normalizer (Q : Set G) := le_sup_left.trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))
  have hUC : Source.UL L H V₃ ≤ centralizer (Q : Set G) := by
    rw [← full_denominators_U0_eq_UL d h c hDH hDg hH hcentral hHz
      K hK hprod eL a e model earlier1354 earlier1376 chief]
    exact conjugateSpanBy_le hseed (centralizer_normalized Q L hnorm)
  have hCQ : A6Endgame.ActionAnalysis33.CQUL Q L H V₃ = Q :=
    inf_eq_left.mpr (le_centralizer_iff.mp hUC)
  have hc : sectionCubicLength A (A6Endgame.ActionAnalysis33.CQUL Q L H V₃) Q = 0 := by
    rw [hCQ, sectionCubicLength, Nat.sub_self]
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
      3 + A6Endgame.ActionAnalysis33.filtrationK A Q L H V₃
    rw [hv,hu,hl'] at hleft
    omega
  · exact A6Endgame.ActionAnalysis33.filtrationK_le_filtrationJ A Q L H V₃ hULQ hQH

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup Representation
open scoped IsMulCommutative commutatorElement Pointwise
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
open A6Endgame.ActionAnalysis33.ChiefModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Both full denominators are impossible under the original hypotheses.
The central branch has the stronger left bound 3+j on the same actor. -/
theorem full_denominators_false
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
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥) :
    False := by
  have hseed := full_denominators_seed_central d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief hcomm
  obtain ⟨eb⟩ := exists_full_denominators_bar_equiv d h c hDH hDg
  obtain ⟨d',hpar,hplane⟩ := exists_original_parabolic_coordinates d hH eb
    (BarQuotients.sourceResidual L (T : Subgroup G) V₂) rfl
  obtain ⟨A,hAP,hA,f,hf,hm⟩ := exists_original_cubic_actor d' hpar
  obtain ⟨hbound,hkj⟩ := full_denominators_central_left_filtration d' h c hDH hDg hH
    hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief hseed hpar A hAP hA f hf hm
  have hcard := original_cubic_card d' h eL A (hAP.trans inf_le_left) hA f hf hm
  obtain ⟨_,F,hF,hp⟩ := full_denominators_abelian_cover d' h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  have hstar := original_cover_star_parabolic d' h c hDH hDg hH a e F hF hp
  rw [original_point_parabolic_eq d' hH] at hstar
  have hmove : ⁅V₃, Source.QH H⁆ ≠ ⊥ := by
    change ⁅V₃,H.pCoreIn 2⁆ ≠ ⊥
    rwa [hH]
  have hright := original_right_filtration d' h hH a e model hmove hstar A hAP hcard
  omega
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
