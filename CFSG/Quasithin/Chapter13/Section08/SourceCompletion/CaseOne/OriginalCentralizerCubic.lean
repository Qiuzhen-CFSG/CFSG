module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCentralizerPermutation
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.CentralizerCubicModels

/-!
# The original centralizer quotient contributes at most one cubic constituent

The literal Q/C_Q(U_L) embeds in the fifteen-pair permutation module and
has dimension at most five. The marked cubic bound therefore gives
section cubic length at most one. The quotient map, its exact centralizer
kernel and the original conjugation formula construct the section map;
no model tag or numerical chief-factor premise is used.

The final theorem constructs simultaneous point and line parabolic
coordinates and lifts the common cubic into the original local group.
It supplies the bound for that actual actor while retaining both markings.
This discharges the centralizer-quotient contribution in the noncentral
branch of the source comparison. The other filtration contributions,
central-seed 13.4.1 application and strict denominators remain to be assembled.

Source: Aschbacher--Smith, 13.8.33, printed p.968. Earlier 13.5.4 and
13.7.6 inputs remain explicit for their existing source producers.
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

theorem full_denominators_noncentral_centralizer_length_le_one
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
    (A : Subgroup G) (hAP : A ≤ L ⊔ (T : Subgroup G)) (hA : IsPGroup 3 A)
    (f : A →* cubicActor) (hf : Function.Surjective f)
    (hmark : ∀ b : A, Section07.NaturalAction.permutation (localNaturalSetup d)
      (inclusion hAP b) = (cubicActorEquiv (f b) : Equiv.Perm (Fin 6))) :
    sectionCubicLength A
      (A6Endgame.ActionAnalysis33.CQUL ((L ⊔ (T : Subgroup G)).pCoreIn 2) L H V₃)
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 1 := by
  obtain ⟨hN,hE,hn,ρ,hρ,_,hd,j,hj⟩ := full_denominators_noncentral_pair_embedding
    d h c hDH hDg hH hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief hnc
  let _ := hN
  let _ := hE
  let P := L ⊔ (T : Subgroup G)
  let Q := P.pCoreIn 2
  let C := A6Endgame.ActionAnalysis33.CQUL Q L H V₃
  let π := Section07.NaturalAction.permutation (localNaturalSetup d)
  let τ := ρ.comp (Marked.outer.toMonoidHom.comp cubicActor.subtype)
  let _ := action τ
  let φ : Q →* Multiplicative (Additive (Q ⧸ C.subgroupOf Q)) :=
    MulEquiv.toMultiplicative_toAdditive.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  let s : Subgroup.ConjugationSection A C Q f := {
    le := inf_le_left
    normalizes := hAP.trans hn
    projection := φ
    onto := MulEquiv.toMultiplicative_toAdditive.symm.surjective.comp (QuotientGroup.mk'_surjective _)
    kernel := by
      ext q
      change QuotientGroup.mk' (C.subgroupOf Q) q = 1 ↔ q ∈ C.subgroupOf Q
      exact QuotientGroup.eq_one_iff q
    equivariant := by
      intro b q
      change Additive.ofMul (QuotientGroup.mk' (C.subgroupOf Q)
        ⟨(b : G) * (q : G) * (b : G)⁻¹,_⟩) =
          ρ (Marked.outer (f b).val) (Additive.ofMul (QuotientGroup.mk' _ q))
      have hm : π (inclusion hAP b) = Marked.outer (f b).val := hmark b
      rw [← hm]
      exact (hρ (inclusion hAP b) q).symm }
  have he := s.length_eq hA (isPGroup_pCoreIn 2 P) hf
  change sectionCubicLength A C Q = Nat.log 4 (fixedIndex τ) at he
  rw [he]
  have hb := Nat.log_mono_right (b := 4) (small_pair_cubic_fixedIndex_le ρ j hj hd)
  exact hb

theorem full_denominators_noncentral_cubic_comparison
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
          sectionCubicLength A
            (A6Endgame.ActionAnalysis33.CQUL ((L ⊔ (T : Subgroup G)).pCoreIn 2) L H V₃)
            ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ 1 := by
  obtain ⟨eb⟩ := exists_full_denominators_bar_equiv d h c hDH hDg
  obtain ⟨d',hpar,hplane⟩ := exists_original_parabolic_coordinates d hH eb
    (BarQuotients.sourceResidual L (T : Subgroup G) V₂) rfl
  obtain ⟨A,hAP,hA,f,hf,hmark⟩ := exists_original_cubic_actor d' hpar
  exact ⟨d',hpar,hplane,A,hAP,hA,f,hf,hmark,
    full_denominators_noncentral_centralizer_length_le_one d' h c hDH hDg hH
      hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief hnc
      A (hAP.trans inf_le_left) hA f hf hmark⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
