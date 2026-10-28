module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalLeftFiltration
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalRightActor
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalRightDuality

/-!
# The original H-side value and the noncentral-seed contradiction

On the same ambient cubic subgroup, U_H contributes two, Q_H/H_C
contributes two by the original central duality, and the point-parabolic
two-core quotient contributes one. The literal H-side filtration therefore
has value 5+j. All action and parabolic maps are constructed; no numerical
chief-factor identity is assumed.

The final application obtains the star parabolic from the original cover,
retains the actor from OriginalLeftFiltration, and contradicts its bound
n ≤ 4+j. Thus full denominators force U₁ to centralize O₂(LT). This closes
the noncentral-seed branch. OriginalCentralFiltration uses the same H-side
value to exclude the central-seed branch directly, and the strict-denominator
and terminal modules apply both exclusions. The earlier ordinary setup,
13.5.4 and 13.7.6 inputs retain their producers.
Source: Aschbacher--Smith, 13.8.33, printed pp.967--968.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup Representation
open scoped IsMulCommutative
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open A6Endgame.ActionAnalysis33 A6Endgame.ActionAnalysis33.ChiefModels
open A6Endgame.PointNormalizer Representation.BinaryFixedPoints
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open ComponentSieve.SixAndG2.NaturalSix
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

private noncomputable def star_section
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (hz : V₁ ≤ Source.UH H V₃)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) W)
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] W)
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) = ρ (e g) (F v))
    (A : Subgroup G) (hAH : A ≤ H) (f : A →* cubicActor)
    (hm : ∀ b : A, e (QuotientGroup.mk' (pCore 2 H) (inclusion hAH b)) = (f b : Equiv.Perm (Fin 6))) :
    letI := action (ρ.comp cubicActor.subtype)
    ConjugationSection (Y := Multiplicative W) A V₁ (Source.UH H V₃) f := by
  letI := action (ρ.comp cubicActor.subtype)
  let E := F.toAddEquiv.toMultiplicative
  let q := MulEquiv.toMultiplicative_toAdditive.symm.toMonoidHom.comp
    (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))
  refine ⟨hz,hAH.trans a.normalizes,E.toMonoidHom.comp q,
    E.surjective.comp (MulEquiv.toMultiplicative_toAdditive.symm.surjective.comp
      (QuotientGroup.mk'_surjective _)),?_,?_⟩
  · ext u
    change E (q u) = 1 ↔ u ∈ V₁.subgroupOf (Source.UH H V₃)
    rw [← map_one E,E.injective.eq_iff]
    exact QuotientGroup.eq_one_iff u
  · intro b u
    change F (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
      ⟨(b : G) * (u : G) * (b : G)⁻¹,_⟩)) =
      ρ (f b).val (F (Additive.ofMul (QuotientGroup.mk' _ u)))
    have he := hF (QuotientGroup.mk' (pCore 2 H) (inclusion hAH b))
      (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))
    rw [hm] at he
    exact (congrArg (fun x => F (Additive.ofMul x)) (a.conjugation (inclusion hAH b) u)).symm.trans he

/-- The whole H-side seed span contributes two, including its central line. -/
theorem original_star_span_length
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (coords : LinearCoordinates a e.toMonoidHom)
    (A : Subgroup G) (hAH : A ≤ H) (hA : IsPGroup 3 A)
    (f : A →* cubicActor) (hf : Function.Surjective f)
    (hm : ∀ b : A, e (QuotientGroup.mk' (pCore 2 H) (inclusion hAH b)) = (f b : Equiv.Perm (Fin 6))) :
    conjugationCubicLength A (Source.UH H V₃) = 2 := by
  have hs : sectionCubicLength A V₁ (Source.UH H V₃) = 2 := by
    rcases coords with ⟨F,hF⟩ | ⟨F,hF⟩
    · exact standard_section_length .natural
        (star_section a (d.line_le_uh H) e _ F hF A hAH f hm)
        hA ((isPGroup_pCoreIn 2 H).to_le h.UH_le_QH) hf
    · exact standard_section_length .augmentation
        (star_section a (d.line_le_uh H) e _ F hF A hAH f hm)
        hA ((isPGroup_pCoreIn 2 H).to_le h.UH_le_QH) hf
  have hz : conjugationCubicLength A V₁ = 0 := by
    rw [conjugationCubicLength,show (centralizer (A : Set G)).relIndex V₁ = 1 from
      relIndex_eq_one.mpr (le_centralizer_iff.mp (hAH.trans h.H_centralizes))]
    rfl
  simpa only [sectionCubicLength,hz,Nat.sub_zero] using hs

private noncomputable def star_parabolic_quotient
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (hpar : (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom = H2)
    (A : Subgroup G) (hAP : A ≤ (L ⊔ (T : Subgroup G)) ⊓ H)
    (f : A →* cubicActor)
    (hm : ∀ b : A, e (QuotientGroup.mk' (pCore 2 H) (inclusion (hAP.trans inf_le_right) b)) = (f b : Equiv.Perm (Fin 6))) :
    LocalCoreQuotient A (Source.QH H) ((L ⊔ (T : Subgroup G)) ⊓ H) cubicActor H2 f := by
  let P := (L ⊔ (T : Subgroup G)) ⊓ H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : (P.subgroupOf H).map q = H2 := by rw [← map_map]; exact hpar
  let φ : P →* H2 := (q.comp (inclusion inf_le_right)).codRestrict H2
    (fun x => hq ▸ mem_map_of_mem q x.property)
  refine ⟨hAP,le_inf (h.QH_le_T.trans le_sup_right) (pCoreIn_le 2 H),φ,?_,?_,hm⟩
  · rintro ⟨y,hy⟩
    obtain ⟨x,hx,hxy⟩ := show y ∈ (P.subgroupOf H).map q from hq.symm ▸ hy
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  · ext x
    change φ x = 1 ↔ (x : G) ∈ Source.QH H
    rw [← Subtype.coe_inj]
    change e (QuotientGroup.mk' (pCore 2 H) (inclusion inf_le_right x)) = 1 ↔ _
    rw [← map_one e,e.injective.eq_iff]
    exact (QuotientGroup.eq_one_iff (inclusion (show P ≤ H from inf_le_right) x)).trans
      (mem_map_iff_mem H.subtype_injective).symm

/-- The original H-side value 5+j on any order-three subgroup of the common
point parabolic. Its marked star coordinates are constructed by inner conjugacy. -/
theorem original_right_filtration
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hH : H = G₁)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hmove : ⁅V₃, Source.QH H⁆ ≠ ⊥)
    (hpar : (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom = H2)
    (A : Subgroup G) (hAP : A ≤ (L ⊔ (T : Subgroup G)) ⊓ H) (hcard : Nat.card A = 3) :
    filtrationN A (sourceOne L T V₁) (T : Subgroup G) = 5 + filtrationJ A H V₃ := by
  obtain ⟨e',coords,hpar',f,hf,hm⟩ := exists_original_star_cubic_coordinates a e
    (model.action_cases H V₃ V₁ a e) _ inf_le_right hpar A hAP hcard
  have hA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hU := original_star_span_length d h a e' coords A (hAP.trans inf_le_right) hA f hf hm
  have hdual := original_dual_section_length d h a e model hmove A (hAP.trans inf_le_right) hcard
  let localQuotient := star_parabolic_quotient h e' hpar' A hAP f hm
  let := conjMulDistribMulActionOfLeNormalizer cubicActor (H2.pCoreIn 2)
    cubicActor_normalizes_parabolic_core
  let s := localQuotient.coreSection (isPGroup_pCoreIn 2 H) cubicActor_normalizes_parabolic_core
  have htop := syntheme_core_section_length s hA (isPGroup_pCoreIn 2 _) hf
  have hCQ : Source.HC H V₃ ≤ Source.QH H := by
    obtain ⟨_,_,_,sQ,_,_⟩ := Section07.source_central_duality (localNaturalSetup d) h
      (show IsMulCommutative (Source.UH H V₃) from inferInstance)
    exact sQ.kernel_le
  have hUC : Source.UH H V₃ ≤ Source.HC H V₃ :=
    le_inf h.UH_le_H (le_centralizer (Source.UH H V₃))
  have h₁ := conjugationCubicLength_mono A hUC
  have h₂ := conjugationCubicLength_mono A hCQ
  have h₃ := conjugationCubicLength_mono A s.le
  have he : filtrationTop (sourceOne L T V₁) (T : Subgroup G) =
      (((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2) := by
    unfold filtrationTop
    rw [original_point_parabolic_eq d hH]
  unfold filtrationN filtrationJ sectionCubicLength at *
  rw [he]
  omega
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open Subgroup Representation
open scoped IsMulCommutative commutatorElement Pointwise
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The original noncentral-seed branch is impossible: the very same cubic actor
has length at most 4+j and exactly 5+j on the same original two-core. -/
theorem full_denominators_seed_central
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
    Source.U1 H K V₃ ≤ centralizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) := by
  by_contra hnc
  obtain ⟨d',hpar,_,A,hAP,hA,f,hf,hm,hbound⟩ :=
    full_denominators_noncentral_filtration_budget d h c hDH hDg hH hcentral hHz
      K hK hprod eL a e model earlier1354 earlier1376 chief hnc
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
