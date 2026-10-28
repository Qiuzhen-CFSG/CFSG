module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalWholeCover
public import CFSG.Quasithin.ChapterG.Section05.Structure.PairSmallMovement

/-!
# The whole original cover under the endpoint image bound

The actual fifteen-pair surjection and full L-movement are already constructed.
An involution from Uγ moves at most two dimensions when the literal image of
U_L modulo Qγ has order at most four. Applying the sharp G.5.3 comparison to
that same action excludes dimensions 9, 10 and 14. The original F.9 argument
already excludes dimension four, leaving an equivariant isomorphism with the
five-dimensional augmentation cover, including its constant line.

The actor remains LT/C_LT(V), and the image of the original L is exactly A₆.
Consequently |U_L| = 512 and |U_L:U₂| = 2. The endpoint index bound is kept
explicit here and discharged from the original setup in OriginalEndpointCore.
The 13.4.1 application, chief-factor contradiction and strict-denominator
assembly remain unfinished. No assertion of full 13.8.33 or 13.8.34 is made here.

Source: Aschbacher--Smith, proof of 13.8.33, printed pp.967--968.
-/

public section
open Subgroup Representation CFSG.Quasithin.ChapterG.Section05.Structure
open Representation.BinaryOffender.NaturalTensor
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}


variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The literal whole section is the augmentation cover when the original
endpoint-core image has order at most four. The endpoint bound remains explicit. -/
theorem full_denominators_whole_cover_of_endpoint_index
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
    (hi : c.Qgamma.relIndex (Source.UL L H V₃) ≤ 4) :
    IsMulCommutative (Source.UL L H V₃) ∧
    Source.UL L H V₃ = ⁅Source.UL L H V₃,L⁆ ∧
    ∃ hUL : L ⊔ (T : Subgroup G) ≤ normalizer (Source.UL L H V₃ : Set G),
      ∃ hN : (V.subgroupOf (Source.UL L H V₃)).Normal,
        let _ := hN
        ∃ hE : IsElementaryAbelian 2 (Source.ULsection L H V₃ V),
          let _ := hE
          ∃ hA : (actorKernel (L ⊔ (T : Subgroup G)) V).Normal,
            let _ := hA
            ∃ eB : ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸
                actorKernel (L ⊔ (T : Subgroup G)) V) ≃* Equiv.Perm (Fin 6),
              (eB.toMonoidHom.comp ((QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V)).comp
                (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)))).range =
                  alternatingGroup (Fin 6) ∧
              ∃ ρ : Representation (ZMod 2)
                  ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ actorKernel (L ⊔ (T : Subgroup G)) V)
                  (Additive (Source.ULsection L H V₃ V)),
                SectionConjugationAlong (L ⊔ (T : Subgroup G)) (Source.UL L H V₃) V
                  (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V)) hUL ρ ∧
                Coinvariants.ker ρ = ⊤ ∧
                (let σ := ρ.comp (eB.symm.toMonoidHom.comp (alternatingGroup (Fin 6)).subtype)
                 Nonempty (Representation.Equiv (BinaryPermutation.alternatingCoreRepresentation (Fin 6)) σ)) ∧
                Module.finrank (ZMod 2) (Additive (Source.ULsection L H V₃ V)) = 5 := by
  obtain ⟨hab,hlt,p,hbij,hwhole⟩ := full_denominators_whole_permutation d h c hDH hDg hH
    hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  let _ := p.actor_normal
  obtain ⟨hUL,hN,hE,ρ,hρ,f,hf⟩ := hwhole
  let _ := hN
  let _ := hE
  let eB := MulEquiv.ofBijective p.permutation hbij
  have hgen := full_denominators_span_generated d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  have hUP : Source.UL L H V₃ ≤ L ⊔ (T : Subgroup G) :=
    (Section07.span_UH_L_le_core (localNaturalSetup d) h
      (show IsMulCommutative (Source.UH H V₃) from inferInstance)).trans (pCoreIn_le 2 _)
  have hg := section_fully_moved (Source.UL L H V₃) V (L ⊔ (T : Subgroup G)) L
    hUP hlt.le le_sup_left (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V))
    hUL ρ hρ hgen
  let : Nontrivial (Additive (Source.ULsection L H V₃ V)) := by
    obtain ⟨u,hu,hnu⟩ := SetLike.exists_of_lt hlt
    refine ⟨⟨Additive.ofMul (QuotientGroup.mk' (V.subgroupOf (Source.UL L H V₃)) ⟨u,hu⟩),0,?_⟩⟩
    intro he
    exact hnu ((QuotientGroup.eq_one_iff (⟨u,hu⟩ : Source.UL L H V₃)).mp he)
  let _ := barKernel_normal (L ⊔ (T : Subgroup G)) V d.normalizes_V
  let eb := (barEquivImage (L ⊔ (T : Subgroup G)) V d.normalizes_V).symm.trans eB
  obtain ⟨u,hu,ho⟩ := full_denominators_bar_mover d h c hDH hDg eb
  have he : eb ((barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).rangeRestrict u) =
      eB (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V) u) := by
    have hb : barEquivImage (L ⊔ (T : Subgroup G)) V d.normalizes_V
        (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V) u) =
        (barMap (L ⊔ (T : Subgroup G)) V d.normalizes_V).rangeRestrict u := by
      apply Subtype.ext
      rfl
    rw [← hb]
    exact congrArg eB ((barEquivImage (L ⊔ (T : Subgroup G)) V d.normalizes_V).symm_apply_apply _)
  rw [he] at ho
  have hsmall := full_denominators_small_displacement_along d h c hDH hDg hcentral hab hlt.le
    (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V)) hUL ρ hρ hi u hu
  obtain ⟨hc,hd⟩ := marked_pair_small_involution ρ eB f hf hg
    (QuotientGroup.mk' (actorKernel (L ⊔ (T : Subgroup G)) V) u) ho hsmall
  have hfour := full_denominators_whole_finrank_ne_four d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  refine ⟨hab,hgen,hUL,hN,hE,p.actor_normal,eB,original_whole_actor_component d eB,ρ,hρ,hg,?_,
    hd.resolve_left hfour⟩
  rcases hc with hn | hcover
  · obtain ⟨F⟩ := hn
    exact (hfour (F.toLinearEquiv.finrank_eq.symm.trans
      (by simpa using BinaryPermutation.finrank_natural_even (Fin 6) (by decide)))).elim
  · exact hcover

/-- The recognized whole cover gives the exact source orders and the
index-two inclusion of the original U₂. No order is added as a premise. -/
theorem full_denominators_whole_size_of_endpoint_index
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
    (hi : c.Qgamma.relIndex (Source.UL L H V₃) ≤ 4) :
    Nat.card (Source.UL L H V₃) = 512 ∧
      (Source.U2 H V V₂).relIndex (Source.UL L H V₃) = 2 := by
  obtain ⟨_,_,_,hN,hE,_,_,_,_,_,_,_,hdim⟩ :=
    full_denominators_whole_cover_of_endpoint_index d h c hDH hDg hH hcentral hHz
      K hK hprod eL a e model earlier1354 earlier1376 chief hi
  let _ := hN
  let _ := hE
  have hV : Nat.card V = 16 := by
    rw [Nat.card_congr d.coordinate.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_even _ (by decide)]
    rfl
  have hq : Nat.card (Source.ULsection L H V₃ V) = 32 := by
    change Nat.card (Additive (Source.ULsection L H V₃ V)) = 32
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
    rfl
  obtain ⟨_,hlt,_,_,_⟩ := full_denominators_whole_permutation d h c hDH hDg hH
    hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  have hm := relIndex_mul_card_of_le hlt.le
  change Nat.card (Source.ULsection L H V₃ V) * Nat.card V = Nat.card (Source.UL L H V₃) at hm
  rw [hq,hV] at hm
  have hUL : Nat.card (Source.UL L H V₃) = 512 := hm.symm
  obtain ⟨_,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨_,_,_,hcard,_,_,hle⟩ := original_cover_orbit d h c hDH hDg hHz K hK hprod
    eL a e F hF hp earlier1354 earlier1376
  have hindex := relIndex_mul_card_of_le hle
  rw [hcard,hUL] at hindex
  exact ⟨hUL,by omega⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
