module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalWholeComparison

/-!
# Excluding the natural whole section in the original cover branch

The actual intersection LT ∩ H maps onto the maximal syntheme parabolic.
The K₂-orbit of V₃ has order 32, so K₂ does not lie in this intersection;
together they generate H. If U₂ = U_L, both generators normalize U_L,
which would be a nontrivial normal two-subgroup of LT ∨ H, contradicting
the original F.9 hypothesis. Dimension four for U_L/V forces precisely
that equality, since V has order 16 and U₂ has order 256.

Thus the natural alternative in OriginalWholeComparison is impossible.
The actual U_L/V admits a surjection onto the five-dimensional augmentation
cover, with its constant line retained, and has dimension 5, 9, 10 or 14.
The sharper displacement argument must still eliminate the three larger
dimensions. The subsequent 13.4.1 application, strict denominators and
13.8.34 remain with the original endgame assembly.

Source: Aschbacher--Smith, proof of 13.8.33, printed p.967. The F.9
normal-two-subgroup exclusion replaces the equivalent maximal-local
normalizer contradiction in the source.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic FiveSeed
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

variable [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The actual cover parabolic and K₂ generate H. -/
theorem full_denominators_cover_generates_H
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
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁) :
    H = Source.K2 H V₂ ⊔ ((L ⊔ (T : Subgroup G)) ⊓ H) := by
  obtain ⟨_,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨_,hB,_,_,_,_,_⟩ := original_cover_orbit d h c hDH hDg hHz K hK hprod
    eL a e F hF hp earlier1354 earlier1376
  have hpar := original_cover_star_parabolic d h c hDH hDg hH a e F hF hp
  let P := (L ⊔ (T : Subgroup G)) ⊓ H
  let φ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcoreT : H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow H (T.subtype h.T_le_H)).trans_eq
      (map_subgroupOf_eq_of_le h.T_le_H)
  have hkP : φ.ker ≤ P.subgroupOf H := by
    intro x hx
    have hz : QuotientGroup.mk' (pCore 2 H) x = 1 := e.injective (hx.trans (map_one e).symm)
    have hxt : (x : G) ∈ (T : Subgroup G) :=
      hcoreT ⟨x,(QuotientGroup.eq_one_iff x).mp hz,rfl⟩
    exact ⟨mem_sup_right hxt,x.property⟩
  have himage : (P.subgroupOf H).map φ = Theory.SpecificGroups.SymmetricSix.synthemeStabilizer := by
    rw [← map_map]
    have hP : P = sourceOne L T V₁ ⊔ (T : Subgroup G) := (original_point_parabolic_eq d hH).symm
    rw [hP]
    exact hpar
  have hco : IsCoatom (P.subgroupOf H) := by
    rw [← comap_map_eq_self hkP, himage]
    exact isCoatom_comap_of_surjective hφ Theory.SpecificGroups.SymmetricSix.synthemeStabilizer_isCoatom
  have hPN : P ≤ normalizer (V₃ : Set G) := by
    change (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).LT ⊓
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).H ≤ _
    rw [h.LT_inf_H_eq]
    exact h.local_normalizes
  have hnot : ¬ Source.K2 H V₂ ≤ P := by
    intro hk
    have hb : conjugateSpanBy V₃ (Source.K2 H V₂) ≤ V₃ :=
      conjugateSpanBy_le le_rfl (hk.trans hPN)
    have hc := card_le_of_le hb
    rw [hB,d.seed_card] at hc
    omega
  have ht : (Source.K2 H V₂).subgroupOf H ⊔ P.subgroupOf H = ⊤ := by
    apply hco.lt_iff.mp
    apply lt_of_le_of_ne le_sup_right
    intro he
    apply hnot
    intro x hx
    have hh : (⟨x,Source.K2_le H V₂ hx⟩ : H) ∈
        (Source.K2 H V₂).subgroupOf H ⊔ P.subgroupOf H := mem_sup_left hx
    rw [← he] at hh
    exact hh
  have hm := congrArg (fun S : Subgroup H => S.map H.subtype) ht
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (Source.K2_le H V₂),
    map_subgroupOf_eq_of_le (show P ≤ H from inf_le_right),
    ← MonoidHom.range_eq_map,range_subtype] at hm
  exact hm.symm

/-- Equality U_L = U₂ would give a nontrivial normal two-subgroup in the
original generated pair, contradicting its F.9 two-core hypothesis. -/
theorem full_denominators_U2_ne_UL
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
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁) :
    Source.U2 H V V₂ ≠ Source.UL L H V₃ := by
  intro heq
  have hHgen := full_denominators_cover_generates_H d h c hDH hDg hH hcentral hHz K hK hprod
    eL a e model earlier1354 earlier1376 chief
  have hUP := Section07.span_UH_L_le_core (localNaturalSetup d) h
    (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  have htwo : IsPGroup 2 (Source.UL L H V₃) := (isPGroup_pCoreIn 2 _).to_le hUP
  have hLT : L ⊔ (T : Subgroup G) ≤ normalizer (Source.UL L H V₃ : Set G) :=
    SectionStructure.LT_normalizes_UL L H T V₃ h.T_le_H d.normalizes_L
  have hK₂ : Source.K2 H V₂ ≤ normalizer (Source.UL L H V₃ : Set G) := by
    rw [← heq]
    exact le_normalizer_conjugateSpanBy _ _
  have hHN : H ≤ normalizer (Source.UL L H V₃ : Set G) := by
    conv_lhs => rw [hHgen]
    exact sup_le hK₂ (inf_le_left.trans hLT)
  have hc := le_pCoreIn_of_normalizes htwo
    ((hUP.trans (pCoreIn_le 2 _)).trans (show L ⊔ (T : Subgroup G) ≤
      (L ⊔ (T : Subgroup G)) ⊔ H from le_sup_left)) (sup_le hLT hHN)
  have hz : ((L ⊔ (T : Subgroup G)) ⊔ H).pCoreIn 2 = ⊥ := by
    change (pCore 2 ((L ⊔ (T : Subgroup G)) ⊔ H : Subgroup G)).map _ = ⊥
    have hz0 : pCore 2 ((L ⊔ (T : Subgroup G)) ⊔ H : Subgroup G) = ⊥ := h.generated_core
    rw [hz0,Subgroup.map_bot]
  rw [hz] at hc
  have hu : Source.U2 H V V₂ = ⊥ := heq.trans (le_bot_iff.mp hc)
  have hv := (Source.seed_le_U2 H V V₂).trans_eq hu
  have hline : V₁ = ⊥ := le_bot_iff.mp
    ((d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)).trans hv)
  have hh := d.line_card
  rw [hline,card_bot] at hh
  contradiction

/-- The whole section cannot have natural-module dimension. -/
theorem full_denominators_whole_finrank_ne_four
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
    [(V.subgroupOf (Source.UL L H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.ULsection L H V₃ V)] :
    Module.finrank (ZMod 2) (Additive (Source.ULsection L H V₃ V)) ≠ 4 := by
  intro hdim
  obtain ⟨_,hlt,_,_,_⟩ := full_denominators_whole_permutation d h c hDH hDg hH
    hcentral hHz K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨_,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨_,_,_,hcard,_,_,hle⟩ := original_cover_orbit d h c hDH hDg hHz K hK hprod
    eL a e F hF hp earlier1354 earlier1376
  have hV : Nat.card V = 16 := by
    rw [Nat.card_congr d.coordinate.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_even _ (by decide)]
    rfl
  have hq : Nat.card (Source.ULsection L H V₃ V) = 16 := by
    change Nat.card (Additive (Source.ULsection L H V₃ V)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
    rfl
  have hUL := relIndex_mul_card_of_le hlt.le
  change Nat.card (Source.ULsection L H V₃ V) * Nat.card V = Nat.card (Source.UL L H V₃) at hUL
  rw [hq,hV] at hUL
  apply full_denominators_U2_ne_UL d h c hDH hDg hH hcentral hHz K hK hprod
    eL a e model earlier1354 earlier1376 chief
  exact eq_of_le_of_card_ge hle (by rw [← hUL,hcard])

/-- The original whole section has an equivariant quotient onto the actual
augmentation cover. The natural whole-module alternative is impossible. -/
theorem full_denominators_whole_cover_quotient
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
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁) :
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
                 ∃ q : Representation.IntertwiningMap σ (BinaryPermutation.alternatingCoreRepresentation (Fin 6)),
                   Function.Surjective q) ∧
                (Module.finrank (ZMod 2) (Additive (Source.ULsection L H V₃ V)) = 5 ∨
                  Module.finrank (ZMod 2) (Additive (Source.ULsection L H V₃ V)) = 9 ∨
                  Module.finrank (ZMod 2) (Additive (Source.ULsection L H V₃ V)) = 10 ∨
                  Module.finrank (ZMod 2) (Additive (Source.ULsection L H V₃ V)) = 14) := by
  obtain ⟨hab,hgen,hUL,hN,hE,hA,eB,hL,ρ,hρ,hg,hcomp,hdim⟩ :=
    full_denominators_whole_comparison d h c hDH hDg hH hcentral hHz K hK hprod
      eL a e model earlier1354 earlier1376 chief
  let _ := hN
  let _ := hE
  let _ := hA
  have hfour := full_denominators_whole_finrank_ne_four d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  refine ⟨hab,hgen,hUL,hN,hE,hA,eB,hL,ρ,hρ,hg,?_,hdim.resolve_left hfour⟩
  rcases hcomp with hnat | hcover
  · obtain ⟨F⟩ := hnat
    exact (hfour (F.toLinearEquiv.finrank_eq.symm.trans
      (by simpa using BinaryPermutation.finrank_natural_even (Fin 6) (by decide)))).elim
  · exact hcover

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
