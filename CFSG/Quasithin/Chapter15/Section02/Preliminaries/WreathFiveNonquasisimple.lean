module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveSylowExclusion
public import Theory.GroupTheory.Fitting.NormalizedFiveResidual
public import Theory.GroupTheory.CentralizerResidualProducts
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaFiveFitting
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NonquasisimpleFitting

/-!
# The original wreath-five overcomponent has quasisimple two-core quotient

If L₁/O₂(L₁) were nonquasisimple, A.3.6 and the original C.2.6
factorization put its Fitting preimage in W∩M. That preimage normalizes Y,
so the prime-index intersection lemma and Fitting self-centralization force
Y inside it. Subnormal two-core transport gives the literal image of Y
order five. The actual Sylow-two action makes this image central.

Thus [L₁,Y] lies in O₂(W). This normalizing kernel lies in S, so residual
lifting gives L₁≤N_G(Y)≤M, contradicting its original choice. The final
H-star consumer retains the same K,W,R,L₁ and supplies quasisimplicity with
no new premise. The later C.2.7/A.3.15 comparison remains separate.
Source: Aschbacher--Smith, original15.2.4, printed p.1107.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
variable {G : Type*} [Group G] [Finite G]

private theorem fitting_map_le {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN,hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩
private theorem fitting_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : (fittingSubgroup A).map e.toMonoidHom = fittingSubgroup B := by
  apply le_antisymm (fitting_map_le e)
  have hh := map_mono (f := e.toMonoidHom) (fitting_map_le e.symm)
  have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by
    ext x
    exact e.apply_symm_apply x
  simpa only [map_map,he,map_id] using hh

private theorem residual_image_fitting {L Y M : Subgroup G} (hL : (⊤ : Subgroup L).IsCComponent)
    (hYL : Y ≤ L) (hMN : M ≤ normalizer (Y : Set G))
    (hp : IsPPerfect 2 Y) (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (hF : (twoFittingCore L).map L.subtype ≤ M)
    (hn : ¬ IsQuasisimple (L ⧸ pCore 2 L)) :
    Y.subgroupOf L ≤ twoFittingCore L ∧
    Nat.card ((Y.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L))) = 5 := by
  let Y₀ := Y.subgroupOf L
  let e : Y₀ ≃* Y := subgroupOfEquivOfLe hYL
  let Q := L ⧸ pCore 2 L
  let q := QuotientGroup.mk' (pCore 2 L)
  let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
  have htop : (⊤ : Subgroup L).IsCComponent := hL
  have hbar : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using htop.map_quotient (pCore 2 L)
  have hnc : ¬ fittingSubgroup (⊤ : Subgroup Q) ≤ center (⊤ : Subgroup Q) := by
    intro hh
    have hh' : fittingSubgroup Q ≤ center Q := by
      have ht := map_mono (f := (topEquiv : (⊤ : Subgroup Q) ≃* Q).toMonoidHom) hh
      simpa only [fitting_map_equiv, map_center_equiv] using ht
    have hC : fittingSubgroup Q ≤ centralizer ((⊤ : Subgroup Q) : Set Q) := by
      simpa only [coe_top,centralizer_univ] using hh'
    let := hbar.isQuasisimple_of_fitting_centralizes hC
    exact hn (IsQuasisimple.of_mulEquiv topEquiv)
  have hf : generalizedFitting Q = fittingSubgroup Q := by
    have he := ChapterA.Section03.NoncentralFitting.generalizedFitting_eq_fitting hbar hnc
    have hm := congrArg (map (topEquiv : (⊤ : Subgroup Q) ≃* Q).toMonoidHom) he
    simpa only [map_generalizedFitting_equiv,fitting_map_equiv] using hm
  have hFN : twoFittingCore L ≤ normalizer (Y₀ : Set L) := by
    intro x hx
    rw [←subgroupOf_normalizer_eq hYL]
    exact hMN (hF (mem_map_of_mem L.subtype hx))
  have hp₀ : IsPPerfect 2 Y₀ := hp.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hc₀ : (pCore 2 Y₀).index = 5 := by
    rw [index_eq_card]
    exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).trans hc
  have hYF := residual_le_twoFittingCore_of_normalized Y₀ hp₀ hc₀ hFN hf
  have hsub : Y₀.IsSubnormal := by
    have hnF : (Y₀.subgroupOf (twoFittingCore L)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hYF).mpr hFN
    exact Subgroup.IsSubnormal.trans hYF hnF.isSubnormal
      (inferInstance : (twoFittingCore L).Normal).isSubnormal
  have hker : (q.comp Y₀.subtype).ker = pCore 2 Y₀ := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk',pCore_subnormal_eq_comap 2 hsub]
  let eqv : (Y₀ ⧸ pCore 2 Y₀) ≃* Y₀.map q :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (q.comp Y₀.subtype)).trans
        (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp,range_subtype])))
  exact ⟨hYF,(Nat.card_congr eqv.toEquiv).symm.trans hc₀⟩
private theorem residual_central_mod_core {L Y M : Subgroup G}
    (hsq : IsSQTK KnownSimple.IsKnownSimple L) (hL : (⊤ : Subgroup L).IsCComponent)
    (hYL : Y ≤ L) (hMN : M ≤ normalizer (Y : Set G))
    (hp : IsPPerfect 2 Y) (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (hF : (twoFittingCore L).map L.subtype ≤ M)
    (hn : ¬ IsQuasisimple (L ⧸ pCore 2 L))
    (P : Sylow 2 L) (hPN : (P : Subgroup L).map L.subtype ≤ normalizer (Y : Set G)) :
    ⁅L,Y⁆ ≤ L.pCoreIn 2 := by
  let Y₀ := Y.subgroupOf L
  let Q := L ⧸ pCore 2 L
  let q := QuotientGroup.mk' (pCore 2 L)
  let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
  have htop : (⊤ : Subgroup L).IsCComponent := hL
  have hbar : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using htop.map_quotient (pCore 2 L)
  have hsqQ : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 L) pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  obtain ⟨hYF,hcard⟩ := residual_image_fitting hL hYL hMN hp hc hF hn
  let A := Y₀.map q
  let P₀ := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hAF : A ≤ fittingSubgroup Q := map_le_iff_le_comap.mpr hYF
  have hPnorm : (P : Subgroup L) ≤ normalizer (Y₀ : Set L) := by
    rw [←subgroupOf_normalizer_eq hYL]
    exact map_le_iff_le_comap.mp hPN
  have hPAnorm : (P₀ : Subgroup Q) ≤ normalizer (A : Set Q) :=
    (map_mono hPnorm).trans (Y₀.le_normalizer_map q)
  have hcentral := OmegaFive.top_cComponent_invariant_five_le_center hsqQ
    (pCore_quotient_pCore_eq_bot 2) hbar P₀ A hcard hAF hPAnorm
  have hcomm : ⁅(⊤ : Subgroup L),Y₀⁆ ≤ pCore 2 L := by
    rw [←QuotientGroup.ker_mk' (pCore 2 L),←Subgroup.map_eq_bot_iff,map_commutator,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
    exact le_bot_iff.mp ((commutator_mono le_rfl hcentral).trans (commutator_center_right ⊤).le)
  have hh := map_mono (f := L.subtype) hcomm
  simpa only [map_commutator,←MonoidHom.range_eq_map,range_subtype,
    Y₀, pCoreIn, map_subgroupOf_eq_of_le hYL] using hh

/-- C.2.6 and the genuine A.3.6 Sylow action force a nonquasisimple normal
component to normalize the original five-residual. -/
public theorem nonquasisimple_component_normalizes_five_residual
    {W L R M Y S : Subgroup G}
    (hsetup : Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W R M)
    (hL : L ∈ Chapter1.cComponentsIn W)
    (hf : generalizedFitting L = pCore 2 L)
    (hWN : W ≤ normalizer (L : Set G))
    (hSyl : Chapter1.IsSylowIn 2 S W) (hSM : S ≤ M)
    (hYL : Y ≤ L) (hMN : M ≤ normalizer (Y : Set G))
    (hp : IsPPerfect 2 Y) (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (hn : ¬ IsQuasisimple (L ⧸ pCore 2 L)) :
    L ≤ normalizer (Y : Set G) := by
  have hF := ChapterC.Section02Source.fittingCore_le_of_nonquasisimple_component_setup
    hsetup hL hf hWN hn
  let K := L.subgroupOf W
  let e : K ≃* L := subgroupOfEquivOfLe hL.1
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hL.2.subgroupOf le_rfl
  have htopL : (⊤ : Subgroup L).IsCComponent := by
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using htop.map_equiv e
  have hsqL : IsSQTK KnownSimple.IsKnownSimple L :=
    (IsSQTK.equiv e).mp (hsetup.sqtk.subgroup K)
  have hnormal : K.Normal := normal_subgroupOf_of_le_normalizer hWN
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl hL.1 hnormal.isSubnormal
  have hPN : (P : Subgroup L).map L.subtype ≤ normalizer (Y : Set G) :=
    hP ▸ (inf_le_left.trans (hSM.trans hMN))
  have hcomm := residual_central_mod_core hsqL htopL hYL hMN hp hc hF hn P hPN
  have hcore : L.pCoreIn 2 ≤ W.pCoreIn 2 := pCoreIn_mono_of_normalizes hL.1 hWN
  have hcoreS : W.pCoreIn 2 ≤ S := by
    obtain ⟨P,hP⟩ := hSyl
    exact hP ▸ pCoreIn_le_sylow W P
  have hcoreY : W.pCoreIn 2 ≤ normalizer (Y : Set G) := hcoreS.trans (hSM.trans hMN)
  have hWcore : W ≤ normalizer (W.pCoreIn 2 : Set G) :=
    W.le_normalizer.trans (normalizer_le_normalizer_characteristic_image W (pCore 2 W))
  have hres : (pResidual 2 Y).map Y.subtype = Y := by
    rw [(pResidual_eq_top_iff 2 Y).mpr hp,←MonoidHom.range_eq_map,range_subtype]
  have hcomm' : ⁅L,(pResidual 2 Y).map Y.subtype⁆ ≤ W.pCoreIn 2 := by
    rw [hres]
    exact hcomm.trans hcore
  have hh := normalizes_residual_of_commutator_le_two L (W.pCoreIn 2) Y (W.pCoreIn 2)
    hcoreY le_rfl (isPGroup_pCoreIn 2 W) (hL.1.trans hWcore) hcomm'
  rwa [hres] at hh

open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- The original marked-five residual excludes the nonquasisimple branch
for its chosen outside overcomponent. -/
public theorem source_dihedral_five_overcomponent_quasisimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V K L₁ : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    let W := ChapterF.Source.generated ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S
    let R := (Y ⊔ S).pCoreIn 2
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W R (W ⊓ M) →
    L₁ ∈ Chapter1.cComponentsIn W → generalizedFitting L₁ = pCore 2 L₁ →
    W ≤ normalizer (L₁ : Set G) → Chapter1.IsSylowIn 2 S W →
    Y ≤ L₁ → ¬ L₁ ≤ M → IsQuasisimple (L₁ ⧸ pCore 2 L₁) := by
  intro Y S W R hsetup hL hf hWN hSyl hYL hout
  by_contra hn
  have hYM : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  have hMN : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp
      (source_dihedral_five_residual_normal T hM.1.2 hu hV l hd)
  have hc : Nat.card (Y ⧸ pCore 2 Y) = 5 := by
    rw [←(pCore 2 Y).index_eq_card]
    exact (source_dihedral_five_residual_core_index hG T hempty hM hJ hu hmany hV l
      ((primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)) hd).1
  have hSM : S ≤ W ⊓ M := le_inf
    (Chapter1.isSylowIn_iff.mp hSyl).2.1 (inf_le_left.trans hM.1.2)
  have hLN := nonquasisimple_component_normalizes_five_residual hsetup hL hf hWN hSyl hSM
    hYL (inf_le_right.trans hMN) (source_caseIIResidual_isPPerfect T M _ Mc) hc hn
  exact hout (hLN.trans
    (source_dihedral_five_residual_core_normalizer hG T hempty hM hJ hu hmany hV l
      ((primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)) hd).2.2)

/-- The original failed-parabolic configuration has quasisimple overcomponent
quotient. The chosen K, W, R and L₁ remain fixed throughout the proof. -/
public theorem source_HStar_wreath_five_failed_quotient_quasisimple_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let R := (Y ⊔ S).pCoreIn 2
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (pCore 2 W ≠ ⊥ →
        (¬ ∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
          pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) →
        Chapter1.IsSylowIn 2 S W ∧ V ≤ W.pCoreIn 2 ∧
        generalizedFitting W = pCore 2 W ∧
        Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W R (W ⊓ M) ∧
        ∃ L₁ : Subgroup G, L₁ ∈ Chapter1.cComponentsIn W ∧ K ≤ L₁ ∧ ¬ L₁ ≤ M ∧
          W ≤ normalizer (L₁ : Set G) ∧ W = L₁ ⊔ (W ⊓ M) ∧
          generalizedFitting L₁ = pCore 2 L₁ ∧
          ¬ Chapter1.IsSylowIn 2 R (L₁ ⊔ R) ∧ Y ≤ L₁ ∧
          IsQuasisimple (L₁ ⧸ pCore 2 L₁)) := by
  obtain ⟨l,hd,_⟩ := source_HStar_wreath_five_reduction
    hG T hempty hM hJ hu hmany hV hcases hH he
  obtain ⟨K,hK,heK,hout,hi,hJS,hconf⟩ :=
    source_HStar_wreath_five_failed_quotient_residual_in_component
      hG T hempty hM hJ hu hmany hV hcases hH he
  refine ⟨K,hK,heK,hout,hi,hJS,?_⟩
  intro hcore hfailed
  obtain ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL⟩ :=
    hconf hcore hfailed
  refine ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL,?_⟩
  exact source_dihedral_five_overcomponent_quasisimple hG T hempty hM hJ hu hmany hV l hd
    hsetup hL₁ hLfit hNL hSyl hYL houtL

end CFSG.Quasithin.Chapter15.Section02
