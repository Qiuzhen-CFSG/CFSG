module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalSpecialLinearBorel
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalRankTwo
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentNormalizer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction.LocalThreePart
public import Theory.SpecificGroups.SL3.FourBorelResidual
/-!
# Original containment and Borel markings in the normal SL₃(4) row

The full original Sylow normalizer lies in M and is normalized by L₁.
Its cubic residual lies in the original L₁ and carries all of its three-part.
Two-perfectness forces L₁ into this Borel, hence into K. Cubic generation
of the model Borel identifies the image of the same L₁ in K/O₂(K).
The component equivalence transports this exact image to H/O₂(H), with
its original Sylow, yielding T intersect K <= O₂(L₁T) through the full
ambient kernel. In the reduced actor this also proves H=KT.

Source: Aschbacher–Smith 12.6.31, printed pp.836–837. The earlier geometry
remains explicit; the module exclusion and universal natural reduction are
not concluded by these structural results.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)


private theorem point_threeResidual_le (B : Subgroup G)
    (hBM : B ≤ M L) (hBG : B ≤ (D.fullSetup hZ T z).Gz) :
    (primeToResidual 3 B).map B.subtype ≤ (D.fullSetup hZ T z).L₁ := by
  let E := D.fullSetup hZ T z
  let Y := (primeToResidual 3 B).map B.subtype
  have hYL : Y ≤ L := (embedded_primeToResidual_mono 3 hBM).trans_eq
    (S.normalizer_primeToResidual D)
  have hYC : Y ≤ L ⊓ E.Gz := le_inf hYL
    ((map_subtype_le _).trans hBG)
  have hpY : IsPPerfect 2 Y :=
    (isPPerfect_primeToResidual (G := B) 3 2 (by decide)).of_surjective
      (B.subtype.subgroupMap (primeToResidual 3 B)) (B.subtype.subgroupMap_surjective _)
  have hYe : (pResidual 2 Y).map Y.subtype = Y := by
    rw [(pResidual_eq_top_iff 2 Y).mpr hpY,←MonoidHom.range_eq_map,range_subtype]
  have hY : Y ≤ E.L₁ := by
    rw [←hYe]
    exact embedded_pResidual_mono 2 hYC
  exact hY

include hz hTV hTz hbound hTI hns hH hKH in
/-- The original point residual is contained in the full special-linear Borel. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_point_borel
    (hn : (K.subgroupOf H).Normal)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4) :
    ∃ P : Sylow 2 K,
      (P : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K ∧
      (D.fullSetup hZ T z).L₁ ≤ (normalizer (P : Set K)).map K.subtype ∧
      (normalizer (P : Set K)).map K.subtype ≤ M L ∧
      ((normalizer (P : Set K)).map K.subtype).pCoreIn 2 = (T : Subgroup G) ⊓ K := by
  let E := D.fullSetup hZ T z
  obtain ⟨P,hP,hBM,hsol,hnB,hcore⟩ :=
    S.original_abelian_normal_specialLinearThree_sylow_normalizer
      D hZ z hz hTV hTz hbound hTI hns hH hKH hn (by decide : 2 ≤ 2) hm
  let N := normalizer (P : Set K)
  let B := N.map K.subtype
  have hBK : B ≤ K := map_subtype_le _
  have hY := point_threeResidual_le S D hZ z B hBM (hBK.trans (hKH.trans hH.2.1))
  obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let q : K →* SL(3,F) := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := P.mapSurjective hq
  have hN : N.map q = normalizer (R : Set SL(3,F)) := P.normalizer_map_surjective q hq
  have h9 : 9 ∣ Nat.card B := by
    have hc : Nat.card ((normalizer (R : Set SL(3,F))) ⧸
        pCore 2 (normalizer (R : Set SL(3,F)))) = 9 := by
      rw [Nat.card_congr (Matrix.PSL3.CartanActions.BorelQuotient.sylowSLNormalizerQuotientEquiv
        F (by decide : 0 < 2) hcard R).toEquiv,Nat.card_prod,Nat.card_units,hcard]
    have hd := hc ▸ card_quotient_dvd_card (pCore 2 (normalizer (R : Set SL(3,F))))
    have hncard : Nat.card (normalizer (R : Set SL(3,F))) ∣ Nat.card N := by
      rw [←hN]
      exact card_dvd_of_surjective (q.subgroupMap N) (q.subgroupMap_surjective N)
    rw [←Nat.card_congr (N.equivMapOfInjective K.subtype K.subtype_injective).toEquiv]
    exact hd.trans hncard
  have hval : 2 ≤ (Nat.card B).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h9
  obtain ⟨_,_,_,e9,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
  have hquot : Nat.card (E.L₁ ⧸ pCore 2 E.L₁) = 3 ^ 2 :=
    (Nat.card_congr e9.toEquiv).trans BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9_card
  have hLB : E.L₁ ≤ B := by
    by_contra hout
    have hh := Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction.borel_three_valuation_lt_of_outside
      B B E.L₁ le_rfl hout hY (le_sup_left.trans hnB)
      (isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)) 2 hquot
    omega
  exact ⟨P,hP,hLB,hBM,hcore⟩

include hz hTV hTz hbound hTI hns hH hKH in
/-- L₁ has the full Borel image through the literal intrinsic two-core quotient. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_borel_quotient
    (hn : (K.subgroupOf H).Normal)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4) :
    ∃ P : Sylow 2 K,
      (P : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K ∧
      (D.fullSetup hZ T z).L₁ ≤ K ∧
      (((D.fullSetup hZ T z).L₁).subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) =
        normalizer (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K)) :
          Set (K ⧸ pCore 2 K)) := by
  let E := D.fullSetup hZ T z
  obtain ⟨P,hP,hLB,hBM,_⟩ := S.original_abelian_normal_specialLinearFour_point_borel
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hm
  let N := normalizer (P : Set K)
  let B := N.map K.subtype
  have hBK : B ≤ K := map_subtype_le _
  have hLK : E.L₁ ≤ K := hLB.trans hBK
  let q := QuotientGroup.mk' (pCore 2 K)
  let R := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hN : N.map q = normalizer (R : Set (K ⧸ pCore 2 K)) :=
    P.normalizer_map_surjective q (QuotientGroup.mk'_surjective _)
  have hY := point_threeResidual_le S D hZ z B hBM (hBK.trans (hKH.trans hH.2.1))
  obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let R' := R.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hNe : (normalizer (R : Set (K ⧸ pCore 2 K))).map eK.toMonoidHom =
      normalizer (R' : Set SL(3,F)) :=
    map_normalizer_eq_of_bijective _ eK.bijective
  let eN : normalizer (R : Set (K ⧸ pCore 2 K)) ≃* normalizer (R' : Set SL(3,F)) :=
    (equivMapOfInjective _ eK.toMonoidHom eK.injective).trans (MulEquiv.subgroupCongr hNe)
  have hres : primeToResidual 3 (normalizer (R : Set (K ⧸ pCore 2 K))) = ⊤ := by
    apply (map_injective (f := eN.toMonoidHom) eN.injective)
    rw [map_primeToResidual_of_surjective 3 eN.toMonoidHom eN.surjective,
      Matrix.SL3.four_sylowNormalizer_primeToResidual hcard R',
      map_top_of_surjective _ eN.surjective]
  have hBsub : B.subgroupOf K = N := comap_map_eq_self_of_injective K.subtype_injective _
  have hYsub : (((primeToResidual 3 B).map B.subtype).subgroupOf K).map q =
      normalizer (R : Set (K ⧸ pCore 2 K)) := by
    have ht := map_embedded_primeToResidual_of_hom 3 N K.subtype
    apply_fun Subgroup.comap K.subtype at ht
    rw [comap_map_eq_self_of_injective K.subtype_injective] at ht
    change (((primeToResidual 3 (N.map K.subtype)).map (N.map K.subtype).subtype).comap K.subtype).map q = _
    rw [←ht,map_embedded_primeToResidual_of_hom,hN,hres,
      ←MonoidHom.range_eq_map,range_subtype]
  refine ⟨P,hP,hLK,le_antisymm ?_ ?_⟩
  · rw [←hN,←hBsub]
    exact map_mono (comap_mono hLB)
  · rw [←hYsub]
    exact map_mono (comap_mono hY)

include hz hTV hTz hbound hTI hns hH hKH hK in
/-- The same L₁ image is the full Borel in H/O₂(H), with the original Sylow image. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_borel_star
    (hn : (K.subgroupOf H).Normal)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4) :
    ∃ P : Sylow 2 (actorImage H K),
      (P : Subgroup (actorImage H K)).map (actorImage H K).subtype =
        actorImage H ((T : Subgroup G) ⊓ K) ∧
      (normalizer (P : Set (actorImage H K))).map (actorImage H K).subtype =
        actorImage H (D.fullSetup hZ T z).L₁ := by
  obtain ⟨P,hP,hLK,hquot⟩ := S.original_abelian_normal_specialLinearFour_borel_quotient
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hm
  let q := QuotientGroup.mk' (pCore 2 K)
  let e : (K ⧸ pCore 2 K) ≃* actorImage H K := componentStarEquiv H K hKH hK
  have him (Y : Subgroup G) (hYK : Y ≤ K) :
      ((Y.subgroupOf K).map q).map ((actorImage H K).subtype.comp e.toMonoidHom) =
        actorImage H Y := by
    have hf : ((actorImage H K).subtype.comp e.toMonoidHom).comp q =
        (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hKH) := by
      ext k
      exact componentStarEquiv_mk H K hKH hK k
    rw [map_map,hf,←map_map]
    have hi : (Y.subgroupOf K).map (inclusion hKH) = Y.subgroupOf H := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x,hYK hx⟩,hx,rfl⟩
    rw [hi]
    rfl
  let R := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective,?_,?_⟩
  · change (((P : Subgroup K).map q).map e.toMonoidHom).map (actorImage H K).subtype = _
    rw [map_map]
    have hi : ((T : Subgroup G) ⊓ K : Subgroup G).subgroupOf K = (P : Subgroup K) := by
      rw [←hP]
      exact comap_map_eq_self_of_injective K.subtype_injective _
    rw [←hi]
    exact him _ inf_le_right
  · change (normalizer ((R : Subgroup (K ⧸ pCore 2 K)).map e.toMonoidHom :
        Set (actorImage H K))).map (actorImage H K).subtype = _
    change (((D.fullSetup hZ T z).L₁).subgroupOf K).map q =
      normalizer (R : Set (K ⧸ pCore 2 K)) at hquot
    rw [←map_normalizer_eq_of_bijective _ (f := e.toMonoidHom) e.bijective,map_map]
    change (normalizer (R : Set (K ⧸ pCore 2 K))).map _ = _
    rw [←hquot]
    exact him _ hLK

include hz hTV hTz hbound hTI hns hH hKH hK in
/-- The intrinsic two-core of L₁-star is the full original component Sylow image. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_star_core
    (hn : (K.subgroupOf H).Normal)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4) :
    (actorImage H (D.fullSetup hZ T z).L₁).pCoreIn 2 =
      actorImage H ((T : Subgroup G) ⊓ K) := by
  obtain ⟨P,hP,hB⟩ := S.original_abelian_normal_specialLinearFour_borel_star
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm
  have hs : (normalizer (P : Set (actorImage H K))).pCoreIn 2 = P := by
    apply P.is_maximal' (isPGroup_pCoreIn 2 _)
    exact le_pCoreIn_of_normalizes P.isPGroup' P.le_normalizer le_rfl
  rw [←hB,←map_pCoreIn_of_injective 2 _ _ (actorImage H K).subtype_injective,hs,hP]

include hz hTV hTz hbound hTI hns hH hKH in
/-- On the same reduced actor, L₁ lies in K and the original H equals KT. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_reduction
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H)
    (hn : (K.subgroupOf H).Normal)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4) :
    (D.fullSetup hZ T z).L₁ ≤ K ∧ K ⊔ (T : Subgroup G) = H := by
  obtain ⟨_,_,hLK,_⟩ := S.original_abelian_normal_specialLinearFour_borel_quotient
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hm
  have hg := hgen
  rw [conjugateSpan_eq_of_normal H K T hKH (fun x hx => hH.1.2 (Or.inr hx)) hn,
    sup_eq_left.mpr hLK] at hg
  exact ⟨hLK,hg⟩

include hz hTV hTz hbound hTI hns hH hKH hK in
/-- The full ambient two-core kernel lifts the Borel-core identity to the original edge. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_sylow_le_edge_core
    (hn : (K.subgroupOf H).Normal)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4) :
    (T : Subgroup G) ⊓ K ≤ (D.fullSetup hZ T z).R₁ := by
  apply S.original_sylow_intersection_le_edge_core_of_star_core D hZ z hTV hH
  exact S.original_abelian_normal_specialLinearFour_star_core
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm

end CFSG.Quasithin.Chapter12.Section06
