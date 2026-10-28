module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalFiveCore
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsResidualStar
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalResidualComponentAction
import all CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalResidualComponentAction

/-!
# The selected component contains the literal original local A5

The full original common residual is retained through the singular quotient.
The same actual normal overcomponent, selected action, original ambient
Sylow, and HS covering witnesses are kept together. The internal import is
an intentional proof split reusing the already checked action construction;
no private name enters the public statement.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original escaping HS branch supplies a literal local A5 in the same
selected normal component and its original action marking. -/
theorem SourceHypothesis.exists_original_hs_selected_local_five
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ hZ : ZV L V = ⊥, ∃ u w : V,
      D.Nonsingular u ∧ D.Nonsingular w ∧ w ≠ u ∧
      ∃ P : Sylow 2 G, ∃ t ∈ (P : Subgroup G),
        (MulAut.conj t) (u : G) = w ∧ (MulAut.conj t) (w : G) = u ∧
        let z := u*w
        z ≠ 1 ∧ ¬ D.Nonsingular z ∧
        (T : Subgroup G) ≤ Gv (z : G) ∧ ∃ hPz : (P : Subgroup G) ≤ Gv (z : G),
        ¬ Gv (z : G) ≤ M L ∧ Gv (z : G) ∈ (D.fullSetup hZ T z).Hz ∧
        IsQuasisimple (Kv (u : G)) ∧ ¬ Kv (u : G) ≤ M L ∧
        Nonempty ((Kv (u : G) ⧸ center (Kv (u : G))) ≃*
          Sporadic.LeechRelated.HS.Carrier) ∧
        ∃ S : Sylow 2 (Gv (u : G)),
          (z : G) ∈ (center ((S : Subgroup (Gv (u : G))).map
            (Gv (u : G)).subtype)).map ((S : Subgroup (Gv (u : G))).map
            (Gv (u : G)).subtype).subtype ∧
          (z : G) ∉ centralizer (Kv (u : G) : Set G) ∧
        let X := Gv (z : G)
        let B := Gv (u : G) ⊓ X
        let J := (primeToResidual 3 B).map B.subtype
        J ≤ Kv (u : G) ⊓ Kv (w : G) ∧
        (P : Subgroup G) ≤ normalizer (J : Set G) ∧
        J ∈ Chapter1.LIn X (P : Subgroup G) ∧ J.pCoreIn 2 ≤ X.pCoreIn 2 ∧
        Group.IsPerfect J ∧ Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∧
        Nonempty (Nonabelian.Setup.star X J ≃* alternatingGroup (Fin 5)) ∧
        Nonabelian.Setup.star X J ∈ ChapterA.Section03.localCComponents
          ((P.subtype hPz).mapSurjective
            (QuotientGroup.mk'_surjective (pCore 2 X))) ∧
        Nonabelian.Setup.star X (P : Subgroup G) ≤
          normalizer (Nonabelian.Setup.star X J : Set (X ⧸ pCore 2 X)) ∧
        ¬ IsMulCommutative ((D.fullSetup hZ T z).VH X) ∧
        ∃ c : (D.fullSetup hZ T z).SelectedComponent X,
          J ≤ c.K ∧ X ≤ normalizer (c.K : Set G) ∧
          (D.fullSetup hZ T z).V₅ ≤ c.K.pCoreIn 2 ∧
          (D.fullSetup hZ T z).UH X ≤ c.K.pCoreIn 2 ∧
          ⁅Nonabelian.Setup.star X c.K,
            Nonabelian.Setup.star X (D.fullSetup hZ T z).L₁⁆ =
            Nonabelian.Setup.star X c.K ∧
          (primeRank 3 (Nonabelian.Setup.star X c.K) = 1 ∨
            primeRank 3 (Nonabelian.Setup.star X c.K) = 2) ∧
          Nonempty c.ActionMarking := by
  classical
  obtain ⟨hZ,u,w,hu,hw,huw,P,t,ht,htu,htw,hz,hsz,hTz,hPz,hout,hHz,
    hKu,hKunot,⟨e⟩,S,hzS,hzc,hJC,hPJ,hlocal,hJcore,hperf,⟨eJ⟩,
    hmoveJ,K,hKG,hK,hordinary,hJK,hKN,huCore,hwCore,hmove,hV5,hUH⟩ :=
    H.exists_original_hs_five_core_configuration D hTV hTI v hv he
  let z := u*w
  let X := Gv (z : G)
  let E := D.fullSetup hZ T z
  let B := Gv (u : G) ⊓ X
  let J := (primeToResidual 3 B).map B.subtype
  let := hperf
  let π := QuotientGroup.mk' (pCore 2 X)
  let K₀ := K.subgroupOf X
  let K₁ := K₀.map π
  have hHz' : X ∈ E.Hz := by rwa [E.Gz_eq] at hHz
  have hnz : (T : Subgroup G) ≤ normalizer (E.V₁ : Set G) := by
    change (T : Subgroup G) ≤ normalizer (zpowers (z : G) : Set G)
    apply hTz.trans
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    rfl
  have hcoreN : X ≤ normalizer (X.pCoreIn 2 : Set G) :=
    X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hVnot : ¬ V ≤ X.pCoreIn 2 := by
    intro hc
    apply hmove
    rw [commutator_comm]
    exact (commutator_mono hKG hc).trans
      (le_normalizer_iff_commutator_le_right.mp hcoreN)
  have hbound := H.original_hs_conjugate_intersection_bound D hTV hTI v hv he
  have ha := H.original_abelian_criteria D hZ z hz hTV hnz hbound hHz'
  have hn : ¬ IsMulCommutative (E.VH X) :=
    fun hc => hVnot (ha.1.mp (ha.2.2.mpr hc))
  let eK : K ≃* K₀ := (subgroupOfEquivOfLe hKG).symm
  let d : (K ⧸ pCore 2 K) ≃* K₁ :=
    (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans
      (cComponentTwoCoreQuotientEquiv hK)
  let : IsQuasisimple K₁ := hordinary.of_mulEquiv d
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer hKN
  let : K₁.Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have hc : IsComponent (X ⧸ pCore 2 X) K₁ :=
    ⟨(inferInstance : K₁.Normal).isSubnormal,inferInstance⟩
  have hnorm : Nonabelian.Setup.star X V ≤ normalizer (K₁ : Set (X ⧸ pCore 2 X)) :=
    le_normalizer_of_normal
  have hm : ⁅K₁,Nonabelian.Setup.star X V⁆ ≠ ⊥ := by
    intro hh
    have hi : ⁅K₀,V.subgroupOf X⁆ ≤ pCore 2 X := by
      have hmap : (⁅K₀,V.subgroupOf X⁆).map π = ⊥ := by
        rw [map_commutator]
        exact hh
      simpa only [π,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hmap
    have ha := map_mono (f := X.subtype) hi
    rw [map_commutator,map_subgroupOf_eq_of_le hKG,
      map_subgroupOf_eq_of_le (V_le_Gv z),commutator_comm] at ha
    exact hmove ha
  have hfull := hc.commutator_eq_self_of_normalizes hnorm hm
  have hVM : V ≤ (M L).pCoreIn 2 := H.chosen.le_componentCore.trans
    (pCoreIn_mono_of_normalizes L.le_normalizer (le_refl (M L)))
  let c : E.SelectedComponent X :=
    ⟨K,hKG,hK,hc,hm,hnorm,hfull,E.component_not_le_M hc hVM hfull⟩
  have hJX : J ≤ X := hJK.trans hKG
  let f : J →* (X ⧸ pCore 2 X) := π.comp (inclusion hJX)
  have hf : f.range = Nonabelian.Setup.star X J := by
    rw [MonoidHom.range_comp,inclusion_range]
    rfl
  have hfne : f.range ≠ ⊥ := by
    intro hh
    rw [hf] at hh
    have hi : J.subgroupOf X ≤ pCore 2 X := by
      change (J.subgroupOf X).map π = ⊥ at hh
      simpa only [π,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hh
    have hJcore : J ≤ X.pCoreIn 2 := by
      rw [←map_subgroupOf_eq_of_le hJX]
      exact map_mono hi
    exact hmoveJ ((commutator_mono (V_le_Gv z) hJcore).trans
      (le_normalizer_iff_commutator_le_right.mp hcoreN))
  have hres : ⁅Nonabelian.Setup.star X K,Nonabelian.Setup.star X E.L₁⁆ =
      Nonabelian.Setup.star X K := by
    apply hc.commutator_eq_self_of_normalizes
      (H.original_residual_star_normalizes_selectedComponent D hZ z hz hHz' c)
    intro hzero
    let S : Sylow 3 E.L₁ := default
    let A := (S : Subgroup E.L₁).map E.L₁.subtype
    obtain ⟨hA,hcard,_⟩ := H.original_point_sylow_star D hZ z hz hnz hHz' S
    let := hA
    apply OriginalHigmanSimsResidualRank.perfect_five_image_not_centralized_by_plane
      eJ f hfne (Nonabelian.Setup.star X A) hcard
      (H.original_star_three_rank D hZ z hz hHz')
    have hAc : Nonabelian.Setup.star X A ≤
        centralizer (Nonabelian.Setup.star X K : Set (X ⧸ pCore 2 X)) :=
      (map_mono (comap_mono (map_subtype_le _))).trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero))
    rw [hf]
    exact hAc.trans (centralizer_le (map_mono (comap_mono hJK)))
  have hthree : 3 ∣ Nat.card (Nonabelian.Setup.star X K) := by
    have hj := (OriginalHigmanSimsResidualRank.nontrivial_perfect_image_five_quotient eJ f hfne).2.1
    rw [hf] at hj
    exact hj.trans (card_dvd_of_le (map_mono (comap_mono hJK)))
  have hrank : primeRank 3 (Nonabelian.Setup.star X K) = 1 ∨
      primeRank 3 (Nonabelian.Setup.star X K) = 2 := by
    have hl := Theory.Quasithin.one_le_primeRank_of_dvd_card hthree
    have hu := (Theory.GroupTheory.primeRank_le_of_injective 3
      (Nonabelian.Setup.star X K).subtype (Nonabelian.Setup.star X K).subtype_injective).trans
        (H.original_star_three_rank D hZ z hz hHz')
    omega
  obtain ⟨a⟩ := component_action_of_residual_movement H D hZ z hz hTV hnz hbound hHz' hn c hres
  obtain ⟨hfive,hlocalstar⟩ := OriginalHigmanSimsResidualStar.star_five_mem_localCComponents
    X J P hPz hlocal hJcore eJ
  have hPJstar : Nonabelian.Setup.star X (P : Subgroup G) ≤
      normalizer (Nonabelian.Setup.star X J : Set (X ⧸ pCore 2 X)) :=
    (map_mono (show (P : Subgroup G).subgroupOf X ≤
      normalizer (J.subgroupOf X : Set X) by
        rw [←subgroupOf_normalizer_eq hJX]
        exact comap_mono hPJ)).trans (le_normalizer_map π)
  refine ⟨hZ,u,w,hu,hw,huw,P,t,ht,htu,htw,hz,hsz,hTz,hPz,hout,hHz',
    hKu,hKunot,⟨e⟩,S,hzS,hzc,hJC,hPJ,hlocal,hJcore,hperf,⟨eJ⟩,
    hfive,hlocalstar,hPJstar,hn,c,hJK,hKN,hV5,hUH,hres,hrank,⟨a⟩⟩

end CFSG.Quasithin.Chapter12.Section06
