module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalCoreSpan
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsResidualRank
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentCondition
public import Theory.Quasithin.PositiveLocalRank

/-!
# The original residual moves the actual HS overcomponent

The common residual has a nontrivial perfect two-by-A5 image in the
singular star quotient. An elementary nine-group centralizing that image
would be disjoint from it, because its center is a two-group, and would
force three-rank at least three. The surviving original Sylow of L1
therefore moves the same ordinary component.

This constructs the literal component action and condition (*) from the
original escaping HS configuration. It retains the full perpendicular
and conjugate-span containment in the same intrinsic core. Nonsingular
centralizer control and a component-action hypothesis are not assumed.
The final HS exclusion remains a separate obligation.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

section Action
variable (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

private theorem component_action_of_residual_movement
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H)
    (hcomm : ⁅Nonabelian.Setup.star H c.K,
      Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁⁆ =
      Nonabelian.Setup.star H c.K) :
    Nonempty c.ActionMarking := by
  let E := D.fullSetup hZ T z
  let X := c.K ⊔ E.L₁ ⊔ V
  let B := Nonabelian.Setup.star H c.K
  let A := Nonabelian.Setup.star H E.L₁
  let U := Nonabelian.Setup.star H V
  let N := normalizer (B : Set (H ⧸ pCore 2 H))
  let q := QuotientGroup.mk' (pCore 2 H)
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hVH : V ≤ H := S.chosen.le_sylow.trans (fun x hx => hH.1.2 (Or.inr hx))
  have hAX : E.L₁ ≤ X := le_sup_right.trans le_sup_left
  have hVX : V ≤ X := le_sup_right
  have hXH : X ≤ H := sup_le (sup_le c.le_H hAH) hVH
  have hAN : A ≤ N := S.original_residual_star_normalizes_selectedComponent D hZ z hz hH c
  have hUN : U ≤ N := c.normalized
  have hXN : Nonabelian.Setup.star H X ≤ N := by
    change ((c.K ⊔ E.L₁ ⊔ V).subgroupOf H).map q ≤ N
    rw [subgroupOf_sup (sup_le c.le_H hAH) hVH,
      subgroupOf_sup c.le_H hAH,Subgroup.map_sup,Subgroup.map_sup]
    exact sup_le (sup_le B.le_normalizer hAN) hUN
  let j : X →* N := (q.comp (inclusion hXH)).codRestrict N
    (fun x => hXN (mem_map_of_mem q x.property))
  let a : X →* MulAut B := B.normalizerMonoidHom.comp j
  have hmap (R : Subgroup G) (hRX : R ≤ X) :
      (R.subgroupOf X).map j = (Nonabelian.Setup.star H R).subgroupOf N := by
    ext n
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact mem_map_of_mem q hx
    · intro hn
      obtain ⟨r,hr,he⟩ := hn
      exact ⟨⟨r.val,hRX hr⟩,hr,Subtype.ext he⟩
  have ha (R : Subgroup G) (hRX : R ≤ X) :
      (R.subgroupOf X).map a = ((Nonabelian.Setup.star H R).subgroupOf N).map B.normalizerMonoidHom := by
    change (R.subgroupOf X).map (B.normalizerMonoidHom.comp j) = _
    rw [←Subgroup.map_map,hmap R hRX]
  have hzero (R : Subgroup G) (hRX : R ≤ X)
      (hRN : Nonabelian.Setup.star H R ≤ N) :
      (R.subgroupOf X).map a = ⊥ ↔
        Nonabelian.Setup.star H R ≤ centralizer (B : Set (H ⧸ pCore 2 H)) := by
    rw [ha R hRX,Subgroup.map_eq_bot_iff,normalizerMonoidHom_ker]
    constructor
    · intro hc r hr
      exact hc (show (⟨r,hRN hr⟩ : N) ∈ (Nonabelian.Setup.star H R).subgroupOf N from hr)
    · intro hc r hr
      exact hc hr
  have hUne : (V.subgroupOf X).map a ≠ ⊥ := by
    intro he
    exact c.moved (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp ((hzero V hVX hUN).mp he)))
  have hAne : (E.L₁.subgroupOf X).map a ≠ ⊥ := by
    intro he
    have hzeroA := commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp ((hzero E.L₁ hAX hAN).mp he))
    rw [hcomm] at hzeroA
    exact c.moved (by rw [hzeroA,commutator_bot_left])
  have hcardU : Nat.card ((V.subgroupOf X).map a) = 2 := by
    have hd := card_map_dvd (U.subgroupOf N) B.normalizerMonoidHom
    rw [Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv] at hd
    have hc : Nat.card U = 2 :=
      (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.1
    rw [hc,←ha V hVX] at hd
    exact ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd).resolve_left
      (fun h => hUne (Subgroup.card_eq_one.mp h))
  let F := (E.L₁.subgroupOf X).map a
  let e := (subgroupOfEquivOfLe hAX).symm
  let f : E.L₁ →* F := (a.subgroupMap (E.L₁.subgroupOf X)).comp e.toMonoidHom
  have hf : Function.Surjective f := (a.subgroupMap_surjective _).comp e.surjective
  have hpF : IsPPerfect 2 F := (isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)).of_surjective f hf
  have hthree : 3 ∣ Nat.card F := by
    by_contra hnot
    have hd : Nat.card F ∣ Nat.card E.L₁ := Subgroup.card_dvd_of_surjective f hf
    obtain ⟨_,_,_,eqv,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
    have hq : Nat.card (E.L₁ ⧸ pCore 2 E.L₁) = 9 :=
      (Nat.card_congr eqv.toEquiv).trans BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9_card
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := E.L₁)).exists_card_eq
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 E.L₁),hq,hn] at hd
    have hcop : Nat.Coprime (Nat.card F) 9 :=
      ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hnot).symm.pow_right 2
    have htwo : IsPGroup 2 F := isPGroup_iff_card_dvd_pow.mpr
      ⟨n,hcop.dvd_of_dvd_mul_left hd⟩
    have hid := hpF.hom_eq_one_of_isPGroup htwo (MonoidHom.id F)
    apply hAne
    apply bot_unique
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun hid ⟨x,hx⟩)
  have hcentral : F ≤ centralizer ((V.subgroupOf X).map a : Set (MulAut B)) := by
    change (E.L₁.subgroupOf X).map a ≤ _
    rw [ha E.L₁ hAX,ha V hVX]
    apply (map_mono (f := B.normalizerMonoidHom) ?_).trans (map_centralizer_le_centralizer_image _ _)
    rintro r hr u hu
    apply Subtype.ext
    exact S.original_point_residual_star_centralizes D hZ z hz hTV hTz hbound hH hn hr u.val hu
  have hKX : c.K ≤ X := le_sup_left.trans le_sup_left
  have hinner : (c.K.subgroupOf X).map a = MulAut.innerSubgroup B := by
    rw [ha c.K hKX]
    ext b
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,by ext y; rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,B.le_normalizer x.property⟩,x.property,by ext y; rfl⟩
  have hKN : (c.K.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (sup_le c.K.le_normalizer
      (S.original_residual_normalizes_selectedComponent D hZ z hz hH c))
      (S.original_module_normalizes_selectedComponent D hZ z hH c))
  refine ⟨⟨hXH,hKN,a,fun _ _ => rfl,?_,hinner,hcardU,hAne,hpF,hthree,hcentral⟩⟩
  ext x
  change B.normalizerMonoidHom (j x) = 1 ↔ _
  rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker]
  rfl

end Action

/-- The actual HS configuration supplies condition (*) on the same ordinary
component, together with its core-span containment and its original residual
commutator. Every action and rank conclusion is derived from the source. -/
theorem SourceHypothesis.exists_original_hs_component_with_residual_action
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ hZ : ZV L V = ⊥, ∃ z : V, z ≠ 1 ∧ ¬ D.Nonsingular z ∧
      (T : Subgroup G) ≤ Gv (z : G) ∧ ¬ Gv (z : G) ≤ M L ∧
      Gv (z : G) ∈ (D.fullSetup hZ T z).Hz ∧
      ¬ IsMulCommutative ((D.fullSetup hZ T z).VH (Gv (z : G))) ∧
      ∃ c : (D.fullSetup hZ T z).SelectedComponent (Gv (z : G)),
        (D.fullSetup hZ T z).V₅ ≤ c.K.pCoreIn 2 ∧
        (D.fullSetup hZ T z).UH (Gv (z : G)) ≤ c.K.pCoreIn 2 ∧
        ⁅Nonabelian.Setup.star (Gv (z : G)) c.K,
          Nonabelian.Setup.star (Gv (z : G)) (D.fullSetup hZ T z).L₁⁆ =
          Nonabelian.Setup.star (Gv (z : G)) c.K ∧
        (primeRank 3 (Nonabelian.Setup.star (Gv (z : G)) c.K) = 1 ∨
          primeRank 3 (Nonabelian.Setup.star (Gv (z : G)) c.K) = 2) ∧
        ∃ a : c.ActionMarking,
          let A := (((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
          let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
          let C := centralizer (U : Set a.action.range)
          Nat.card U = 2 ∧ 3 ∣ Nat.card A ∧
          A.subgroupOf C ≤ (pCore 3 (C ⧸ pCore 2 C)).comap (QuotientGroup.mk' (pCore 2 C)) ∧
          ∃ R : Sylow 2 a.action.range, U ≤ (R : Subgroup a.action.range) ∧
            U ≤ centralizer (R : Set a.action.range) := by
  classical
  obtain ⟨hZ,u,w,_,_,_,P,t,_,_,_,hz,hsz,hTz,_,hout,hHz,
    _,_,hperf,⟨eJ⟩,hmoveJ,K,hKG,hK,hordinary,hJK,hKN,_,_,hmove,hV5,hUH⟩ :=
    H.exists_original_hs_normal_overcomponent_core_span D hTV hTI v hv he
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
  refine ⟨hZ,z,hz,hsz,hTz,hout,hHz',hn,c,hV5,hUH,hres,hrank,a,?_,?_,
    H.original_action_residual_le_centralizer_twoThreeCore D hZ z hz hTV hnz hbound hHz' hn c a,
    H.original_action_module_sylow_central D hZ z hz hTV hnz hbound hHz' hn c a⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe (map_le_range _ _)).toEquiv]
    exact a.module_card
  · rw [Nat.card_congr (subgroupOfEquivOfLe (map_le_range _ _)).toEquiv]
    exact a.residual_three_dvd

end CFSG.Quasithin.Chapter12.Section06
