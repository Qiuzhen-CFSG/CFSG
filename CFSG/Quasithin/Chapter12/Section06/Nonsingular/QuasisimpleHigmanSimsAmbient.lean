module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHigmanSimsGeneration
public import Theory.GroupTheory.IndexTwoCentralInvolution
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow

/-!
# An ambient central pair in the surviving HS configuration

Retain the original preferred point v, the selected Sylow S of G_v and
its ambient image S₀. The exact indices [T:T_v]=4 and [S₀:T_v]=2 put S₀
normally inside an ambient Sylow P with index two. An element t of P
outside S₀ exchanges v with a distinct conjugate w in the center of S₀.
Their product z is a nonidentity central involution of P.

The equality S₀ intersect N_G(V)=T_v and the original LT action kernel
place the entire center of S₀ in T_v intersect Q. In particular w and z
belong to the original Q. The original v and w are not two-central,
whereas z is. Even characteristic and the index-two inheritance theorem
make both G_z and G_v intersect G_z characteristic two. Consequently w
and z act nontrivially on the full K_v: otherwise the original quasisimple
C-component would persist in that common centralizer.

The preferred-point application keeps the selected S, original R and its
literal quotient image, full component generation, and the earlier
component conjugator s while constructing t. These are additional ambient
restrictions on the HS row. Its exclusion, the J4 exclusion, and the
remaining source discharge through 12.6.2 and 12.6.23 remain open.

Source: Aschbacher--Smith 12.6.4--5 and the inspection in 12.6.12,
printed pp.824--826; 1.1.4(2,7), printed pp.500--501, for the
characteristic-two inheritance used here.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The whole center of the original selected Sylow lies in the original core. -/
theorem SourceHypothesis.nonsingular_hs_selected_center_le_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ Kv (v : G) ≤ M L)
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) :
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    (center S₀).map S₀.subtype ≤ Tv T (v : G) ⊓ Q T L := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hNV := (H.nonsingular_hs_selected_sylow_conjugate D v hv hK hTV hnot hi e S hTS).1
  have hVS : V ≤ S₀ := (le_inf H.chosen.le_sylow (V_le_Gv v)).trans hTS
  change (center S₀).map S₀.subtype ≤ Tv T (v : G) ⊓ Q T L
  intro x hx
  rw [map_center_subtype_eq_inf_centralizer] at hx
  have hc : x ∈ centralizer (V : Set G) := centralizer_le hVS hx.2
  have hxT : x ∈ Tv T (v : G) := hNV.le ⟨hx.1,Subgroup.centralizer_le_normalizer _ hc⟩
  refine ⟨hxT,?_⟩
  rw [←H.join_centralizer_eq_core hTV]
  exact ⟨(show (T : Subgroup G) ≤ LT T L from le_sup_right) hxT.1,hc⟩

/-- The original HS point has a distinct conjugate in Q whose product with
it is two-central and acts nontrivially on the full original component. -/
theorem SourceHypothesis.nonsingular_hs_ambient_central_pair
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ Kv (v : G) ≤ M L)
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) :
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    ∃ P : Sylow 2 G,
      S₀ ≤ (P : Subgroup G) ∧ S₀.relIndex (P : Subgroup G) = 2 ∧
      (S₀.subgroupOf (P : Subgroup G)).Normal ∧
      (P : Subgroup G) ⊓ Gv (v : G) = S₀ ∧
      ∃ t ∈ (P : Subgroup G), t ∉ S₀ ∧
        let w := (MulAut.conj t) (v : G)
        w ≠ (v : G) ∧ (MulAut.conj t) w = (v : G) ∧
        w ∈ (center S₀).map S₀.subtype ∧ w ∈ Tv T (v : G) ⊓ Q T L ∧
        (v : G)*w ∈ (center (P : Subgroup G)).map (P : Subgroup G).subtype ∧
        (v : G)*w ∈ Tv T (v : G) ⊓ Q T L ∧
        (v : G)*w ≠ 1 ∧ ((v : G)*w)^2 = 1 ∧
        TwoCentral ((v : G)*w) ∧ ¬ TwoCentral (v : G) ∧ ¬ TwoCentral w ∧
        Gv ((v : G)*w) ∈ Chapter1.He G ∧
        Gv (v : G) ⊓ Gv ((v : G)*w) ∈ Chapter1.He G ∧
        w ∉ centralizer (Kv (v : G) : Set G) ∧
        (v : G)*w ∉ centralizer (Kv (v : G) : Set G) ∧
        (v : G)*w ∉ (center (Kv (v : G))).map (Kv (v : G)).subtype := by
  classical
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  obtain ⟨P,hP⟩ := S.exists_comap_subtype_eq
  have hSP : S₀ ≤ (P : Subgroup G) := by
    change (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype ≤ _
    rw [←hP]
    exact map_comap_le _ _
  have hPC : (P : Subgroup G) ⊓ Gv (v : G) = S₀ := by
    dsimp [S₀]
    rw [←hP,map_comap_eq,range_subtype,inf_comm]
  have hTS' : Tv T (v : G) ≤ (P : Subgroup G) := hTS.trans hSP
  have hcard : Nat.card P = Nat.card T := Nat.card_congr (P.equiv T).toEquiv
  have hcP := relIndex_mul_relIndex (⊥ : Subgroup G) (Tv T (v : G))
    (P : Subgroup G) bot_le hTS'
  have hcT := relIndex_mul_relIndex (⊥ : Subgroup G) (Tv T (v : G))
    (T : Subgroup G) bot_le inf_le_left
  simp only [relIndex_bot_left] at hcP hcT
  have hiP : (Tv T (v : G)).relIndex (P : Subgroup G) = 4 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Tv T (v : G)))
    rw [hcP,hcard,←hcT,hi]
  have hiS := (H.nonsingular_hs_selected_sylow_geometry D v hv hK hTV hi e S hTS).1
  have hiSP : S₀.relIndex (P : Subgroup G) = 2 := by
    have hm := relIndex_mul_relIndex (Tv T (v : G)) S₀ (P : Subgroup G) hTS hSP
    rw [hiS,hiP] at hm
    omega
  have hne : ¬ (P : Subgroup G) ≤ S₀ := by
    intro hh
    have he := (relIndex_eq_one.mpr hh)
    rw [hiSP] at he
    omega
  obtain ⟨t,ht,htS⟩ := SetLike.not_le_iff_exists.mp hne
  have hmove : (MulAut.conj t) (v : G) ≠ (v : G) := by
    intro hh
    apply htS
    apply hPC.le
    exact ⟨ht,mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh)⟩
  have hvS : (v : G) ∈ S₀ := hTS ⟨H.chosen.le_sylow v.property,V_le_Gv v v.property⟩
  have hvZ : (v : G) ∈ (center S₀).map S₀.subtype := by
    rw [map_center_subtype_eq_inf_centralizer]
    exact ⟨hvS,fun x hx => mem_centralizer_singleton_iff.mp (map_subtype_le _ hx)⟩
  have hv2 : (v : G)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ v.property
  obtain ⟨hwZ,hwne,hswap,hzZ,hz1,hz2,hzv⟩ :=
    central_involution_pair_of_relIndex_two S₀ (P : Subgroup G) hSP hiSP (v : G) hvZ hv2 t ht hmove
  let w := (MulAut.conj t) (v : G)
  have hZQ := H.nonsingular_hs_selected_center_le_core D v hv hK hTV hnot hi e S hTS
  have hwQ : w ∈ Tv T (v : G) ⊓ Q T L := hZQ hwZ
  have hzQ : (v : G)*w ∈ Tv T (v : G) ⊓ Q T L :=
    (Tv T (v : G) ⊓ Q T L).mul_mem (hZQ hvZ) hwQ
  have hzcentral : TwoCentral ((v : G)*w) := by
    have hz' : (v : G)*w ∈ (P : Subgroup G) ⊓ centralizer ((P : Subgroup G) : Set G) :=
      map_center_subtype_eq_inf_centralizer (P : Subgroup G) ▸ hzZ
    refine ⟨P,hz'.1,mem_center_iff.mpr ?_⟩
    intro x
    exact Subtype.ext (hz'.2 x x.property)
  have hvnon : ¬ TwoCentral (v : G) := by
    intro hc
    obtain ⟨P',hP'⟩ := hc.exists_sylow_le_centralizer
    exact H.nonsingular_quasisimple_no_ambient_sylow D v hv hK P' hP'
  have hwnon : ¬ TwoCentral w := by
    intro hc
    exact hvnon (hswap ▸ hc.map (MulAut.conj t))
  have hPz : (P : Subgroup G) ≤ Gv ((v : G)*w) := by
    have hz' : (v : G)*w ∈ (P : Subgroup G) ⊓ centralizer ((P : Subgroup G) : Set G) :=
      map_center_subtype_eq_inf_centralizer (P : Subgroup G) ▸ hzZ
    exact fun x hx => mem_centralizer_singleton_iff.mpr (hz'.2 x hx)
  have hzHe : Gv ((v : G)*w) ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le P (H.source.simpleQTKE.evenCharacteristic P)
      (isTwoLocal_involution_centralizer (orderOf_eq_prime hz2 hz1)) hPz
  have hcommon : Gv (v : G) ⊓ Gv ((v : G)*w) ∈ Chapter1.He G := by
    have hn : Gv (v : G) ⊓ Gv ((v : G)*w) ≠ ⊥ := by
      intro he
      have hm : (v : G) ∈ Gv (v : G) ⊓ Gv ((v : G)*w) :=
        ⟨V_le_Gv v v.property,hPz (hSP hvS)⟩
      rw [he,mem_bot] at hm
      exact nonsingular_ne_one D hv (Subtype.ext hm)
    have hPN : (P : Subgroup G) ⊓ (Gv (v : G) ⊓ Gv ((v : G)*w)) = S₀ := by
      rw [←inf_assoc,hPC,inf_eq_left.mpr (hSP.trans hPz)]
    apply Chapter1.lemma_1_1_4_7 hzHe (P.subtype hPz) hn inf_le_right
    rw [Sylow.coe_subtype,relIndex_subgroupOf hPz,←inf_relIndex_right,inf_comm,hPN,hiSP]
  have hznon : (v : G)*w ∉ centralizer (Kv (v : G) : Set G) := by
    intro hh
    let := hK
    have hKC : Kv (v : G) ≤ Gv (v : G) ⊓ Gv ((v : G)*w) :=
      le_inf (Kv_le_Gv _) (fun x hx => mem_centralizer_singleton_iff.mpr (hh x hx))
    have hcomp := (H.nonsingular_canonical_component D v hv).1.subgroupOf_of_le hKC inf_le_left
    exact hcomp.not_isQuasisimple_of_characteristic_two (Chapter1.mem_He_iff.mp hcommon)
      (IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKC).symm)
  have hwnot : w ∉ centralizer (Kv (v : G) : Set G) := by
    intro hh
    have hvC : (v : G) ∈ centralizer (Kv (v : G) : Set G) :=
      fun x hx => mem_centralizer_singleton_iff.mp (Kv_le_Gv _ hx)
    exact hznon ((centralizer (Kv (v : G) : Set G)).mul_mem hvC hh)
  have hznot : (v : G)*w ∉ (center (Kv (v : G))).map (Kv (v : G)).subtype := by
    intro hh
    exact hznon ((map_center_subtype_eq_inf_centralizer (Kv (v : G)) ▸ hh).2)
  exact ⟨P,hSP,hiSP,normal_of_index_eq_two hiSP,hPC,t,ht,htS,
    hwne,hswap,hwZ,hwQ,hzZ,hzQ,hz1,hz2,hzcentral,hvnon,hwnon,hzHe,hcommon,hwnot,hznon,hznot⟩

/-- At the original preferred point, retain the selected S, R, full quotient
map and component conjugator while constructing the ambient central pair. -/
theorem SourceHypothesis.exists_preferred_nonsingular_hs_ambient_pair
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ZV L V = ⊥ ∧ Nat.card V = 64 ∧
      ∃ u : V, D.Nonsingular u ∧ ¬ Gv (u : G) ≤ M L ∧
        Chapter1.IsSylowIn 2 (Tv T (u : G)) (Mv L (u : G)) ∧
        (Tv T (u : G)).relIndex (T : Subgroup G) = 4 ∧
        Lv L (u : G) < Kv (u : G) ∧ ¬ Kv (u : G) ≤ M L ∧
        V ⊓ centralizer (Kv (u : G) : Set G) = zpowers (u : G) ∧
        ZV (Lv L (u : G)) (Vv L V (u : G)) = zpowers (u : G) ∧
        (u : G) ∈ Vv L V (u : G) ∧ IsQuasisimple (Kv (u : G)) ∧
        NonsingularHSJankoCoverModels (Kv (u : G)) ∧
        ∃ S : Sylow 2 (Gv (u : G)),
          let S₀ := (S : Subgroup (Gv (u : G))).map (Gv (u : G)).subtype
          Tv T (u : G) ≤ S₀ ∧
          R L (Kv (u : G)) S₀ (u : G) ≤ normalizer (Lv L (u : G) : Set G) ∧
          ⁅Lv L (u : G), R L (Kv (u : G)) S₀ (u : G)⁆ ≤ (Lv L (u : G)).pCoreIn 2 ∧
          R L (Kv (u : G)) S₀ (u : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (u : G)) ∧
          ∀ e : ((Kv (u : G)) ⧸ center (Kv (u : G))) ≃* Sporadic.LeechRelated.HS.Carrier,
            let C := Kv (u : G)
            let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
            let B := ((Lv L (u : G)).subgroupOf C).map f
            ((R L C S₀ (u : G)).subgroupOf C).map f =
              (S₀.subgroupOf C).map f ⊓ coreQuotientCentralizer B ∧
            Lv L (u : G) ⊔ (S₀ ⊓ C) = C ∧
            ∃ s ∈ S₀ ⊓ C, s ∉ Tv T (u : G) ∧
              V.map (MulAut.conj s).toMonoidHom ≠ V ∧
              (Vv L V (u : G)).map (MulAut.conj s).toMonoidHom ≠ Vv L V (u : G) ∧
              V.map (MulAut.conj s).toMonoidHom ⊓ C =
                (Vv L V (u : G)).map (MulAut.conj s).toMonoidHom ∧
              ∃ P : Sylow 2 G,
                S₀ ≤ (P : Subgroup G) ∧ S₀.relIndex (P : Subgroup G) = 2 ∧
                (S₀.subgroupOf (P : Subgroup G)).Normal ∧
                (P : Subgroup G) ⊓ Gv (u : G) = S₀ ∧
                ∃ t ∈ (P : Subgroup G), t ∉ S₀ ∧
                  let w := (MulAut.conj t) (u : G)
                  w ≠ (u : G) ∧ (MulAut.conj t) w = (u : G) ∧
                  w ∈ (center S₀).map S₀.subtype ∧ w ∈ Tv T (u : G) ⊓ Q T L ∧
                  (u : G)*w ∈ (center (P : Subgroup G)).map (P : Subgroup G).subtype ∧
                  (u : G)*w ∈ Tv T (u : G) ⊓ Q T L ∧
                  (u : G)*w ≠ 1 ∧ ((u : G)*w)^2 = 1 ∧
                  TwoCentral ((u : G)*w) ∧ ¬ TwoCentral (u : G) ∧ ¬ TwoCentral w ∧
                  Gv ((u : G)*w) ∈ Chapter1.He G ∧
                  Gv (u : G) ⊓ Gv ((u : G)*w) ∈ Chapter1.He G ∧
                  w ∉ centralizer (C : Set G) ∧
                  (u : G)*w ∉ centralizer (C : Set G) ∧
                  (u : G)*w ∉ (center C).map C.subtype := by
  obtain ⟨hz,hcard,u,hu,he,hs,hi,hlt,hnot,hcentral,hline,huV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,hidx,hAn,hmodel⟩ :=
    H.exists_preferred_nonsingular_hs_generated_pair D hTV hTI v hv he
  refine ⟨hz,hcard,u,hu,he,hs,hi,hlt,hnot,hcentral,hline,huV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,?_⟩
  intro e
  obtain ⟨_,_,_,hRimage,_,hgenC,_,s,hsC,hsT,hVne,hWne,hinter,_⟩ := hmodel e
  exact ⟨hRimage,hgenC,s,hsC,hsT,hVne,hWne,hinter,
    H.nonsingular_hs_ambient_central_pair D u hu hK hTV hnot hi e S hTS⟩

end CFSG.Quasithin.Chapter12.Section06
