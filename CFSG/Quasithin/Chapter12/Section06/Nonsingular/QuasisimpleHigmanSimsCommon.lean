module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHigmanSimsCentralizer
public import Theory.GroupAction.InnerCentralizerCardinality

/-!
# The ambient common centralizer in the surviving HS configuration

Keep the original nonsingular point v, selected Sylow S, conjugate w,
and two-central product z=vw. The full common centralizer
B=C_G(v) intersect C_G(z)=C_G(v) intersect C_G(w) has order indivisible
by nine. Indeed its original action on HS centralizes the inner action
of z. That automorphism centralizer has order dividing the native
involution-centralizer order times |Out(HS)|, and the original action
kernel has order prime to three by the local A6 three-rank bound.

The same ambient Sylow P normalizes B and the original S is Sylow in B.
The same t exchanges the two full component centralizers in B; both
are relatively normal there. This supplies the ambient common group
for comparing K_v with K_w, with neither central covering kernel removed.
The preferred-point application retains V, Q, R, both conjugators and
the literal HS quotient map.

These restrictions do not yet exclude the surviving HS configuration.
The ambient contradiction, J4 exclusion and remaining source discharge
through 12.6.2 and 12.6.23 stay with this branch.

Source: Aschbacher--Smith, 12.6.4--5 and the inspection in 12.6.12,
printed pp.824--826; the HS centralizer and outer-order inputs retain
their native ATLAS and GLS3 Table 5.3m attribution.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The whole common centralizer has order indivisible by nine, including
the kernel of the original action on the full component. -/
theorem SourceHypothesis.nonsingular_hs_common_centralizer_nine_free
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (z : G) (hz : z ∈ (center ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype)).map ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype).subtype)
    (hz2 : z ^ 2 = 1) (hznot : z ∉ centralizer (Kv (v : G) : Set G)) :
    ¬ 9 ∣ Nat.card (Gv (v : G) ⊓ Gv z : Subgroup G) := by
  let := hK
  let C := Kv (v : G)
  let A := Gv (v : G)
  let B := (Gv z).subgroupOf A
  let a := nonsingularModelAction (v : G) e
  obtain ⟨j,hj,hjc,hja,_,himage,_,_,_,h9,_,_⟩ :=
    H.nonsingular_hs_selected_centralizer_image D v hv hK e S z hz hz2 hznot
  have hzA : z ∈ A := map_subtype_le _ (map_subtype_le _ hz)
  have himage_le : B.map a ≤ centralizer ({MulAut.conj j} : Set (MulAut Sporadic.LeechRelated.HS.Carrier)) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [←hja hzA,mem_centralizer_singleton_iff,←map_mul,←map_mul]
    exact congrArg a (Subtype.ext (mem_centralizer_singleton_iff.mp hx))
  have h9j : ¬ 9 ∣ Nat.card (centralizer ({j} : Set Sporadic.LeechRelated.HS.Carrier)) := by
    rwa [himage] at h9
  have h9aut : ¬ 9 ∣ Nat.card (centralizer ({MulAut.conj j} : Set (MulAut Sporadic.LeechRelated.HS.Carrier))) := by
    intro hd
    have hh := hd.trans (MulAut.centralizer_conj_card_dvd
      Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot j)
    have hc : Nat.Coprime 9 (Nat.card (MulAut.Outer Sporadic.LeechRelated.HS.Carrier)) :=
      (by decide : Nat.Coprime 9 2).of_dvd_right Sporadic.LeechRelated.HS.outer_card_dvd_two
    exact h9j (hc.dvd_mul_right.mp hh)
  have hker : Nat.Coprime 3 (Nat.card a.ker) := by
    have hLC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L _
      (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
    have hle : a.ker.map A.subtype ≤ A ⊓ coreQuotientCentralizer (Lv L (v : G)) := by
      rintro _ ⟨x,hx,rfl⟩
      rw [nonsingularModelAction_ker] at hx
      have hc : (x:G) ∈ centralizer (Lv L (v : G) : Set G) := centralizer_le hLC hx
      refine ⟨x.property,(mem_coreQuotientCentralizer_iff _ _).mpr
        ⟨Subgroup.centralizer_le_normalizer _ hc,?_⟩⟩
      intro y hy
      have hh : ⁅(x:G),y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hc y hy).symm
      change ⁅(x:G),y⁆ ∈ _
      rw [hh]
      exact one_mem _
    have hh := (H.nonsingular_quotient_centralizer_three_free D v hv).of_dvd_right
      (card_dvd_of_le hle)
    rwa [card_map_of_injective A.subtype_injective] at hh
  have h9B : ¬ 9 ∣ Nat.card B := by
    intro hd
    have hcard := IsElementaryAbelian.card_inf_ker_mul_card_map B a
    rw [←hcard] at hd
    have hc : Nat.Coprime 9 (Nat.card (B ⊓ a.ker : Subgroup A)) := by
      exact (hker.of_dvd_right (card_dvd_of_le inf_le_right)).pow_left 2
    exact h9aut ((hc.dvd_mul_left.mp hd).trans (card_dvd_of_le himage_le))
  have he : Nat.card B = Nat.card (A ⊓ Gv z : Subgroup G) := by
    rw [show B = (A ⊓ Gv z).subgroupOf A from (inf_subgroupOf_left _ _).symm]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rwa [he] at h9B

omit [Finite G] in
private theorem point_pair_centralizer (v w : G) :
    Gv v ⊓ Gv (v*w) = Gv v ⊓ Gv w := by
  ext x
  change (x ∈ Gv v ∧ x ∈ Gv (v*w)) ↔ (x ∈ Gv v ∧ x ∈ Gv w)
  apply and_congr_right
  intro hx
  simp only [Gv,mem_centralizer_singleton_iff] at hx ⊢
  rw [←mul_assoc x v w,hx,mul_assoc,mul_assoc,mul_left_cancel_iff]

private theorem common_centralizer_pair_geometry
    (v w t : G) (S₀ : Subgroup G) (P : Sylow 2 G)
    (hS : Chapter1.IsSylowIn 2 S₀ (Gv v))
    (hSP : S₀ ≤ (P : Subgroup G)) (hi : S₀.relIndex (P : Subgroup G) = 2)
    (ht : t ∈ (P : Subgroup G)) (htS : t ∉ S₀)
    (hw : (MulAut.conj t) v = w) (hswap : (MulAut.conj t) w = v)
    (hvw : Commute v w) (hSW : S₀ ≤ Gv w) :
    let B := Gv v ⊓ Gv (v*w)
    B = Gv v ⊓ Gv w ∧ Chapter1.IsSylowIn 2 S₀ B ∧
      (P : Subgroup G) ≤ normalizer (B : Set G) ∧
      (Kv v ⊓ Gv (v*w)).map (MulAut.conj t).toMonoidHom =
        Kv w ⊓ Gv (v*w) ∧
      ((Kv v ⊓ Gv (v*w)).subgroupOf B).Normal ∧
      ((Kv w ⊓ Gv (v*w)).subgroupOf B).Normal := by
  let B := Gv v ⊓ Gv (v*w)
  have hSV : S₀ ≤ Gv v := by obtain ⟨S,rfl⟩ := hS; exact map_subtype_le _
  have hB := point_pair_centralizer v w
  have hn : (P : Subgroup G) ≤ normalizer (B : Set G) := by
    have h := le_normalizer_inf_and_commutator_conjugate_of_relIndex_two
      (Gv v) S₀ (P : Subgroup G) hSP hi (hSV.trans (Gv v).le_normalizer) t ht htS
    have hm : (Gv v).map (MulAut.conj t).toMonoidHom = Gv w := by
      rw [Gv,map_pointCentralizer,hw]
      rfl
    rw [hm] at h
    change (P : Subgroup G) ≤ normalizer ((Gv v ⊓ Gv (v*w) : Subgroup G) : Set G)
    rw [hB]
    exact h.trans inf_le_left
  have htz : (MulAut.conj t) (v*w) = v*w := by
    rw [map_mul,hw,hswap]
    exact hvw.eq.symm
  have hconj : (Kv v ⊓ Gv (v*w)).map (MulAut.conj t).toMonoidHom = Kv w ⊓ Gv (v*w) := by
    rw [map_inf _ _ _ (MulAut.conj t).injective,Kv_map_conjugation,hw,
      Gv,map_pointCentralizer,htz]
  have hnormv : ((Kv v ⊓ Gv (v*w)).subgroupOf B).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    exact (le_inf (inf_le_left.trans
      ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv v)).mp (Kv_normalIn_Gv v)))
      (inf_le_right.trans (Gv (v*w)).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hnormw : ((Kv w ⊓ Gv (v*w)).subgroupOf B).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    exact (le_inf ((hB.symm ▸ (inf_le_right : Gv v ⊓ Gv w ≤ Gv w)).trans
      ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv w)).mp (Kv_normalIn_Gv w)))
      (inf_le_right.trans (Gv (v*w)).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  exact ⟨hB,hS.restrict (hB.symm ▸ le_inf hSV hSW) inf_le_left,hn,hconj,hnormv,hnormw⟩

/-- The original preferred point and both conjugators give one ambient
common centralizer, with its Sylow, order bound and both normal intersections. -/
theorem SourceHypothesis.exists_preferred_nonsingular_hs_common_centralizer
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
                  (u : G)*w ∉ (center C).map C.subtype ∧
                  ∃ j : Sporadic.LeechRelated.HS.Carrier,
                    orderOf j = 2 ∧ TwoCentral j ∧
                    (∀ hzG : (u : G)*w ∈ Gv (u : G),
                      nonsingularModelAction (u : G) e ⟨(u : G)*w,hzG⟩ = MulAut.conj j) ∧
                    (∃ k : C, ∀ x : C,
                      ((u : G)*w)*(x:G)*((u : G)*w)⁻¹ = (k:G)*(x:G)*(k:G)⁻¹) ∧
                    (Gv w).subgroupOf C = (Gv ((u : G)*w)).subgroupOf C ∧
                    ((Gv ((u : G)*w)).subgroupOf C).map f =
                      centralizer ({j} : Set Sporadic.LeechRelated.HS.Carrier) ∧
                    (centralizer ({j} : Set Sporadic.LeechRelated.HS.Carrier)).comap f =
                      (Gv ((u : G)*w)).subgroupOf C ∧
                    IsCoatom (centralizer ({j} : Set Sporadic.LeechRelated.HS.Carrier)) ∧
                    IsCoatom ((Gv ((u : G)*w)).subgroupOf C) ∧
                    ¬ 9 ∣ Nat.card (((Gv ((u : G)*w)).subgroupOf C).map f) ∧
                    ¬ 9 ∣ Nat.card ((Gv ((u : G)*w)).subgroupOf C) ∧
                    ¬ Lv L (u : G) ≤ Gv ((u : G)*w) ∧
                    let B₀ := Gv (u : G) ⊓ Gv ((u : G)*w)
                    B₀ = Gv (u : G) ⊓ Gv w ∧
                    ¬ 9 ∣ Nat.card B₀ ∧ Chapter1.IsSylowIn 2 S₀ B₀ ∧
                    (P : Subgroup G) ≤ normalizer (B₀ : Set G) ∧
                    (C ⊓ Gv ((u : G)*w)).map (MulAut.conj t).toMonoidHom =
                      Kv w ⊓ Gv ((u : G)*w) ∧
                    ((C ⊓ Gv ((u : G)*w)).subgroupOf B₀).Normal ∧
                    ((Kv w ⊓ Gv ((u : G)*w)).subgroupOf B₀).Normal := by
  obtain ⟨hz,hcard,u,hu,he,hs,hi,hlt,hnot,hcentral,hline,huV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,hmodel⟩ :=
    H.exists_preferred_nonsingular_hs_centralizer_pair D hTV hTI v hv he
  refine ⟨hz,hcard,u,hu,he,hs,hi,hlt,hnot,hcentral,hline,huV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,?_⟩
  intro e
  obtain ⟨hRimage,hgen,s,hsC,hsT,hVne,hWne,hinter,
    P,hSP,hidx,hn,hPC,t,ht,htS,hwne,hswap,hwS,hwQ,hzP,hzQ,hz1,hz2,
    hzc,hunc,hwnc,hzHe,hcommon,hwnot,hznot,hzZnot,
    j,hj,hjc,hja,hinner,heq,himage,hfull,hmax,hmaxC,h9,h9C,hmove⟩ := hmodel e
  let S₀ := (S : Subgroup (Gv (u : G))).map (Gv (u : G)).subtype
  let w := (MulAut.conj t) (u : G)
  let z := (u : G)*w
  have hzS : z ∈ (center S₀).map S₀.subtype := by
    rw [map_center_subtype_eq_inf_centralizer]
    exact ⟨hTS hzQ.1,centralizer_le hSP
      ((map_center_subtype_eq_inf_centralizer (P : Subgroup G) ▸ hzP).2)⟩
  have hSW : S₀ ≤ Gv w := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((map_center_subtype_eq_inf_centralizer S₀ ▸ hwS).2 x hx)
  have huS : (u : G) ∈ S₀ :=
    hTS ⟨H.chosen.le_sylow u.property,V_le_Gv u u.property⟩
  have huw : Commute (u : G) w := mem_centralizer_singleton_iff.mp (hSW huS)
  obtain ⟨hB,hSyl,hPN,hconj,hNv,hNw⟩ := common_centralizer_pair_geometry
    (u : G) w t S₀ P ⟨S,rfl⟩ hSP hidx ht htS rfl hswap huw hSW
  have h9B := H.nonsingular_hs_common_centralizer_nine_free D u hu hK e S z hzS hz2 hznot
  exact ⟨hRimage,hgen,s,hsC,hsT,hVne,hWne,hinter,
    P,hSP,hidx,hn,hPC,t,ht,htS,hwne,hswap,hwS,hwQ,hzP,hzQ,hz1,hz2,
    hzc,hunc,hwnc,hzHe,hcommon,hwnot,hznot,hzZnot,
    j,hj,hjc,hja,hinner,heq,himage,hfull,hmax,hmaxC,h9,h9C,hmove,
    hB,h9B,hSyl,hPN,hconj,hNv,hNw⟩

end CFSG.Quasithin.Chapter12.Section06
