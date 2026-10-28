module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHigmanSimsAmbient
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowFixedCentralCover

/-!
# The full component centralizer of the ambient HS pair

Keep the original selected Sylow S, preferred point v, its conjugate w,
and the two-central product z=vw. The action of z fixes the full component
Sylow pointwise and is nontrivial. It is inner on the full K_v, and the
literal image of C_{K_v}(z) is the centralizer of a two-central involution
in HS. Fixed-point lifting retains the whole covering center and proves
that C_{K_v}(z) is the full preimage, hence a maximal subgroup of K_v.

The center of K_v has order two, so nine divides neither that centralizer
nor its image. The original A6 quotient makes nine divide the order of
L_v; consequently L_v does not centralize z. Since v centralizes K_v,
the same subgroup is C_{K_v}(w).

The preferred-point application retains the original V, Q, S, R, both
conjugators and the literal quotient projection. These are further
restrictions on the surviving HS configuration. Their incompatibility
with the full ambient hypotheses, the J4 exclusion and the remaining
source discharge through 12.6.2 and 12.6.23 remain unproved.

Source: Aschbacher--Smith 12.6.4--5 and the inspection in 12.6.12,
printed pp.824--826; A.3.12(18), pp.47--48, for the native HS Sylow
overgroup restriction.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The centralizer in the full original component maps onto an actual
maximal HS involution centralizer, with its entire kernel retained. -/
theorem SourceHypothesis.nonsingular_hs_selected_centralizer_image
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (z : G) (hz : z ∈ (center ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype)).map ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype).subtype)
    (hz2 : z ^ 2 = 1) (hznot : z ∉ centralizer (Kv (v : G) : Set G)) :
    let C := Kv (v : G)
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
    ∃ u : Sporadic.LeechRelated.HS.Carrier,
      orderOf u = 2 ∧ TwoCentral u ∧
      (∀ hzG : z ∈ Gv (v : G),
        nonsingularModelAction (v : G) e ⟨z,hzG⟩ = MulAut.conj u) ∧
      (∃ k : C, ∀ x : C, z*(x:G)*z⁻¹ = (k:G)*(x:G)*(k:G)⁻¹) ∧
      ((Gv z).subgroupOf C).map q = centralizer ({u} : Set Sporadic.LeechRelated.HS.Carrier) ∧
      (centralizer ({u} : Set Sporadic.LeechRelated.HS.Carrier)).comap q = (Gv z).subgroupOf C ∧
      IsCoatom (centralizer ({u} : Set Sporadic.LeechRelated.HS.Carrier)) ∧
      IsCoatom ((Gv z).subgroupOf C) ∧
      ¬ 9 ∣ Nat.card (((Gv z).subgroupOf C).map q) ∧
      ¬ 9 ∣ Nat.card ((Gv z).subgroupOf C) ∧
      ¬ Lv L (v : G) ≤ Gv z := by
  let := hK
  let C := Kv (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hz' : z ∈ S₀ ⊓ centralizer (S₀ : Set G) :=
    map_center_subtype_eq_inf_centralizer S₀ ▸ hz
  have hzG : z ∈ Gv (v : G) := map_subtype_le _ hz'.1
  let a := nonsingularCoverAction (v : G) (MulEquiv.refl C) (⟨z,hzG⟩ : Gv (v : G))
  have ha : a ^ 2 = 1 := by
    rw [←map_pow]
    have hh : (⟨z,hzG⟩ : Gv (v : G)) ^ 2 = 1 := Subtype.ext hz2
    rw [hh,map_one]
  have hane : a ≠ 1 := by
    intro hh
    apply hznot
    have hm : (⟨z,hzG⟩ : Gv (v : G)) ∈
        (nonsingularCoverAction (v : G) (MulEquiv.refl C)).ker := hh
    rw [nonsingularCoverAction_ker] at hm
    exact hm
  have hSyl : Chapter1.IsSylowIn 2 S₀ (Gv (v : G)) := ⟨S,rfl⟩
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (Kv_le_Gv (v : G)) (Kv_normalIn_Gv (v : G)).isSubnormal
  have hfix : ∀ x ∈ P, a x = x := by
    intro x hx
    apply Subtype.ext
    change z*(x:G)*z⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr
      (hz'.2 x (hP ▸ mem_map_of_mem C.subtype hx).1).symm
  obtain ⟨u,hu,huc,hmodel,hinner,himage,hfull,hmax,hmaxC,h9⟩ :=
    Sporadic.LeechRelated.HS.sylow_fixed_central_cover e P a ha hane hfix
  have hfixed : a.fixedSubgroup = (Gv z).subgroupOf C := by
    ext x
    rw [MulAut.mem_fixedSubgroup]
    change a x = x ↔ (x:G) ∈ centralizer ({z} : Set G)
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hh
      have hv := congrArg Subtype.val hh
      change z*(x:G)*z⁻¹ = x at hv
      exact (mul_inv_eq_iff_eq_mul.mp hv).symm
    · intro hh
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr hh.symm)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let A := (Gv z).subgroupOf C
  have hfull' : (centralizer ({u} : Set Sporadic.LeechRelated.HS.Carrier)).comap q = A :=
    hfull.trans hfixed
  have hk : q.ker = center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hZA : center C ≤ A := by
    rw [←hfull']
    intro x hx
    change q x ∈ centralizer ({u} : Set Sporadic.LeechRelated.HS.Carrier)
    rw [show q x = 1 from (show x ∈ q.ker from hk.symm ▸ hx)]
    exact one_mem _
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map A q
  rw [hk,inf_eq_right.mpr hZA,H.nonsingular_hs_ru_center_card D v hv hK (.inl ⟨e⟩)] at hc
  have h9A : ¬ 9 ∣ Nat.card A := by
    intro hd
    rw [←hc] at hd
    exact (hfixed ▸ h9) ((by decide : Nat.Coprime 9 2).dvd_mul_left.mp hd)
  have hLnot : ¬ Lv L (v : G) ≤ Gv z := by
    intro hl
    have hLC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L _
      (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
    have h9L : 9 ∣ Nat.card (Lv L (v : G)) := by
      obtain ⟨f⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
      apply dvd_trans _ (card_quotient_dvd_card (pCore 2 _))
      rw [Nat.card_congr f.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      decide
    have h9B : 9 ∣ Nat.card ((Lv L (v : G)).subgroupOf C) := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hLC).toEquiv]
    exact h9A (h9B.trans (card_dvd_of_le (comap_mono hl)))
  refine ⟨u,hu,huc,?_,?_,hfixed ▸ himage,hfull',hmax,hfixed ▸ hmaxC,hfixed ▸ h9,h9A,hLnot⟩
  · intro _
    exact hmodel
  · obtain ⟨k,hk⟩ := hinner
    refine ⟨k,fun x => ?_⟩
    exact congrArg Subtype.val (congrArg (fun b : MulAut C => b x) hk)

/-- At the original preferred point, retain the selected S, R, full quotient
map and component conjugator and identify the full component centralizer of the ambient central pair. -/
theorem SourceHypothesis.exists_preferred_nonsingular_hs_centralizer_pair
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
                    ¬ Lv L (u : G) ≤ Gv ((u : G)*w) := by
  obtain ⟨hz,hcard,u,hu,he,hs,hi,hlt,hnot,hcentral,hline,huV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,hmodel⟩ :=
    H.exists_preferred_nonsingular_hs_ambient_pair D hTV hTI v hv he
  refine ⟨hz,hcard,u,hu,he,hs,hi,hlt,hnot,hcentral,hline,huV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,?_⟩
  intro e
  obtain ⟨hRimage,hgen,s,hsC,hsT,hVne,hWne,hinter,
    P,hSP,hidx,hn,hPC,t,ht,htS,hwne,hswap,hwS,hwQ,hzP,hzQ,hz1,hz2,
    hzc,hunc,hwnc,hzHe,hcommon,hwnot,hznot,hzZnot⟩ := hmodel e
  let S₀ := (S : Subgroup (Gv (u : G))).map (Gv (u : G)).subtype
  let w := (MulAut.conj t) (u : G)
  let z := (u : G)*w
  have hzS : z ∈ (center S₀).map S₀.subtype := by
    rw [map_center_subtype_eq_inf_centralizer]
    exact ⟨hTS hzQ.1,centralizer_le hSP
      ((map_center_subtype_eq_inf_centralizer (P : Subgroup G) ▸ hzP).2)⟩
  obtain ⟨j,hj,hjc,hja,hinner,himage,hfull,hmax,hmaxC,h9,h9C,hmove⟩ :=
    H.nonsingular_hs_selected_centralizer_image D u hu hK e S z hzS hz2 hznot
  have heq : (Gv w).subgroupOf (Kv (u : G)) = (Gv z).subgroupOf (Kv (u : G)) := by
    ext x
    change (x:G) ∈ centralizer ({w} : Set G) ↔ (x:G) ∈ centralizer ({z} : Set G)
    simp only [mem_centralizer_singleton_iff]
    have hxu := mem_centralizer_singleton_iff.mp (Kv_le_Gv (u : G) x.property)
    change (x:G)*w = w*(x:G) ↔ (x:G)*((u:G)*w) = ((u:G)*w)*(x:G)
    rw [←mul_assoc (x:G) (u:G) w,hxu,mul_assoc,mul_assoc,mul_left_cancel_iff]
  exact ⟨hRimage,hgen,s,hsC,hsT,hVne,hWne,hinter,
    P,hSP,hidx,hn,hPC,t,ht,htS,hwne,hswap,hwS,hwQ,hzP,hzQ,hz1,hz2,
    hzc,hunc,hwnc,hzHe,hcommon,hwnot,hznot,hzZnot,
    j,hj,hjc,hja,hinner,heq,himage,hfull,hmax,hmaxC,h9,h9C,hmove⟩

end CFSG.Quasithin.Chapter12.Section06
