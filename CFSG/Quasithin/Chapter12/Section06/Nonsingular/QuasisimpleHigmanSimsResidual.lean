module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleHigmanSimsCommon
public import Theory.GroupTheory.IndexCoprimeAction
public import Theory.GroupTheory.PResidual.PrimeToIntersection

/-!
# The common prime-to-three residual of the original HS pair

The full point-centralizer action has kernel of order prime to three.
The original K_v maps onto Inn(HS), whose index divides two. The index
calculation, retaining that kernel, identifies K_v with O^{3'}(G_v).
Normal intersection then gives
O^{3'}(K_v intersect G_z) = O^{3'}(G_v intersect G_z).

The same ambient Sylow P normalizes the common centralizer B. Hence it
normalizes J=O^{3'}(B). The original conjugator t exchanges the two
component intersections, so both have exactly this embedded residual J.
In particular J lies in both full original components K_v and K_w.
The preferred-point application preserves V, Q, R, S, both conjugators,
and the literal central quotient map, and supplies every local premise.

This establishes an actual common subgroup; it does not identify its
center or exclude the HS configuration. The ambient HS contradiction,
J4 exclusion and remaining source discharge through 12.6.2 and 12.6.23
remain with this branch.

Source: Aschbacher--Smith 12.6.3--5 and the inspection in 12.6.12,
printed pp.824--826. The imported native HS outer-order input retains
its ATLAS and GLS3 Table 5.3m attribution.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The full original point centralizer has K_v as its prime-to-three residual. -/
theorem SourceHypothesis.nonsingular_hs_point_primeToResidual
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Nat.Coprime 3 ((Kv (v : G)).relIndex (Gv (v : G))) ∧
      (primeToResidual 3 (Gv (v : G))).map (Gv (v : G)).subtype = Kv (v : G) := by
  let := hK
  let C := Kv (v : G)
  let A := Gv (v : G)
  let N := C.subgroupOf A
  let a := nonsingularModelAction (v : G) e
  let : N.Normal := Kv_normalIn_Gv (v : G)
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
  have himage : N.map a = MulAut.innerSubgroup Sporadic.LeechRelated.HS.Carrier := by
    rw [show N = C.subgroupOf A from rfl,nonsingularModelAction_map _ e C le_rfl,
      subgroupOf_self,map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      ←map_map,map_top_of_surjective _ e.surjective,←MonoidHom.range_eq_map]
  have hidx : Nat.Coprime 3 N.index := by
    apply index_coprime_of_map_index_and_kernel 3 a N hker
    rw [himage]
    exact (by decide : Nat.Coprime 3 2).of_dvd_right
      Sporadic.LeechRelated.HS.outer_card_dvd_two
  refine ⟨hidx,?_⟩
  have he := congrArg (map A.subtype)
    (embedded_primeToResidual_eq_of_normal 3 N (primeToResidual_le N hidx))
  rw [map_embedded_primeToResidual_of_hom,map_subgroupOf_eq_of_le (Kv_le_Gv (v : G)),
    Kv_primeToResidual] at he
  exact he.symm

/-- Restriction to any actual ambient intersection preserves this embedded residual. -/
theorem SourceHypothesis.nonsingular_hs_intersection_primeToResidual
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (X : Subgroup G) :
    (primeToResidual 3 (Kv (v : G) ⊓ X : Subgroup G)).map (Kv (v : G) ⊓ X).subtype =
      (primeToResidual 3 (Gv (v : G) ⊓ X : Subgroup G)).map (Gv (v : G) ⊓ X).subtype := by
  have he := embedded_primeToResidual_intersection 3 (Gv (v : G)) X
  rwa [(H.nonsingular_hs_point_primeToResidual D v hv hK e).2] at he

/-- The two original component intersections have one residual normalized by the same P. -/
theorem SourceHypothesis.nonsingular_hs_paired_common_residual
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (w z t : G) (P : Sylow 2 G) (ht : t ∈ (P : Subgroup G))
    (hn : (P : Subgroup G) ≤ normalizer ((Gv (v : G) ⊓ Gv z : Subgroup G) : Set G))
    (hconj : (Kv (v : G) ⊓ Gv z).map (MulAut.conj t).toMonoidHom = Kv w ⊓ Gv z) :
    let B := Gv (v : G) ⊓ Gv z
    let J := (primeToResidual 3 B).map B.subtype
    (primeToResidual 3 (Kv (v : G) ⊓ Gv z : Subgroup G)).map
        (Kv (v : G) ⊓ Gv z).subtype = J ∧
      (primeToResidual 3 (Kv w ⊓ Gv z : Subgroup G)).map
        (Kv w ⊓ Gv z).subtype = J ∧
      J ≤ Kv (v : G) ⊓ Kv w ∧
      (P : Subgroup G) ≤ normalizer (J : Set G) ∧
      J.map (MulAut.conj t).toMonoidHom = J := by
  let B := Gv (v : G) ⊓ Gv z
  let J := (primeToResidual 3 B).map B.subtype
  have hJv := H.nonsingular_hs_intersection_primeToResidual D v hv hK e (Gv z)
  have hPJ : (P : Subgroup G) ≤ normalizer (J : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image B (primeToResidual 3 B))
  have hJt : J.map (MulAut.conj t).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp (hPJ ht)
  have hJw : (primeToResidual 3 (Kv w ⊓ Gv z : Subgroup G)).map
      (Kv w ⊓ Gv z).subtype = J := by
    have hh := congrArg (map (MulAut.conj t).toMonoidHom) hJv
    rw [map_embedded_primeToResidual_of_hom,hconj] at hh
    exact hh.trans hJt
  exact ⟨hJv,hJw,le_inf (hJv.ge.trans ((map_subtype_le _).trans inf_le_left))
    (hJw.ge.trans ((map_subtype_le _).trans inf_le_left)),hPJ,hJt⟩

/-- The same preferred point, quotient and both conjugators have a common
prime-to-three residual inside both full components, normalized by the original P. -/
theorem SourceHypothesis.exists_preferred_nonsingular_hs_common_residual
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
                    ((Kv w ⊓ Gv ((u : G)*w)).subgroupOf B₀).Normal ∧
                    let J := (primeToResidual 3 B₀).map B₀.subtype
                    (primeToResidual 3 (C ⊓ Gv ((u : G)*w) : Subgroup G)).map
                        (C ⊓ Gv ((u : G)*w)).subtype = J ∧
                      (primeToResidual 3 (Kv w ⊓ Gv ((u : G)*w) : Subgroup G)).map
                        (Kv w ⊓ Gv ((u : G)*w)).subtype = J ∧
                      J ≤ C ⊓ Kv w ∧
                      (P : Subgroup G) ≤ normalizer (J : Set G) ∧
                      J.map (MulAut.conj t).toMonoidHom = J := by
  obtain ⟨hz,hcard,u,hu,he,hs,hi,hlt,hnot,hcentral,hline,huV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,hmodel⟩ :=
    H.exists_preferred_nonsingular_hs_common_centralizer D hTV hTI v hv he
  refine ⟨hz,hcard,u,hu,he,hs,hi,hlt,hnot,hcentral,hline,huV,hK,hmodels,
    S,hTS,hR,hcomm,hReq,?_⟩
  intro e
  obtain ⟨hRimage,hgen,s,hsC,hsT,hVne,hWne,hinter,
    P,hSP,hidx,hn,hPC,t,ht,htS,hwne,hswap,hwS,hwQ,hzP,hzQ,hz1,hz2,
    hzc,hunc,hwnc,hzHe,hcommon,hwnot,hznot,hzZnot,
    j,hj,hjc,hja,hinner,heq,himage,hfull,hmax,hmaxC,h9,h9C,hmove,
    hB,h9B,hSyl,hPN,hconj,hNv,hNw⟩ := hmodel e
  have hres := H.nonsingular_hs_paired_common_residual D u hu hK e
    ((MulAut.conj t) (u : G)) ((u : G)*((MulAut.conj t) (u : G))) t P ht hPN hconj
  exact ⟨hRimage,hgen,s,hsC,hsT,hVne,hWne,hinter,
    P,hSP,hidx,hn,hPC,t,ht,htS,hwne,hswap,hwS,hwQ,hzP,hzQ,hz1,hz2,
    hzc,hunc,hwnc,hzHe,hcommon,hwnot,hznot,hzZnot,
    j,hj,hjc,hja,hinner,heq,himage,hfull,hmax,hmaxC,h9,h9C,hmove,
    hB,h9B,hSyl,hPN,hconj,hNv,hNw,hres⟩

end CFSG.Quasithin.Chapter12.Section06
