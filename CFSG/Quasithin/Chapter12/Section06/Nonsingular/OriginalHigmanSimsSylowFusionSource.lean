module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsSylowFusion
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsSingularComponentsLocal

/-!
# Original-source alignment of the actual common HS residual

Select the genuine returned pair and its full ambient Sylow subgroup from
an escaping nonsingular centralizer. The same conjugator inside the original
singular centralizer sends that Sylow to T, places both transported pair
points in the original Q, and transports the literal common residual into
both transported point components, normalized by T. Its original local-family
placement and alternating-five core quotient are retained.

Source: the common paired configuration in Aschbacher--Smith 12.6.12,
printed pp.825--826, with no additional local hypotheses.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original escaping point produces an actual pair, common residual and
single Sylow alignment, retaining the full original ambient constructions. -/
theorem SourceHypothesis.exists_original_hs_sylow_aligned_pair
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ hZ : ZV L V = ⊥, ∃ u w : V,
      D.Nonsingular u ∧ D.Nonsingular w ∧ u ≠ w ∧
      ∃ P : Sylow 2 G, ∃ t ∈ (P : Subgroup G),
        MulAut.conj t (u:G) = (w:G) ∧ MulAut.conj t (w:G) = (u:G) ∧
        let z := u*w
        z ≠ 1 ∧ ¬ D.Nonsingular z ∧
        (T : Subgroup G) ≤ Gv (z:G) ∧ (P : Subgroup G) ≤ Gv (z:G) ∧
        V ≤ (P : Subgroup G) ∧ ¬ Gv (z:G) ≤ M L ∧
        (D.fullSetup hZ T z).Gz ∈ (D.fullSetup hZ T z).Hz ∧
        IsQuasisimple (Kv (u:G)) ∧
        Nonempty (((Kv (u:G)) ⧸ center (Kv (u:G))) ≃* Sporadic.LeechRelated.HS.Carrier) ∧
        let B := Gv (u:G) ⊓ Gv (z:G)
        let J := (primeToResidual 3 B).map B.subtype
        J ≤ Kv (u:G) ⊓ Kv (w:G) ∧
        (P : Subgroup G) ≤ normalizer (J : Set G) ∧
        J ∈ Chapter1.LIn (Gv (z:G)) (P : Subgroup G) ∧
        Group.IsPerfect J ∧ Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∧
        ∃ c : Gv (z:G),
          let a := MulAut.conj (c:G)
          let Jc := J.map a.toMonoidHom
          (P : Subgroup G).map a.toMonoidHom = (T : Subgroup G) ∧
          V.map a.toMonoidHom ≤ (T : Subgroup G) ∧
          a (u:G) ∈ Q T L ∧ a (w:G) ∈ Q T L ∧
          a (u:G)*a (w:G) = (z:G) ∧
          (T : Subgroup G) ≤ normalizer (Jc : Set G) ∧
          Jc ≤ Kv (a (u:G)) ⊓ Kv (a (w:G)) := by
  obtain ⟨hZ,_,u,hu,_,hs,hi,_,hnot,_,_,_,hK,hmodels,
    S,hTS,_,_,_,hmodel⟩ :=
    H.exists_preferred_nonsingular_hs_common_residual D hTV hTI v hv he
  change (∃ hp : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier,
    letI := hp
    ∃ (e : ((Kv (u : G)) ⧸ center (Kv (u : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
      (f : Kv (u : G) ≃* Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover),
      ∀ x, Theory.SpecificGroups.J2HSMultipliers.HS.projection (f x) =
        e (QuotientGroup.mk' (center (Kv (u : G))) x)) ∨
    Nonempty (((Kv (u : G)) ⧸ center (Kv (u : G))) ≃* Janko4.Model) at hmodels
  rcases hmodels with ⟨hp,e,f,hf⟩ | ⟨e⟩
  · let := hp
    obtain ⟨_,_,s,hsS,hsT,_,_,_,
      P,hSP,hidx,_,_,t,ht,htS,hwne,hswap,hwS,hwQ,hzP,hzQ,hz1,hz2,
      hzc,_,hwnc,_,_,_,hznot,_,
      j,_,_,_,_,_,_,_,_,_,_,_,_,
      _,_,_,_,_,_,_,_,_,hJC,hPJ,hJt⟩ := hmodel e
    let S₀ := (S : Subgroup (Gv (u : G))).map (Gv (u : G)).subtype
    let w := (MulAut.conj t) (u : G)
    let z := (u : G)*w
    let B := Gv (u : G) ⊓ Gv z
    let J := (primeToResidual 3 B).map B.subtype
    have hzS : z ∈ (center S₀).map S₀.subtype := by
      rw [map_center_subtype_eq_inf_centralizer] at hzP ⊢
      exact ⟨hTS hzQ.1,fun x hx => hzP.2 x (hSP hx)⟩
    have hPz : (P : Subgroup G) ≤ Gv z := by
      rw [map_center_subtype_eq_inf_centralizer] at hzP
      exact fun x hx => mem_centralizer_singleton_iff.mpr (hzP.2 x hx)
    have hZJ := H.nonsingular_hs_center_le_common_residual D u hu hK e S z hzS hz2 hznot
    have hcenter := (H.nonsingular_hs_original_geometry D u hu hK hTV hnot e).2.2.2
    have huJ : (u : G) ∈ J := hZJ (hcenter.symm ▸ mem_zpowers (u : G))
    change J.map (MulAut.conj t).toMonoidHom = J at hJt
    have hwJ : w ∈ J := hJt ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom huJ
    have hwC : w ∈ Kv (u : G) := (hJC hwJ).1
    have hw2 : w ^ 2 = 1 := by
      change (MulAut.conj t) (u : G) ^ 2 = 1
      rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian (u : G) u.property,map_one]
    have hwW := H.nonsingular_hs_core_involution_mem_moved D u hu hK e w hwC hwQ.2 hw2
    let wV : V := ⟨w,Vv_le_V H.chosen.normalizes _ hwW⟩
    have hw1 : wV ≠ 1 := by
      intro hh
      apply nonsingular_ne_one D hu
      apply Subtype.ext
      exact (MulAut.conj t).injective
        ((congrArg Subtype.val hh).trans (MulAut.conj t).map_one.symm)
    have hw : D.Nonsingular wV := by
      by_contra hh
      exact hwnc ((H.fixed_free_twoCentral_iff_singular D hTV hTI hZ wV hw1).mpr hh)
    have hfix : Tv T (u : G) ≤ Gv w := by
      rw [map_center_subtype_eq_inf_centralizer] at hwS
      exact fun x hx => mem_centralizer_singleton_iff.mpr (hwS.2 x (hTS hx))
    have hTz := H.original_nonsingular_pair_product_sylow_fixed D hTV hTI hZ
      u wV hu hw (fun hh => hwne (congrArg Subtype.val hh).symm) hs hfix
    have hout : ¬ Gv z ≤ M L := by
      intro hh
      have hSM : S₀ ≤ Mv L (u : G) :=
        le_inf (hSP.trans (hPz.trans hh)) (map_subtype_le _)
      have hSle : S₀ ≤ Tv T (u : G) :=
        ((Chapter1.isSylowIn_iff.mp hs).2.2 S₀ (S.isPGroup'.map _) hTS hSM).le
      exact hsT (hSle hsS.1)
    let zV : V := u*wV
    have hzV1 : zV ≠ 1 := fun hh => hz1 (congrArg Subtype.val hh)
    have hsing : ¬ D.Nonsingular zV :=
      (H.fixed_free_twoCentral_iff_singular D hTV hTI hZ zV hzV1).mp hzc
    have hHz : (D.fullSetup hZ T zV).Gz ∈ (D.fullSetup hZ T zV).Hz := by
      let E := D.fullSetup hZ T zV
      apply E.Gz_mem_Hz hzV1
      · change (T : Subgroup G) ≤ normalizer (zpowers (zV : G) : Set G)
        have hc : (T : Subgroup G) ≤ centralizer (zpowers (zV : G) : Set G) := by
          rw [zpowers_eq_closure,centralizer_closure]
          exact hTz
        exact hc.trans (Subgroup.centralizer_le_normalizer _)
      · rw [E.Gz_eq]
        exact hout
    have hlocal := H.nonsingular_hs_common_residual_mem_local_family D u hu hK hTV hnot
      e S z hzS hz2 hznot P hPz hPJ
    have hquot := H.nonsingular_hs_common_residual_perfect_quotient D u hu hK e S z hzS hz2 hznot
    have hVP : V ≤ (P : Subgroup G) :=
      (le_inf H.chosen.le_sylow (V_le_Gv u)).trans (hTS.trans hSP)
    have huS : (u:G) ∈ centralizer (S₀ : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mp (map_subtype_le _ hx)
    have hwCen : (wV:G) ∈ centralizer (S₀ : Set G) := by
      rw [map_center_subtype_eq_inf_centralizer] at hwS
      exact hwS.2
    have huw : u ≠ wV := fun hh => hwne (congrArg Subtype.val hh).symm
    obtain ⟨c,hPT,hVc,huQ,hwQc,hprod,hn⟩ :=
      H.original_hs_pair_sylow_alignment D hZ hTV u wV hu huw hsing
        hTz P hVP hPz S₀ hidx huS hwCen t ht htS rfl
    have hJc : J.map (MulAut.conj (c:G)).toMonoidHom ≤
        Kv (MulAut.conj (c:G) (u:G)) ⊓ Kv (MulAut.conj (c:G) (wV:G)) := by
      have hh := map_mono hJC (f := (MulAut.conj (c:G)).toMonoidHom)
      rw [map_inf _ _ (MulAut.conj (c:G)).toMonoidHom
        (MulAut.conj (c:G)).injective,Kv_map_conjugation,Kv_map_conjugation] at hh
      exact hh
    exact ⟨hZ,u,wV,hu,hw,huw,P,t,ht,rfl,hswap,hzV1,hsing,hTz,hPz,hVP,
      hout,hHz,hK,⟨e⟩,hJC,hPJ,hlocal,hquot.1,hquot.2,
      c,hPT,hVc,huQ,hwQc,hprod,hn J hPJ,hJc⟩
  · obtain ⟨e⟩ := e
    exact (H.original_nonsingular_not_jankoFour D u hu hK hTV hi e).elim

end CFSG.Quasithin.Chapter12.Section06
