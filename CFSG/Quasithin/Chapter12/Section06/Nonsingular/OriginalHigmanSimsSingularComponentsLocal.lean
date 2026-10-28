module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsSingularComponents
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsSingularSource
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.NormalizedPerfect

/-!
# Actual Sylow-local placement of the common HS residual

The common residual J is perfect with alternating-five two-core quotient.
The original point involution lies in its center and makes its two-core
nontrivial. Since the full ambient Sylow P normalizes J, these facts place
J in the literal local family L(G_z,P). The final source application keeps
the same u,w,z,P,t and also proves that the unchanged original T lies in
G_z. It does not promote J to a C-component of the whole G_z.

Source: Aschbacher--Smith Definition 1.2.3, printed p.505, applied to the
original paired HS configuration in the inspection for 12.6.12,
printed pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual common residual belongs to the local family inside G_z,
relative to the given full ambient Sylow subgroup which normalizes it. -/
theorem SourceHypothesis.nonsingular_hs_common_residual_mem_local_family
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ Kv (v : G) ≤ M L)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier)
    (S : Sylow 2 (Gv (v : G)))
    (z : G) (hz : z ∈ (center ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype)).map ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype).subtype)
    (hz2 : z ^ 2 = 1) (hznot : z ∉ centralizer (Kv (v : G) : Set G))
    (P : Sylow 2 G) (hPz : (P : Subgroup G) ≤ Gv z)
    (hn : (P : Subgroup G) ≤ normalizer
      (((primeToResidual 3 (Gv (v : G) ⊓ Gv z : Subgroup G)).map
        (Gv (v : G) ⊓ Gv z).subtype) : Set G)) :
    (primeToResidual 3 (Gv (v : G) ⊓ Gv z : Subgroup G)).map
      (Gv (v : G) ⊓ Gv z).subtype ∈ Chapter1.LIn (Gv z) (P : Subgroup G) := by
  let J := (primeToResidual 3 (Gv (v : G) ⊓ Gv z : Subgroup G)).map
    (Gv (v : G) ⊓ Gv z).subtype
  obtain ⟨hp,⟨d⟩⟩ := H.nonsingular_hs_common_residual_perfect_quotient D v hv hK e S z hz hz2 hznot
  let : Group.IsPerfect J := hp
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (J ⧸ pCore 2 J) := IsQuasisimple.of_mulEquiv d.symm
  have hZJ := H.nonsingular_hs_center_le_common_residual D v hv hK e S z hz hz2 hznot
  have hcenter := (H.nonsingular_hs_original_geometry D v hv hK hTV hnot e).2.2.2
  have hvJ : (v : G) ∈ J := hZJ (hcenter.symm ▸ mem_zpowers (v : G))
  have hJv : J ≤ Gv (v : G) := (map_subtype_le _).trans inf_le_left
  have hc : J ≤ centralizer (zpowers (v : G) : Set G) := by
    simpa only [Gv,zpowers_eq_closure,centralizer_closure] using hJv
  have hline : zpowers (v : G) ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).to_le (zpowers_le.mpr v.property))
    (zpowers_le.mpr hvJ) (hc.trans (Subgroup.centralizer_le_normalizer _))
  have hcore : J.pCoreIn 2 ≠ ⊥ := by
    intro hh
    have hve := hline (mem_zpowers (v : G))
    rw [hh,mem_bot] at hve
    exact nonsingular_ne_one D hv (Subtype.ext hve)
  have hSyl : Chapter1.IsSylowIn 2 (P : Subgroup G) (Gv z) :=
    Chapter1.isSylowIn_iff.mpr ⟨P.isPGroup',hPz,fun U hU hPU _ => P.is_maximal' hU hPU⟩
  exact Chapter1.mem_LIn_of_normalized_perfect hSyl
    ((map_subtype_le _).trans inf_le_right) hn hcore

/-- Original source hypotheses produce a single singular centralizer containing
both the unchanged T and the paired Sylow P, with its literal common residual
in L(G_z,P). The same P-conjugator exchanges the two nonsingular points. -/
theorem SourceHypothesis.exists_original_hs_singular_local_component
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
        (T : Subgroup G) ≤ Gv (z : G) ∧ (P : Subgroup G) ≤ Gv (z : G) ∧
        ¬ Gv (z : G) ≤ M L ∧ (D.fullSetup hZ T z).Gz ∈ (D.fullSetup hZ T z).Hz ∧
        IsQuasisimple (Kv (u : G)) ∧ ¬ Kv (u : G) ≤ M L ∧
        Nonempty (((Kv (u : G)) ⧸ center (Kv (u : G))) ≃* Sporadic.LeechRelated.HS.Carrier) ∧
        ∃ S : Sylow 2 (Gv (u : G)),
        (z : G) ∈ (center ((S : Subgroup (Gv (u : G))).map
          (Gv (u : G)).subtype)).map ((S : Subgroup (Gv (u : G))).map
          (Gv (u : G)).subtype).subtype ∧
        let B := Gv (u : G) ⊓ Gv (z : G)
        let J := (primeToResidual 3 B).map B.subtype
        J ≤ Kv (u : G) ⊓ Kv (w : G) ∧
        (P : Subgroup G) ≤ normalizer (J : Set G) ∧
        J ∈ Chapter1.LIn (Gv (z : G)) (P : Subgroup G) ∧
        Group.IsPerfect J ∧ Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) := by
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
      P,hSP,_,_,_,t,ht,_,hwne,hswap,hwS,hwQ,hzP,hzQ,hz1,hz2,
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
    exact ⟨hZ,u,wV,hu,hw,(fun hh => hwne (congrArg Subtype.val hh)),
      P,t,ht,rfl,hswap,hzV1,hsing,hTz,hPz,hout,hHz,hK,hnot,⟨e⟩,S,hzS,hJC,hPJ,hlocal,hquot⟩
  · obtain ⟨e⟩ := e
    exact (H.original_nonsingular_not_jankoFour D u hu hK hTV hi e).elim

end CFSG.Quasithin.Chapter12.Section06
