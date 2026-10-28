module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsPairedReturn
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsPairCoordinates
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Perpendicular

/-!
# An actual original-Sylow singular centralizer from the HS pair

Transfer returns the exchanged involution to the original moved module.
The actual marked point-Sylow fixed-plane bound puts the product in C_V(T).
Its centralizer contains the original T and escapes M, so it belongs to
exactly the original point-overgroup family used later in Section12.6.
This placement makes no nonsingular-centralizer-control assumption.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- A hypothetical escaping nonsingular centralizer produces an escaping
singular centralizer containing the unchanged original full Sylow subgroup. -/
theorem SourceHypothesis.exists_original_hs_singular_centralizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ hZ : ZV L V = ⊥, ∃ z : V, z ≠ 1 ∧ ¬ D.Nonsingular z ∧
      (T : Subgroup G) ≤ Gv (z : G) ∧ ¬ Gv (z : G) ≤ M L ∧
      Gv (z : G) ∈ Chapter1.He G ∧
      (D.fullSetup hZ T z).Gz ∈ (D.fullSetup hZ T z).Hz := by
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
      P,hSP,_,_,_,t,ht,_,hwne,_,hwS,hwQ,hzP,hzQ,hz1,hz2,
      hzc,_,hwnc,hzHe,_,hwnot,hznot,_,
      j,_,_,_,_,_,_,_,_,_,_,_,_,
      _,_,_,_,_,_,_,_,_,hJC,_,hJt⟩ := hmodel e
    let S₀ := (S : Subgroup (Gv (u : G))).map (Gv (u : G)).subtype
    let w := (MulAut.conj t) (u : G)
    let z := (u : G) * w
    let B := Gv (u : G) ⊓ Gv z
    let J := (primeToResidual 3 B).map B.subtype
    have hzS : z ∈ (center S₀).map S₀.subtype := by
      rw [map_center_subtype_eq_inf_centralizer] at hzP ⊢
      exact ⟨hTS hzQ.1,fun x hx => hzP.2 x (hSP hx)⟩
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
      intro x hx
      exact mem_centralizer_singleton_iff.mpr (hwS.2 x (hTS hx))
    have hTz := H.original_nonsingular_pair_product_sylow_fixed D hTV hTI hZ
      u wV hu hw (fun hh => hwne (congrArg Subtype.val hh).symm) hs hfix
    have hout : ¬ Gv z ≤ M L := by
      intro hh
      have hPM : (P : Subgroup G) ≤ M L := by
        intro x hx
        rw [map_center_subtype_eq_inf_centralizer] at hzP
        exact hh (mem_centralizer_singleton_iff.mpr (hzP.2 x hx))
      have hSM : S₀ ≤ Mv L (u : G) := le_inf (hSP.trans hPM) (map_subtype_le _)
      have hSle : S₀ ≤ Tv T (u : G) :=
        ((Chapter1.isSylowIn_iff.mp hs).2.2 S₀ (S.isPGroup'.map _) hTS hSM).le
      exact hsT (hSle hsS.1)
    let zV : V := u*wV
    have hzV1 : zV ≠ 1 := fun hh => hz1 (congrArg Subtype.val hh)
    have hsing : ¬ D.Nonsingular zV :=
      (H.fixed_free_twoCentral_iff_singular D hTV hTI hZ zV hzV1).mp hzc
    refine ⟨hZ,zV,hzV1,hsing,hTz,hout,hzHe,?_⟩
    let E := D.fullSetup hZ T zV
    apply E.Gz_mem_Hz hzV1
    · change (T : Subgroup G) ≤ normalizer (zpowers (zV : G) : Set G)
      have hc : (T : Subgroup G) ≤ centralizer (zpowers (zV : G) : Set G) := by
        rw [zpowers_eq_closure,centralizer_closure]
        exact hTz
      exact hc.trans (Subgroup.centralizer_le_normalizer _)
    · rw [E.Gz_eq]
      exact hout
  · obtain ⟨e⟩ := e
    exact (H.original_nonsingular_not_jankoFour D u hu hK hTV hi e).elim


end CFSG.Quasithin.Chapter12.Section06
