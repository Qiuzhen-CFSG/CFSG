module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalSelectedFive
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsFiveShortlist
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsResidualOuterSource
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsSelectedOuter
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsSelectedRows
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentAlternating
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentSevenFour

/-!
# Original nonsingular centralizers lie in the chosen maximal local subgroup

A hypothetical escape produces the original paired HS configuration after
the J4 source exclusion. Its literal common residual becomes A5 in the full
singular quotient and lies in the same selected ordinary normal component.
The actual full-Sylow local-A5 shortlist leaves five possibilities. The
original component action excludes A7, its triple cover, J1 and PSL2(25).
The original moved hyperplane acts outer on the literal A5, whereas the
same Sylow-fixed action must restrict inner in the equality and prime rows.

All kernels, original points, Sylows and module actions are retained. No
nonsingular-control, natural-module, or assumed movement premise is used.
Source: Aschbacher--Smith Section12.6, original HS contrary branch.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Original nonsingular centralizer control from the actual chosen
orthogonal module, its Sylow invariance, and its original TI geometry. -/
theorem SourceHypothesis.original_nonsingular_centralizer_le_of_ti
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) : Gv (v : G) ≤ M L := by
  classical
  by_contra he
  obtain ⟨hZ,u,w,hu,_,_,P,t,_,_,_,hz,hsz,hTz,hPz,_,hHz,
    hKu,_,⟨e⟩,S,hzS,hzc,_,_,_,_,_,_,⟨eJ⟩,hlocal,hPJ,hn,
    c,hJK,_,_,_,_,_,⟨a⟩⟩ :=
    H.exists_original_hs_selected_local_five D hTV hTI v hv he
  let z : V := u*w
  let X := Gv (z : G)
  let E := D.fullSetup hZ T z
  let B := Gv (u : G) ⊓ X
  let J := (primeToResidual 3 B).map B.subtype
  have hnz : (T : Subgroup G) ≤ normalizer (E.V₁ : Set G) := by
    apply hTz.trans
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rw [Nonabelian.Setup.V₁,zpowers_eq_closure,centralizer_closure]
    rfl
  have hbound := H.original_hs_conjugate_intersection_bound D hTV hTI v hv he
  obtain ⟨_,hpolar⟩ := H.original_hs_singular_perpendicular_core D hTV hTI v hv he
  obtain ⟨x,hx,hnJ,hoJ⟩ := H.nonsingular_hs_outer_on_common_star
    D hZ u hu hKu e S z hz hzS hzc (hpolar z hz hsz)
  have hxV : (x : G) ∈ V := Vv_le_V H.chosen.normalizes _ hx
  let Pstar := (P.subtype hPz).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hnorm : (Pstar : Subgroup (X ⧸ pCore 2 X)) ≤
      normalizer (Nonabelian.Setup.star X J : Set (X ⧸ pCore 2 X)) := hPJ
  have hJKstar : Nonabelian.Setup.star X J ≤ Nonabelian.Setup.star X c.K :=
    map_mono (comap_mono hJK)
  have hcases := OriginalHigmanSimsFiveShortlist.five_or_shortlist
    (H.original_star_sqtk D hZ z hz hHz) (pCore_quotient_pCore_eq_bot 2)
    Pstar hlocal c.component hJKstar hnorm eJ
  rcases hcases with hfive | hseven | hcover | hjanko | htwentyfive | ⟨p,hp,hprime⟩
  · exact H.original_hs_selected_not_alternatingFive_of_outer D hZ z hz hTV hnz hbound
      hHz hn c a J hJK eJ x hxV hnJ hoJ hfive
  · exact H.original_selectedComponent_not_alternatingSevenEight D hZ z hz hTV hnz hbound
      hHz hn c a (.inl rfl) hseven
  · exact H.original_not_alternatingSevenCover D hZ z hz hTV hnz hbound hHz hn c a hcover
  · exact H.original_hs_selected_not_jankoOne D hZ z hz hTV hnz hbound hHz hn c a hjanko
  · exact H.original_hs_selected_not_linearTwoTwentyFive D hZ z hz hTV hnz hbound hHz hn c a htwentyfive
  · obtain ⟨hp,hop,hmod,_⟩ := hp
    have hl : 3 < p := by
      by_contra hsmall
      have hp2 := hp.two_le
      have hcases : p = 2 ∨ p = 3 := by omega
      rcases hcases with rfl | rfl
      · norm_num at hop
      · norm_num at hmod
    exact H.original_hs_selected_not_primeLinearTwo_of_outer D hZ z hz hTV hnz hbound
      hHz hn c a J hJK eJ x hxV hnJ hoJ hp hop hl hprime

end CFSG.Quasithin.Chapter12.Section06
