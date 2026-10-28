module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ResidualBlock

/-!
# General canonical containment at the original nonsingular point

The two branches for the ambient normalizer of R_v exhaust the selected
source arrangement. If that normalizer lies in M, its proved equality
R=R_v lets A.4.10 transfer the original V_v. Otherwise normalizer escape
makes the original L short; the actual local block and characteristic-two
core then put the same V_v in the canonical moved module.

This proves 12.6.13(3) without a fixed-space, block, R=R_v or escaping-K_v
premise. The final theorem combines it with the simple quotient and
self-centralizing core, on one and the same selected Sylow subgroup.
Nonquasisimplicity remains the explicit 12.6.12 input; its HS/J4 exclusions
and full nonsingular-centralizer and fixed-space elimination remain open.
Earlier invariance/TI retain qt-d-1222-source and final discharge retains
qt-d-12634-source.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.13, printed p.826, and A.4.10, printed p.60.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The general source containment, on the same selected Sylow subgroup. -/
theorem SourceHypothesis.nonsingular_moved_le_canonical
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (hN : Chapter1.IsSylowIn 2
      (((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) ⊓
        normalizer (Lv L (v : G) : Set G))
      (Gv (v : G) ⊓ normalizer (Lv L (v : G) : Set G)))
    (hReq : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) =
      ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) ⊓
        coreQuotientCentralizer (Lv L (v : G))) :
    Vv L V (v : G) ≤
      ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆ := by
  by_cases hn : normalizer (Rv T L (v : G) : Set G) ≤ M L
  · exact H.nonsingular_moved_le_canonical_of_R_eq D v hv hTV hnot S hN
      (H.nonsingular_R_eq_Rv_of_normalizer D v hv hs hn S hTS) hReq
  · have hshort := H.nonsingular_original_short D hTV v hv hn
    have hc := H.nonsingular_nonquasisimple_signalizer D v hv hnot
    have hSC := (map_subtype_le (S : Subgroup (Gv (v : G)))).trans
      ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv (v : G))).mp (Kv_normalIn_Gv _))
    have hFit := generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_sup_le 2 (Kv (v : G))
        ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
        (hc.2.2 ▸ centralizer_generalizedFitting_le (Kv (v : G)))
        (S.isPGroup'.map _) hSC)
    exact H.nonsingular_moved_le_canonical_of_local_block D v hv hshort S
      (hReq.le.trans (inf_le_right.trans (coreQuotientCentralizer_le_normalizer _))) hFit

/-- All three clauses of 12.6.13 on the literal canonical groups, retaining
only nonquasisimplicity and the earlier Sylow position as source inputs. -/
theorem SourceHypothesis.nonsingular_nonquasisimple_canonical_structure
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4) :
    IsSimpleGroup (Star (Kv (v : G))) ∧
    ∃ S : Sylow 2 (Gv (v : G)),
      let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
      let J := Kv (v : G) ⊔ S₀
      Tv T (v : G) ≤ S₀ ∧
      Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (Lv L (v : G) : Set G))
        (Gv (v : G) ⊓ normalizer (Lv L (v : G) : Set G)) ∧
      R L (Kv (v : G)) S₀ (v : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (v : G)) ∧
      generalizedFitting J = pCore 2 J ∧
      centralizer ((U (Kv (v : G)) S₀).subgroupOf J : Set J) = pCore 2 J ∧
      U (Kv (v : G)) S₀ = (reducedTwoSubgroup J).map J.subtype ∧
      Vv L V (v : G) ≤ ⁅U (Kv (v : G)) S₀,Kv (v : G)⁆ := by
  obtain ⟨S,hTS,hN,_,_,hReq,_,hFit,hker,hred⟩ :=
    H.nonsingular_nonquasisimple_canonical_module D v hv hnot hs hi
  exact ⟨(H.nonsingular_canonical_component D v hv).2.2.2.2,
    S,hTS,hN,hReq,hFit,hker,hred,
    H.nonsingular_moved_le_canonical D v hv hTV hnot hs S hTS hN hReq⟩

end CFSG.Quasithin.Chapter12.Section06
