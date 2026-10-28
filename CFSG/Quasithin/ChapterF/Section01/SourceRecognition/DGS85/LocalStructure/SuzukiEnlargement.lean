module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement
public import Theory.SpecificGroups.Suzuki.SylowSupplement

/-!
# Nondegenerate Suzuki endpoints in the Chapter 6 enlargement

The full Borel core acts on the starred quotient through a two-group.
The Suzuki outer automorphism group has odd order, so this action is inner.
The inner-action join has the same quotient, and the already established
unchanged embedded core forces the enlargement to equal the starred group.
Only the endpoint is finite; the ambient completion is unrestricted.

For the actual reduced F1.11 triple this identifies the graph local actor
with the original starred parabolic. The quotient marking and its formula
on representatives retain the original local-to-starred inclusion.

Source: DGS, Groups and Graphs (1985), 6.1 and its remark, pp.118--119.
This covers Sz(2^(2m+1)) with m > 0. The small Suzuki/dihedral transition
and the unitary alternatives remain separate source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}

/-- Nondegenerate Suzuki quotients do not enlarge the starred endpoint. -/
theorem localEnlargement_eq_star_of_suzuki (d : LocalRankOneData P B)
    {m : ℕ} (hm : 0 < m)
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* SuzukiMatrixGroup m) :
    localEnlargement d = d.Pstar := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  have hBP : B ≤ P := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  let R := B.pCoreIn 2
  have hn : R ≤ normalizer (d.Pstar : Set G) :=
    ((pCoreIn_le 2 B).trans hBP).trans
      ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal)
  have hz : center (d.Pstar ⧸ pCore 2 d.Pstar) = ⊥ := by
    let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    have hc : center (SuzukiMatrixGroup m) = ⊥ := by
      rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with hc | hc
      · exact hc
      · exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
          (Group.isSolvable_of_comm (fun x y => by
            have hx : x ∈ center (SuzukiMatrixGroup m) := hc ▸ mem_top x
            exact (mem_center_iff.mp hx y).symm))).elim
    apply bot_unique
    intro x hx
    have he : e x ∈ center (SuzukiMatrixGroup m) := (centerCongr e ⟨x,hx⟩).property
    rw [hc,mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))
  have ho : Odd (Nat.card (MulAut.Outer (d.Pstar ⧸ pCore 2 d.Pstar))) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    exact suzuki_odd_outer_index m hm
  let a := (pCoreJoinAction 2 hn).comp (inclusion (show R ≤ d.Pstar ⊔ R from le_sup_right))
  have hi (r : R) : pCoreJoinAction 2 hn (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (d.Pstar ⧸ pCore 2 d.Pstar) := by
    obtain ⟨k,hk⟩ := isPGroup_pCoreIn 2 B r
    have hp : a r ^ (2^k) = 1 := by rw [←map_pow,hk,map_one]
    obtain ⟨x,hx⟩ := MulAut.inner_of_two_pow_eq_one_of_odd_index ho (a r) hp
    exact ⟨x,hx.symm⟩
  have hm := map_subgroupOf_pCoreJoin_eq_top_of_inner d.Pstar R hn (isPGroup_pCoreIn 2 B) hz hi
  have hc := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 (d.Pstar ⊔ R : Subgroup G)))) hm
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top] at hc
  have hh := congrArg (Subgroup.map (d.Pstar ⊔ R).subtype) hc
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show d.Pstar ≤ d.Pstar ⊔ R from le_sup_left),
    ←MonoidHom.range_eq_map,range_subtype] at hh
  change d.Pstar ⊔ (localEnlargement d).pCoreIn 2 = localEnlargement d at hh
  rw [localEnlargement_core d,sup_eq_left.mpr (source_core_le_star d)] at hh
  exact hh.symm

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The reduced source enlargement is the original starred parabolic. -/
theorem reduced_enlargedEndpoint_eq_starred_of_suzuki (h : HypothesisF11 L S) (i : Fin 2)
    {m : ℕ} (hm : 0 < m) (e : (L i ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    enlargedEndpoint L S i = starredParabolic L S i := by
  let hh := SuzukiContainment.reduced_hypothesis h
  have he := localEnlargement_eq_star_of_suzuki (hh.starredLocalRankOneData i)
    hm ((hh.starredQuotientEquiv i).symm.trans e)
  rw [reduced_localEnlargement_eq h i] at he
  exact he.trans (SuzukiContainment.reduced_starredParabolic h i)

open Subgroup.CosetGeometry.RankTwo

/-- The actual graph actor embeds onto the original starred endpoint. -/
def reduced_suzukiActorEquiv (h : HypothesisF11 L S) (i : Bool)
    {m : ℕ} (hm : 0 < m)
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* SuzukiMatrixGroup m) :
    graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ≃*
      family (starredParabolic L S) i := by
  have he : (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).map
      (G₀ L S).subtype = family (starredParabolic L S) i := by
    rw [reduced_graphLocalGroup_image h]
    cases i
    · exact reduced_enlargedEndpoint_eq_starred_of_suzuki h 0 hm e
    · exact reduced_enlargedEndpoint_eq_starred_of_suzuki h 1 hm e
  exact ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).equivMapOfInjective
    (G₀ L S).subtype (G₀ L S).subtype_injective).trans (MulEquiv.subgroupCongr he)

/-- The actor equivalence preserves every original completion element. -/
theorem reduced_suzukiActorEquiv_coe (h : HypothesisF11 L S) (i : Bool)
    {m : ℕ} (hm : 0 < m)
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* SuzukiMatrixGroup m)
    (x : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)) :
    (reduced_suzukiActorEquiv h i hm e x : G) = (x : G₀ L S) := by rfl

/-- The original local Suzuki marking on the actual reduced graph actor. -/
def reduced_graphSuzukiQuotient (h : HypothesisF11 L S) (i : Bool)
    {m : ℕ} (hm : 0 < m)
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* SuzukiMatrixGroup m) :
    (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) ≃*
        SuzukiMatrixGroup m :=
  (QuotientGroup.congr _ _ (reduced_suzukiActorEquiv h i hm e)
    (pCore_map_iso 2 _)).trans ((originalStarredQuotientEquiv h i).symm.trans e)

/-- The quotient map is the original starred inclusion followed by the original marking. -/
theorem reduced_graphSuzukiQuotient_mk (h : HypothesisF11 L S) (i : Bool)
    {m : ℕ} (hm : 0 < m)
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* SuzukiMatrixGroup m)
    (x : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)) :
    reduced_graphSuzukiQuotient h i hm e (QuotientGroup.mk x) =
      e ((originalStarredQuotientEquiv h i).symm
        (QuotientGroup.mk (reduced_suzukiActorEquiv h i hm e x))) := by rfl
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
