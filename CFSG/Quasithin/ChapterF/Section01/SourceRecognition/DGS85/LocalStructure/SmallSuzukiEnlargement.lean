module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.DihedralApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SuzukiEnlargement
public import Theory.SpecificGroups.Suzuki.SmallAutomorphisms
/-!
# All Suzuki parameters in the genuine Chapter 6 enlargement

For Sz(2), every automorphism is inner, so the literal quotient-action
kernel and the unchanged embedded core prevent enlargement. Together
with the established positive-parameter argument this covers every
Suzuki row, including the small group. The dihedral-to-Sz(2) transition
remains the separate strict alternative.

The reduced F1.11 graph actor is identified with the original starred
parabolic. Its quotient marking retains the original quotient inclusion
on every representative, with the actual full Borel and cores unchanged.
No finiteness of the completion or extra action premise is assumed.

Source: DGS, *Groups and Graphs* (1985), 6.1 and its remark, pp.118--119;
Aschbacher--Smith F.1.9, printed pp.261--262.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P B : Subgroup G}

/-- The small Suzuki row does not enlarge the original starred endpoint. -/
theorem localEnlargement_eq_star_of_suzuki_zero (d : LocalRankOneData P B)
    (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* SuzukiMatrixGroup 0) :
    localEnlargement d = d.Pstar := by
  have hz : center (d.Pstar ⧸ pCore 2 d.Pstar) = ⊥ := by
    apply bot_unique
    intro x hx
    have he : e x ∈ center (SuzukiMatrixGroup 0) := (centerCongr e ⟨x,hx⟩).property
    rw [suzukiZero_center_eq_bot,mem_bot] at he
    exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))
  apply localEnlargement_eq_star_of_inner d hz
  rintro a ⟨g,rfl⟩
  obtain ⟨b,hb⟩ := suzukiZero_automorphism_inner (MulAut.congr e (localStarCoreAction d g))
  obtain ⟨c,hc⟩ := (MulAut.congr_inner_iff e _).mp ⟨b,hb⟩
  exact ⟨c,hc.symm⟩

/-- Every Suzuki parameter satisfies the source 6.1 starred equality. -/
theorem localEnlargement_eq_star_of_suzuki_all (d : LocalRankOneData P B)
    (m : ℕ) (e : (d.Pstar ⧸ pCore 2 d.Pstar) ≃* SuzukiMatrixGroup m) :
    localEnlargement d = d.Pstar := by
  cases m with
  | zero => exact localEnlargement_eq_star_of_suzuki_zero d e
  | succ n => exact localEnlargement_eq_star_of_suzuki d (Nat.succ_pos n) e

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The full-Borel reduction retains the original starred group for every Suzuki row. -/
theorem reduced_enlargedEndpoint_eq_starred_of_suzuki_all (h : HypothesisF11 L S)
    (i : Fin 2) (m : ℕ) (e : (L i ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    enlargedEndpoint L S i = starredParabolic L S i := by
  let hh := SuzukiContainment.reduced_hypothesis h
  have he := localEnlargement_eq_star_of_suzuki_all (hh.starredLocalRankOneData i)
    m ((hh.starredQuotientEquiv i).symm.trans e)
  rw [reduced_localEnlargement_eq h i] at he
  exact he.trans (SuzukiContainment.reduced_starredParabolic h i)

open Subgroup.CosetGeometry.RankTwo

/-- The actual graph actor is the original starred endpoint, including Sz(2). -/
def reduced_suzukiActorEquiv_all (h : HypothesisF11 L S) (i : Bool) (m : ℕ)
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* SuzukiMatrixGroup m) :
    graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ≃*
      family (starredParabolic L S) i := by
  have he : family (enlargedEndpoint L S) i = family (starredParabolic L S) i := by
    cases i
    · exact reduced_enlargedEndpoint_eq_starred_of_suzuki_all h 0 m e
    · exact reduced_enlargedEndpoint_eq_starred_of_suzuki_all h 1 m e
  exact (reduced_enlargementActorEquiv h i).trans (MulEquiv.subgroupCongr he)

/-- The actor identification preserves the original completion inclusion. -/
theorem reduced_suzukiActorEquiv_all_coe (h : HypothesisF11 L S) (i : Bool) (m : ℕ)
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* SuzukiMatrixGroup m)
    (x : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)) :
    (reduced_suzukiActorEquiv_all h i m e x : G) = (x : G₀ L S) :=
  reduced_enlargementActorEquiv_coe h i x

/-- The original Suzuki marking on the actual graph actor, for every parameter. -/
def reduced_graphSuzukiQuotient_all (h : HypothesisF11 L S) (i : Bool) (m : ℕ)
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* SuzukiMatrixGroup m) :
    (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) ≃*
        SuzukiMatrixGroup m :=
  (QuotientGroup.congr _ _ (reduced_suzukiActorEquiv_all h i m e)
    (pCore_map_iso 2 _)).trans ((originalStarredQuotientEquiv h i).symm.trans e)

/-- The graph quotient marking agrees with the original starred quotient inclusion. -/
theorem reduced_graphSuzukiQuotient_all_mk (h : HypothesisF11 L S) (i : Bool) (m : ℕ)
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* SuzukiMatrixGroup m)
    (x : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)) :
    reduced_graphSuzukiQuotient_all h i m e (QuotientGroup.mk x) =
      e ((originalStarredQuotientEquiv h i).symm
        (QuotientGroup.mk (reduced_suzukiActorEquiv_all h i m e x))) := by rfl

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
