module

public import CFSG.Quasithin.ChapterI.Section04To05.DSystem
public import Theory.GroupAction.TypedCosetGeometry.Residues.Transport
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# The actual quotient parabolics of a D-system

The local two-core lies in the common Sylow subgroup. Passing through any
chosen equivalence of the local core quotient therefore preserves precisely
the two maximal parabolics and their common Sylow subgroup. All maps below
are the original quotient map followed by the supplied model equivalence.

Source: Aschbacher–Smith I.5.3–4, printed pp.419–420.
-/

@[expose] public noncomputable section
namespace Quasithin.I5
open Subgroup
variable {G K : Type*} [Group G] [Group K]

namespace RankTwoParabolics
variable {B P R : Subgroup G} (h : RankTwoParabolics G B P R)

include h in
theorem map (f : G →* K) (hf : Function.Surjective f) (hk : f.ker ≤ B) :
    RankTwoParabolics K (B.map f) (P.map f) (R.map f) := by
  have hBP : B ≤ P := h.borel_eq ▸ inf_le_left
  have hBR : B ≤ R := h.borel_eq ▸ inf_le_right
  have hmax (U : Subgroup G) (hu : IsCoatom U) (hBU : B ≤ U) :
      IsCoatom (U.map f) := by
    have hc : (U.map f).comap f = U := comap_map_eq_self (hk.trans hBU)
    refine ⟨?_, ?_⟩
    · intro he
      apply hu.1
      rw [← hc, he, comap_top]
    · intro V hv
      have hlt : U < V.comap f := by
        rw [← hc]
        exact (comap_lt_comap_of_surjective hf).mpr hv
      exact (comap_injective hf) ((hu.2 _ hlt).trans (comap_top f).symm)
  refine ⟨hmax P h.left_maximal hBP, hmax R h.right_maximal hBR, ?_, ?_, ?_⟩
  · intro he
    apply h.distinct
    have hc := congrArg (comap f) he
    simpa only [comap_map_eq_self (hk.trans hBP),
      comap_map_eq_self (hk.trans hBR)] using hc
  · apply comap_injective hf
    rw [comap_inf, comap_map_eq_self (hk.trans hBP),
      comap_map_eq_self (hk.trans hBR), comap_map_eq_self hk, h.borel_eq]
  · intro U hBU hU
    have hb : B ≤ U.comap f := map_le_iff_le_comap.mp hBU
    rcases h.exhaustive (U.comap f) hb (isCoatom_comap_of_surjective hf hU) with he | he
    · left
      rw [← he, map_comap_eq_self_of_surjective hf]
    · right
      rw [← he, map_comap_eq_self_of_surjective hf]

end RankTwoParabolics

namespace DSystem
variable {D : Diagram} (S : DSystem D G) (i : Fin 3)

def localQuotientMap (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    S.family i →* K := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (S.family i)))

theorem localQuotientMap_surjective (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    Function.Surjective (S.localQuotientMap i e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem localQuotientMap_ker (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    (S.localQuotientMap i e).ker = pCore 2 (S.family i) := by
  ext x
  change e (QuotientGroup.mk' _ x) = 1 ↔ _
  rw [e.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

theorem local_core_le_chamber : pCore 2 (S.family i) ≤ S.T.subgroupOf (S.family i) := by
  obtain ⟨P, hP⟩ := S.sylow i
  rw [← hP]
  exact pCore_isPGroup.le_sylow_of_normal P

theorem localQuotientMap_ker_le (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    (S.localQuotientMap i e).ker ≤ S.T.subgroupOf (S.family i) := by
  rw [S.localQuotientMap_ker]
  exact S.local_core_le_chamber i

theorem localQuotientMap_ker_le_intrinsic
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    (S.localQuotientMap i e).ker ≤ CosetGeometry.intrinsicIntersection S.family i := by
  rw [CosetGeometry.intrinsicIntersection_eq]
  exact S.localQuotientMap_ker_le i e

theorem localQuotient_sylow [Finite K]
    (e : (S.family i ⧸ pCore 2 (S.family i)) ≃* K) :
    ∃ P : Sylow 2 K, (P : Subgroup K) =
      (S.T.subgroupOf (S.family i)).map (S.localQuotientMap i e) := by
  obtain ⟨P, hP⟩ := S.sylow i
  refine ⟨P.mapSurjective (S.localQuotientMap_surjective i e), ?_⟩
  change (P : Subgroup (S.family i)).map _ = _
  rw [hP]

end DSystem
end Quasithin.I5
