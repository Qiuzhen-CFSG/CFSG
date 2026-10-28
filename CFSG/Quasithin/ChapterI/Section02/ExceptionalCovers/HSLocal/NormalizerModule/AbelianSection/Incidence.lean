module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Setup
public import Theory.GroupTheory.PCoreImage

/-!
# Lifting the HS core incidences through the central quotient

The central involution lies in the two-core of the residual centralizer and
in its center. Consequently both subgroups are full inverse images of their
model images. Normal generation in the model then lifts without an extra
cover incidence assumption. This gives the abelian core required in the last
HS paragraph of Aschbacher–Smith I.2.2(5), printed p.412 / PDF p.423.

The residual image and center image are earlier centralizer inputs. The
three model incidences remain explicit for the concrete geometry producer.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Sporadic.LeechRelated.HS.BlockNormalizer
open Sporadic.LeechRelated.HS.EvenLocalCandidates
variable {K : Type*} [Group K]

theorem center_le_centralizerCore_of_le_residual (u : K)
    (hZ : Nat.card (center K) = 2) (hZX : center K ≤ centralizerTwoResidual u) :
    center K ≤ centralizerCore u := by
  exact le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 1) (by simpa using hZ)) hZX
    (by rw [normalizer_eq_top]; exact le_top)

theorem center_le_coreCenter_of_le_residual (u : K)
    (hZ : Nat.card (center K) = 2) (hZX : center K ≤ centralizerTwoResidual u) :
    center K ≤ coreCenter u := by
  intro z hz
  have hr := center_le_centralizerCore_of_le_residual u hZ hZX hz
  refine ⟨⟨z, hr⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact mem_center_iff.mp hz x

theorem residual_eq_model_preimage
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (u : K)
    (hZX : center K ≤ centralizerTwoResidual u)
    (hX : (centralizerTwoResidual u).map (modelMap e) = centralizerTwoResidual e0) :
    centralizerTwoResidual u = (centralizerTwoResidual e0).comap (modelMap e) := by
  rw [← hX, comap_map_eq_self (by rwa [modelMap_ker])]

theorem centralizerCore_map_modelMap [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (hX : (centralizerTwoResidual u).map (modelMap e) = centralizerTwoResidual e0) :
    (centralizerCore u).map (modelMap e) = centralizerCore e0 := by
  have hk : IsPGroup 2 (modelMap e).ker :=
    IsPGroup.of_card (n := 1) (by rw [modelMap_ker, hZ, pow_one])
  change ((centralizerTwoResidual u).pCoreIn 2).map (modelMap e) = _
  rw [map_pCoreIn_of_ker_isPGroup _ hk, hX]
  rfl

theorem centralizerCore_eq_model_preimage [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (hZX : center K ≤ centralizerTwoResidual u)
    (hX : (centralizerTwoResidual u).map (modelMap e) = centralizerTwoResidual e0) :
    centralizerCore u = (centralizerCore e0).comap (modelMap e) := by
  rw [← centralizerCore_map_modelMap e hZ u hX, comap_map_eq_self]
  rw [modelMap_ker]
  exact center_le_centralizerCore_of_le_residual u hZ hZX

theorem coreCenter_eq_model_preimage
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (hZX : center K ≤ centralizerTwoResidual u)
    (hV : (coreCenter u).map (modelMap e) = coreCenter e0) :
    coreCenter u = (coreCenter e0).comap (modelMap e) := by
  rw [← hV, comap_map_eq_self]
  rw [modelMap_ker]
  exact center_le_coreCenter_of_le_residual u hZ hZX

theorem coreCenter_le_M_of_model
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (u : K)
    (hV : (coreCenter u).map (modelMap e) = coreCenter e0)
    (hVM : coreCenter e0 ≤ baseNormalizer) : coreCenter u ≤ M e := by
  exact map_le_iff_le_comap.mp (hV ▸ hVM)

theorem Q_le_residual_of_model [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (hZX : center K ≤ centralizerTwoResidual u)
    (hX : (centralizerTwoResidual u).map (modelMap e) = centralizerTwoResidual e0)
    (hAX : (pCore 2 baseNormalizer).map baseNormalizer.subtype ≤ centralizerTwoResidual e0) :
    (Q e).map (M e).subtype ≤ centralizerTwoResidual u := by
  rw [residual_eq_model_preimage e u hZX hX]
  apply map_le_iff_le_comap.mp
  have hmap : ((Q e).map (M e).subtype).map (modelMap e) =
      ((Q e).map (localMap e)).map baseNormalizer.subtype := by
    rw [map_map, map_map]
    rfl
  rw [hmap, Q_map_localMap e hZ]
  exact hAX

theorem coreCenter_subgroupOf_map_localMap
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (u : K)
    (hV : (coreCenter u).map (modelMap e) = coreCenter e0)
    (hVM : coreCenter e0 ≤ baseNormalizer) :
    ((coreCenter u).subgroupOf (M e)).map (localMap e) =
      (coreCenter e0).subgroupOf baseNormalizer := by
  apply (map_injective baseNormalizer.subtype_injective)
  rw [map_subgroupOf_eq_of_le hVM, ← hV]
  calc
    _ = (((coreCenter u).subgroupOf (M e)).map (M e).subtype).map (modelMap e) := by
      rw [map_map, map_map]
      rfl
    _ = _ := by rw [map_subgroupOf_eq_of_le (coreCenter_le_M_of_model e u hV hVM)]

theorem normalClosure_coreCenter_eq_Q_of_model [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (hZX : center K ≤ centralizerTwoResidual u)
    (hV : (coreCenter u).map (modelMap e) = coreCenter e0)
    (hVM : coreCenter e0 ≤ baseNormalizer)
    (hgen : normalClosure ((coreCenter e0).subgroupOf baseNormalizer : Set baseNormalizer) =
      pCore 2 baseNormalizer) :
    normalClosure ((coreCenter u).subgroupOf (M e) : Set (M e)) = Q e := by
  have hk : (localMap e).ker ≤
      normalClosure ((coreCenter u).subgroupOf (M e) : Set (M e)) := by
    rw [localMap_ker]
    exact (subgroupOf_mono (M e)
      (center_le_coreCenter_of_le_residual u hZ hZX)).trans le_normalClosure
  rw [Q_eq_model_core_preimage e hZ, ← hgen,
    ← coreCenter_subgroupOf_map_localMap e u hV hVM, coe_map,
    ← map_normalClosure _ _ (localMap_surjective e), comap_map_eq_self hk]

/-- The cover core is abelian, using only earlier centralizer facts and
the three literal model incidences. -/
theorem Q_isMulCommutative_of_model_incidence [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (hZX : center K ≤ centralizerTwoResidual u)
    (hX : (centralizerTwoResidual u).map (modelMap e) = centralizerTwoResidual e0)
    (hV : (coreCenter u).map (modelMap e) = coreCenter e0)
    (hXV : centralizerTwoResidual u ≤ centralizer (coreCenter u : Set K))
    (hAX : (pCore 2 baseNormalizer).map baseNormalizer.subtype ≤ centralizerTwoResidual e0)
    (hVM : coreCenter e0 ≤ baseNormalizer)
    (hgen : normalClosure ((coreCenter e0).subgroupOf baseNormalizer : Set baseNormalizer) =
      pCore 2 baseNormalizer) : IsMulCommutative (Q e) :=
  Q_isMulCommutative_of_incidence e u
    (Q_le_residual_of_model e hZ u hZX hX hAX) hXV
    (normalClosure_coreCenter_eq_Q_of_model e hZ u hZX hV hVM hgen)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
