module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelResidual
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.Transport
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Theory.GroupTheory.PerfectCentralizerLift

/-!
# Residual transport in the HS double cover

Take the two-residual of the full preimage of the model centralizer. Its
image is the perfect model residual. Two-perfectness and the binary kernel
make this upstairs residual perfect as well, so it centralizes every lift
of the marked involution. Monotonicity identifies it with the literal
O²(C_K(u)). This avoids assuming surjectivity of the full centralizer map.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

public section
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
private theorem modelMap_kernel_isTwoGroup
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2) :
    IsPGroup 2 (modelMap e).ker :=
  IsPGroup.of_card (n := 1) (by rw [modelMap_ker, hZ, pow_one])

/-- The literal two-residual has the full model two-residual as image. -/
private theorem cover_residual_data
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    ((centralizerTwoResidual u).map (modelMap e) = centralizerTwoResidual e0 ∧
      Group.IsPerfect (centralizerTwoResidual u)) ∧
      centralizerTwoResidual u =
        (pResidual 2 (preimage e u)).map (preimage e u).subtype := by
  let P := preimage e u
  let N := (pResidual 2 P).map P.subtype
  have hN : IsPPerfect 2 N := isPPerfect_embedded_pResidual 2 P
  have himage : N.map (modelMap e) = centralizerTwoResidual e0 := by
    rw [show N = (pResidual 2 (preimage e u)).map (preimage e u).subtype from rfl,
      map_embedded_pResidual, preimage_map, hu]
    rfl
  have hperfect : Group.IsPerfect N := by
    apply Subgroup.isPerfect_iff.mpr
    apply (eq_commutator_of_isPPerfect_of_map_eq N N hN le_normalizer
      (modelMap e) (modelMap_kernel_isTwoGroup e hZ) ?_).symm
    rw [himage]
    exact (Subgroup.isPerfect_iff.mp marked_centralizer_residual_perfect).symm
  let := hperfect
  have hNC : N ≤ centralizer ({u} : Set K) := by
    have huC : u ∈ centralizer (N : Set K) := by
      rw [← comap_centralizer_map_eq_of_perfect (modelMap e) N
        (by rw [modelMap_ker]; exact center_le_centralizer _)]
      change modelMap e u ∈ centralizer (N.map (modelMap e) : Set Carrier)
      rw [hu, himage, mem_centralizer_iff]
      intro x hx
      exact mem_centralizer_singleton_iff.mp (centralizerTwoResidual_le e0 hx)
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp huC x hx)
  have hNX : N = centralizerTwoResidual u := by
    apply le_antisymm
    · have hh := embedded_pResidual_mono 2 hNC
      rw [(pResidual_eq_top_iff 2 N).mpr hN, ← MonoidHom.range_eq_map, range_subtype] at hh
      exact hh
    · exact embedded_pResidual_mono 2 (centralizer_le_preimage e u)
  exact ⟨⟨hNX ▸ himage, hNX ▸ hperfect⟩, hNX.symm⟩

theorem cover_residual_image_and_perfect
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    (centralizerTwoResidual u).map (modelMap e) = centralizerTwoResidual e0 ∧
      Group.IsPerfect (centralizerTwoResidual u) :=
  (cover_residual_data e hZ u hu).1

theorem cover_residual_eq_preimage_residual
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    centralizerTwoResidual u =
      (pResidual 2 (preimage e u)).map (preimage e u).subtype :=
  (cover_residual_data e hZ u hu).2

/-- The cover core maps onto the actual model core. -/
theorem cover_core_image
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    (centralizerCore u).map (modelMap e) = centralizerCore e0 := by
  change ((centralizerTwoResidual u).pCoreIn 2).map (modelMap e) = _
  rw [map_pCoreIn_of_ker_isPGroup _ (modelMap_kernel_isTwoGroup e hZ),
    (cover_residual_image_and_perfect e hZ u hu).1]
  rfl

/-- Elements centralizing the model residual centralize its actual cover residual. -/
theorem cover_commutes_of_model_commutes
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) (a : K)
    (ha : modelMap e a ∈ centralizer (centralizerTwoResidual e0 : Set Carrier)) :
    a ∈ centralizer (centralizerTwoResidual u : Set K) := by
  let := (cover_residual_image_and_perfect e hZ u hu).2
  rw [← comap_centralizer_map_eq_of_perfect (modelMap e) (centralizerTwoResidual u)
    (by rw [modelMap_ker]; exact center_le_centralizer _)]
  change modelMap e a ∈ centralizer ((centralizerTwoResidual u).map (modelMap e) : Set Carrier)
  rwa [(cover_residual_image_and_perfect e hZ u hu).1]

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
