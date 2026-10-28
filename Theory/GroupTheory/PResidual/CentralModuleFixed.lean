module
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover
/-!
# Residual centralizers through a central p-layer

A p-perfect actor centralizes a p-subgroup whenever its displacement lies
in a central layer. Apply commutator idempotence to the largest subgroup
centralizing the actor modulo that layer. Consequently taking the embedded
p-residual of a pointwise centralizer commutes with allowing central
errors, provided the points lie in a normal p-subgroup.

This removes the central module kernel in the A₆ local residual calculation
of Aschbacher–Smith 3.3.31, printed p.602.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Central errors vanish under a p-perfect action on a p-group. -/
theorem centralizes_of_isPPerfect_central_displacement
    (B U E F : Subgroup G) (hB : IsPPerfect p B) (hU : IsPGroup p U)
    (hBU : B ≤ normalizer U) (hUF : U ≤ normalizer F)
    (hFB : F ≤ centralizer (B : Set G)) (hEU : E ≤ U) (hEF : ⁅E, B⁆ ≤ F) :
    E ≤ centralizer (B : Set G) := by
  let C := commutatorPreimage U B F
  have hBC : B ≤ normalizer C := commutatorPreimage_normalized U B F B hUF hBU
    B.le_normalizer ((le_centralizer_iff.mp hFB).trans (Subgroup.centralizer_le_normalizer _))
  have hCF : ⁅C, B⁆ ≤ F := commutator_commutatorPreimage_le U B F hUF
  have hCB : C ≤ centralizer (B : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← commutator_isPPerfect_idempotent B C hB (hU.to_le (commutatorPreimage_le U B F)) hBC]
    exact (commutator_mono hCF le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr hFB).le
  exact (le_commutatorPreimage hEU hEF).trans hCB

/-- Centralizing modulo a central layer has the same embedded p-residual as actual centralization. -/
theorem embedded_residual_centralizer_eq_central_preimage
    (U E F : Subgroup G) [U.Normal] (hU : IsPGroup p U)
    (hEU : E ≤ U) (hF : F ≤ center G) :
    (pResidual p (centralizer (E : Set G))).map (centralizer (E : Set G)).subtype =
      (pResidual p (commutatorPreimage ⊤ E F)).map (commutatorPreimage ⊤ E F).subtype := by
  let D := commutatorPreimage (⊤ : Subgroup G) E F
  let R := (pResidual p D).map D.subtype
  let : F.Normal := ⟨fun f hf g => by
    rw [mem_center_iff.mp (hF hf) g, mul_inv_cancel_right]
    exact hf⟩
  have hFN : (⊤ : Subgroup G) ≤ normalizer F := le_normalizer_of_normal
  have hFR : F ≤ centralizer (R : Set G) := hF.trans (center_le_centralizer _)
  have hEF : ⁅E,R⁆ ≤ F := by
    rw [commutator_comm]
    exact (commutator_mono (map_subtype_le _) le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ E F hFN)
  have hRC : R ≤ centralizer (E : Set G) := le_centralizer_iff.mp
    (centralizes_of_isPPerfect_central_displacement R U E F
      (isPPerfect_embedded_pResidual p D) hU le_normalizer_of_normal
      (le_top.trans hFN) hFR hEU hEF)
  apply le_antisymm
  · exact embedded_pResidual_mono p (le_commutatorPreimage le_top
      (by rw [commutator_eq_bot_iff_le_centralizer.mpr le_rfl]; exact bot_le))
  · have hh := embedded_pResidual_mono p hRC
    rw [(pResidual_eq_top_iff p R).mpr (isPPerfect_embedded_pResidual p D),
      ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
end Subgroup
