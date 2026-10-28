module
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Normalization of a plane-centralizer residual

Suppose Y acts on P with kernel O₂(Y), and this kernel is contained in
R, where R normalizes both A and P. If C_A(P) normalizes Y, then Y
normalizes O²(C_A(P)). Indeed, [Y,C_A(P)] lies in O₂(Y), and R normalizes
C_A(P). Recovering the residual after adjoining this normalizing two-group
proves the conclusion, with all subgroups kept in the ambient group.

Source application: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf, with A = L₁ and the actual reciprocal plane P.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A two-core action kernel controls the residual of the relative
centralizer without requiring that centralizer to be contained in Y. -/
theorem normalizes_plane_centralizer_residual
    (A P Y R : Subgroup G)
    (hAPY : A ⊓ centralizer (P : Set G) ≤ normalizer (Y : Set G))
    (hYP : Y ≤ normalizer (P : Set G))
    (hkernel : Y ⊓ centralizer (P : Set G) = Y.pCoreIn 2)
    (hcore : Y.pCoreIn 2 ≤ R)
    (hRA : R ≤ normalizer (A : Set G))
    (hRP : R ≤ normalizer (P : Set G)) :
    Y ≤ normalizer ((pResidual 2 (A ⊓ centralizer (P : Set G) : Subgroup G)).map
      (A ⊓ centralizer (P : Set G)).subtype : Set G) := by
  let C := A ⊓ centralizer (P : Set G)
  have hRC : R ≤ normalizer (C : Set G) :=
    (le_inf hRA (hRP.trans (normalizer_le_normalizer_centralizer P))).trans
      inf_normalizer_le_normalizer_inf
  have hcomm : ⁅Y,C⁆ ≤ Y.pCoreIn 2 := by
    rw [←hkernel]
    apply le_inf (le_normalizer_iff_commutator_le_left.mp hAPY)
    exact (commutator_mono le_rfl inf_le_right).trans
      (le_normalizer_iff_commutator_le_right.mp
        (hYP.trans (normalizer_le_normalizer_centralizer P)))
  exact normalizes_residual_of_commutator_le_two Y R C (Y.pCoreIn 2) hRC hcore
    (isPGroup_pCoreIn 2 Y)
    (Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)))
    ((commutator_mono le_rfl (map_subtype_le _)).trans hcomm)
end Subgroup
