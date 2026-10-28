module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalPoint
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt

/-!
# The original section kernel from local structure

Apply the original 12.8.4 kernel theorem using normalization and the
unique maximal overgroup at the same G,T. Coordinate equivariance
identifies its kernel with that of the literal U/V₁ action.
Source: AS 12.8.4 and 14.7.30, pp.850,1055.
The structural source producer remains qt-d-1222-source; final
14.7.75 discharge remains with qt-d-14775-source.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "B" => (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)


theorem section_action_kernel_eq_core_of_escape_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hescape : ¬ F.H ≤ normalizer (L : Set G))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ρ.ker = pCore 2 F.H := by
  let := h.chosen.elementary
  have he : ρ.ker = (F.localTildeAction F.H le_rfl).ker := by
    ext a
    exact (s.action_mem_ker_iff a).trans
      (F.mem_localTildeAction_ker_iff F.H le_rfl a).symm
  rw [he]
  exact F.localKernel_eq_pCore h.source.simpleQTKE L (normalizer (L : Set G)) F.H
    (by decide) h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique_at structural).2 (Subgroup.centralizer_le_normalizer _ |>.trans (h.seed_normalizer_le_at structural))
    h.centralizer_L (F.H_mem_Hz (by decide) L (normalizer (L : Set G)) hescape)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
