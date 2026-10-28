module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.ModelAction.SylowAction

/-!
# The actual Sylow action on every envelope factor

Transfer the relative block from the layer envelope to C_G(A), then use
the checked common-Sylow action theorem. The result retains both the
literal intersection with Q and the conjugating omega-center elements.
It applies to every selected factor, independently of the missing
transporter calculations.

Source: Aschbacher–Smith, E.6.7 and its use in E.6.23,
combined manuscript (1 March 2004), printed pp.246 and 254.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
open InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]

/-- Every actual E.6.7 envelope factor has the common Sylow and inner V-action. -/
theorem envelope_factor_sylow_action
    {K : GroupClass} {T : Sylow 2 G} {M V A : Subgroup G}
    (h : HypothesisE61 K T M V) (h21 : OddCoreFree V)
    (hA : A ∈ obstructionFamily M V)
    (d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V A
      (layerEnvelope (centralizer (A : Set G)) (sylowCentralizer (T : Subgroup G) V)))
    (i : Fin d.count) :
    ∃ S : Sylow 2 (d.block i),
      (S : Subgroup (d.block i)).map (d.block i).subtype =
        d.block i ⊓ sylowCentralizer (T : Subgroup G) V ∧
      ∀ v ∈ V, ∃ z : d.block i,
        z ∈ Stellmacher.omegaOneCenterAmbient (S : Subgroup (d.block i)) ∧
        ∀ x : d.block i, (z : G) * (x : G) * (z : G)⁻¹ =
          v * (x : G) * v⁻¹ := by
  let Q := sylowCentralizer (T : Subgroup G) V
  let R := layerEnvelope (centralizer (A : Set G)) Q
  have hQA : Q ≤ centralizer (A : Set G) := inf_le_right.trans (centralizer_le hA.1)
  have hbR : ChapterC.IsBlock ((d.block i).subgroupOf R) :=
    ⟨inferInstance, (d.type i).chi.short.of_mulEquiv
      (subgroupOfEquivOfLe (d.le i)).symm, d.subnormal i⟩
  have hbA := block_lift_from_layerEnvelope hQA
    (T.isPGroup'.to_le inf_le_left) (d.le i) hbR
  exact BlockCase.block_common_sylow_action h h21 hA
    ⟨(d.le i).trans (layerEnvelope_le hQA), hbA⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Detection
