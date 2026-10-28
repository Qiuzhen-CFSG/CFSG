module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerResidual
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionResidualConjugacy
/-!
# Discharging residual fusion in the graph-centralizer recognition

The endpoint three-cycle conjugators prove fusion inside O²(C_G(f)/⟨f⟩).
They discharge the remaining fusion premise of the successive-transfer and
I.4.1(2) applications, retaining only the original source hypotheses.

Source: Aschbacher–Smith F.5.5, printed pp.301–302.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)

include h

/-- The literal endpoint dihedral subgroup is a Sylow subgroup of the residual. -/
theorem source_graph_residual_sylow (R : Sylow 2 (C c i)) (hR : Tf c i≤R) :
    ∃ P : Sylow 2 (pResidual 2 (graphCentralQuotient c i)),
      (P : Subgroup (pResidual 2 (graphCentralQuotient c i))).map
        (pResidual 2 (graphCentralQuotient c i)).subtype=sourceResidualJoinQuotient c i :=
  source_graph_residual_sylow_of_residual_fusion c i z h R hR
    (sourceResidualJoinQuotient_involution_conjugate_in_residual c i h.embedding_injective)

/-- I.4.1(2) applied to the literal graph-centralizer residual. -/
theorem source_graph_residual_recognition (R : Sylow 2 (C c i)) (hR : Tf c i≤R) :
    Nonempty ((pResidual 2 (graphCentralQuotient c i)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
    Nonempty ((pResidual 2 (graphCentralQuotient c i)) ≃* alternatingGroup (Fin 6)) :=
  source_graph_residual_recognition_of_residual_fusion c i z h R hR
    (sourceResidualJoinQuotient_involution_conjugate_in_residual c i h.embedding_injective)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
