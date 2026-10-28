module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerNoPSL
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerResidualFusion
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerResidualLift
/-!
# The actual alternating-six residuals in F.5.5

Endpoint fusion discharges the successive-transfer and I.4.1(2) hypotheses.
The original root fixes an A4 and acts nontrivially, excluding PSL3(2). The
faithful endpoint Sylow lift then identifies the original residual with the
quotient residual. Both are the actual A6, with the quotient map retained.

Source: Aschbacher--Smith F.5.5, printed p.302.
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

theorem source_graph_residual_alternating (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    Nonempty (pResidual 2 (graphCentralQuotient c i) ≃* alternatingGroup (Fin 6)) :=
  (source_graph_residual_recognition c i z h R hR).resolve_left
    (source_graph_residual_not_psl c i z h)

theorem source_centralizer_residual_quotient_equiv (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    ∃e:pResidual 2 (C c i) ≃* pResidual 2 (graphCentralQuotient c i),
      ∀x:pResidual 2 (C c i),(e x).val=
        QuotientGroup.mk' (zpowers (graphInCentralizer c i)) x.val := by
  obtain ⟨P,hP⟩:=source_graph_residual_sylow c i z h R hR
  exact source_graph_residual_equiv_of_sylow c i z h P hP

theorem source_centralizer_residual_alternating (R:Sylow 2 (C c i)) (hR:Tf c i≤R) :
    Nonempty (pResidual 2 (C c i) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e,he⟩:=source_centralizer_residual_quotient_equiv c i z h R hR
  obtain ⟨eA⟩:=source_graph_residual_alternating c i z h R hR
  exact ⟨e.trans eA⟩
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
