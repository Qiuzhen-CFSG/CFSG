module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerQuotient
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.Source

/-!
# Source application of the graph-centralizer quotient

The source joint-centralizer theorem and full fusion producer discharge all
premises of the first centralizer step of F.5.5. The involution in the actual
quotient by the graph involution has centralizer equal to the actual image of
any chosen Sylow of the graph centralizer.

Source: Aschbacher--Smith F.5.5, printed pp.301--302.
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

/-- A root of the original source has precisely R as its graph-centralizer. -/
theorem source_graph_centralizer_root (R : Sylow 2 (C c i)) :
    ∃ u : G, u ∈ Rimage c i R ∧ IsConj (rootElement c i z) u ∧
      IsConj (Source.graphElement c i) (Source.graphElement c i*u) ∧
      C c i ⊓ centralizer ({u} : Set G) = Rimage c i R :=
  exists_graph_centralizer_root c i z (sourceMarkedShort c i)
    (source_fusionFacts c i z h) R (source_normalizer_joint_centralizer c i z h)

/-- The source quotient centralizer is a Sylow subgroup, with its actual map. -/
theorem source_graph_quotient_sylow_centralizer (R : Sylow 2 (C c i)) :
    ∃ u : C c i, u ∈ (R : Subgroup (C c i)) ∧
      IsConj (rootElement c i z) u.val ∧
      orderOf (QuotientGroup.mk' (zpowers (graphInCentralizer c i)) u)=2 ∧
      centralizer ({QuotientGroup.mk' (zpowers (graphInCentralizer c i)) u} :
        Set (graphCentralQuotient c i)) =
        (R : Subgroup (C c i)).map (QuotientGroup.mk' (zpowers (graphInCentralizer c i))) :=
  exists_graph_quotient_sylow_centralizer c i z (sourceMarkedShort c i)
    (source_fusionFacts c i z h) h R (source_normalizer_joint_centralizer c i z h)

/-- In particular, the literal quotient has an involution with Sylow centralizer. -/
theorem source_graph_quotient_has_sylow_centralizer :
    ∃ u : graphCentralQuotient c i, orderOf u=2 ∧
      ∃ S : Sylow 2 (graphCentralQuotient c i),
        centralizer ({u} : Set (graphCentralQuotient c i)) = S := by
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 2 (C c i)))
  obtain ⟨u,_,_,hu,hC⟩ := source_graph_quotient_sylow_centralizer c i z h R
  refine ⟨_,hu,R.mapSurjective (f := QuotientGroup.mk' (zpowers (graphInCentralizer c i)))
    (QuotientGroup.mk'_surjective _),?_⟩
  exact hC

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
