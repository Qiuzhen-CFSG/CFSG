module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerCubicActor
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerElementaryPairAction
/-!
# Excluding the elementary residual centralizer in F.5.5

Assume the literal R₀ is elementary abelian. Fusion supplies a cubic action
on its four elements, adjusted to centralize the actual A₆ residual. The two
endpoint four-groups then give elementary subgroups of order sixteen whose
intersection has order eight and whose normalizer quotients both have order
divisible by nine. The original elementary-subgroup list excludes this pair.

This proves the remaining non-elementarity input for the cyclic-four and
marked-square-root recognition. Source: Aschbacher–Smith F.5.5(2), printed p.302.
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

/-- The original source hypotheses rule out the elementary four-group alternative. -/
theorem source_Rzero_not_elementary (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R) :
    ¬ IsElementaryAbelian 2 (Rzero c i R) := by
  rw [source_Rzero_eq_residual_centralizer c i z h R hR]
  intro hEA
  let := hEA
  obtain ⟨g,hg,hgo⟩ := source_residualCentralizer_centralizing_cubic c i z h R hR
  exact source_elementary_pair_false_of_centralizing_cubic c i z h R hR g hg hgo

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
