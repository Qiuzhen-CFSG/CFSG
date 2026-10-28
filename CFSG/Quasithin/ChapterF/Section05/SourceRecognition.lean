module
public import CFSG.Quasithin.ChapterF.Section05.SourceCyclicRecognition
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerNonElementary
/-!
# The original exceptional binary unitary source theorem

Choose a Sylow overgroup of the graph-fixed upper subgroup. The elementary
R₀ alternative is excluded by the actual pair of elementary-sixteen groups
and their normalizer quotients. The cyclic-four root and the fixed-endpoint
involution pair therefore supply every input to the marked-amalgam recognition.
Thus the original source hypotheses identify the ambient group with PSL₄(3),
with no additional local, recognition or geometric premise.

Source: Aschbacher–Smith F.5.5–8, printed pp.301–304.
-/
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05
open Subgroup Theory.GroupTheory GreenBook.LieModels.UnitaryFour
open ExceptionalLocal
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
  (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
include h

theorem source_ambient_equiv :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) := by
  obtain ⟨S,hS⟩:=source_sylowImage_isSylow c i z h
  have hT:IsPGroup 2 (Source.sylowImage c i):=hS ▸ S.isPGroup'
  obtain ⟨R,hR⟩:=(show IsPGroup 2 (Tf c i) from hT.comap_subtype).exists_le_sylow
  exact source_ambient_of_Rzero_not_elementary c i z h R hR
    (source_Rzero_not_elementary c i z h R hR)

end CFSG.Quasithin.ChapterF.Section05
