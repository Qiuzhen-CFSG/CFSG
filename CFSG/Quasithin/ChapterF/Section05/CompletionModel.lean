module

public import CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
public import Theory.SpecificGroups.OmegaSixThree.ModelComparison

/-!
# F.5 completion recognition with the concrete model comparison discharged

The diagonal orthogonal commutator group is PSL₄(3), and is simple. Applying
these proved facts to the original completion removes both model premises
from the uniqueness-system argument. The source and model systems, their
equivalence, the triangle orbit and the marked vertex group remain genuine
inputs of the earlier F.5 geometry.

Source: Aschbacher--Smith F.5, final paragraph, printed p.304.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.CompletionRecognition

open Theory.GroupTheory Theory.GroupTheory.GraphUniquenessSystem
open GreenBook.LieModels.UnitaryFour
open OmegaSixThree.OrthogonalityGraph

local notation "hn" => Nat.le_refl 1
local notation "Model" => OmegaSixThree.omegaPlusSixThree
local notation "PSL" => Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)

variable {G G0 : Type*} [Group G] [Group G0]

/-- The ambient conclusion needed by 13.5.17 does not require a separate
identification of the embedded completion's vertex stabilizer. -/
theorem source_ambient_of_geometric_equivalence
    (i : G0 →* G)
    (U : System Model Point) (hgraph : U.graph = graph)
    (W : System G (G ⧸ i.range))
    (s : Similarity U W) (hs : s.IsEquivalence)
    (T : U.LocalTriangle) (ht : T.IsTriangleOrbit) :
    Nonempty (G ≃* PSL) := by
  let _ := OmegaSixThree.omega_simple
  obtain ⟨e, _, _⟩ := GraphRecognition.existsUnique_equiv hgraph s hs T ht
  exact ⟨e.symm.trans OmegaSixThree.omegaEquivPSL⟩

/-- The actual F.5 consumer, with model identification and simplicity proved. -/
theorem source_conclusion_of_geometric_equivalence
    (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
    (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
    (U : System Model Point) (hgraph : U.graph = graph)
    (W : System G (G ⧸ i.range)) (hx : W.x = QuotientGroup.mk (1 : G))
    (s : Similarity U W) (hs : s.IsEquivalence)
    (T : U.LocalTriangle) (ht : T.IsTriangleOrbit)
    (eVertex : U.vertexGroup ≃* Extension.ProjectiveExtension 1 hn) :
    Nonempty (G ≃* PSL) ∧ Nonempty (G0 ≃* Extension.ProjectiveExtension 1 hn) := by
  let _ := OmegaSixThree.omega_simple
  exact source_conclusion_of_system_equivalence c i z h U hgraph W hx s hs T ht
    OmegaSixThree.omegaEquivPSL eVertex

end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
