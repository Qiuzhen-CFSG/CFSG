module

public import CFSG.Quasithin.ChapterF.Section05.Source
public import CFSG.Quasithin.ChapterF.Section05.GraphRecognition
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# The F.5 geometric argument applied to the original completion

The source vertices are the actual cosets M/M₀, with M₀ the range of the
given embedding. An equivalence of uniqueness systems identifies M with the
concrete orthogonal model, while its vertex comparison identifies the given
completion M₀ with the model vertex stabilizer. The two concrete model
isomorphisms then yield the two group identifications in F.4.37(4)(ii).

This conditional assembly consumes the proved graph contraction. It keeps
F.5.1--2 model marking, F.5.4--6 source-system construction, F.5.7 equivalence,
F.5.8(1) triangle conjugacy, and the actual Ω₆⁺(3) ≃ PSL₄(3) comparison
explicit. Those premises must all be constructed before asserting F.4.31.

Source: Aschbacher--Smith, final paragraph of F.5, printed p.304.
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

/-- Conditional F.4.37(4)(ii) for the original embedded completion.
Simple connectivity and the identification of its coset stabilizer are
discharged internally; the remaining source and model constructions are explicit. -/
theorem source_conclusion_of_system_equivalence [IsSimpleGroup Model]
    (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
    (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
    (U : System Model Point) (hgraph : U.graph = graph)
    (W : System G (G ⧸ i.range)) (hx : W.x = QuotientGroup.mk (1 : G))
    (s : Similarity U W) (hs : s.IsEquivalence)
    (T : U.LocalTriangle) (ht : T.IsTriangleOrbit)
    (eModel : Model ≃* PSL)
    (eVertex : U.vertexGroup ≃* Extension.ProjectiveExtension 1 hn) :
    Nonempty (G ≃* PSL) ∧ Nonempty (G0 ≃* Extension.ProjectiveExtension 1 hn) := by
  obtain ⟨e, _, _⟩ := GraphRecognition.existsUnique_equiv hgraph s hs T ht
  have hvertex : W.vertexGroup = i.range := by
    change MulAction.stabilizer G W.x = i.range
    rw [hx]
    exact MulAction.stabilizer_quotient i.range
  let e0 : G0 ≃* W.vertexGroup :=
    (MonoidHom.ofInjective h.embedding_injective).trans (MulEquiv.subgroupCongr hvertex.symm)
  exact ⟨⟨e.symm.trans eModel⟩, ⟨e0.trans (s.vertexIso.symm.trans eVertex)⟩⟩

end CFSG.Quasithin.ChapterF.Section05.CompletionRecognition
