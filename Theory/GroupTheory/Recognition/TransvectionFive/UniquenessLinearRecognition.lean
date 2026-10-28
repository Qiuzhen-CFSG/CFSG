module
public import Theory.GroupTheory.Recognition.TransvectionFive.LocalData
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSystem
public import Theory.GroupTheory.GraphUniquenessSystem.CosetConstruction
public import Theory.GroupTheory.GraphUniquenessSystem.Recognition
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Recognition from the actual linear source geometry

The source comparison retains the literal normalizers of the row, plane and
three-space subgroups pulled back by the marked centralizer. Its graph is the
collinearity graph of their cosets; its local maps are compatible in the precise
sense of a graph uniqueness-system equivalence. The concrete SL₅(2) target,
its simplicity, and its cycle base extend those local maps to a unique ambient
isomorphism.

This is a conditional reconstruction theorem. Constructing `SourceComparison`
from `PointCoreFusion` and the two 21-element fusion sets remains the source
obligation of §§40.3–41.4. In particular no conclusion about an arbitrary marked
centralizer follows merely from the definitions here. Final source assembly
is owned by `qt-d-12213-four-uniqueness-linear-source`.
Source: Aschbacher, *Sporadic Groups* (1994), 37.6, Example 38.4 and 41.4–41.6,
pp.200,206–207,222.
-/

public noncomputable section
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open BinaryLinear.TransvectionFiveLocal Subgroup GraphUniquenessSystem
universe u
variable {G : Type u} [Group G] {z : G}

/-- The actual source coset geometry and its compatible local comparisons.
Existence must be derived from the source fusion hypotheses. -/
structure SourceComparison (F : MarkedCentralizer z) where
  source : System G (Cosets.Vertex (normalizer (F.row : Set G)))
  source_point : source.x = Cosets.vertex (normalizer (F.row : Set G)) 1
  source_local : source.H = normalizer (F.threeSpace : Set G)
  source_graph : ∀ a b, source.graph.Adj a b ↔
    Cosets.Collinear (normalizer (F.row : Set G)) (normalizer (F.plane : Set G)) a b
  similarity : Similarity source nativeSystem.system
  equivalent : similarity.IsEquivalence

/-- Simplicity of the literal binary special linear target. -/
theorem model_simple : IsSimpleGroup SL := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  exact (BinaryLinear.OuterCyclic.projectiveEquivSL (n := 5) (by decide)).symm.isSimpleGroup

namespace SourceComparison
variable {F : MarkedCentralizer z} (C : SourceComparison F)

/-- The source vertex stabilizer is the literal row normalizer. -/
theorem vertexGroup_eq : C.source.vertexGroup = normalizer (F.row : Set G) := by
  change MulAction.stabilizer G C.source.x = _
  rw [C.source_point, Cosets.stabilizer_base]

/-- The proved target base extends the actual local comparisons to an ambient isomorphism.
This is conditional on constructing `SourceComparison`, not a proof of 41.6 by itself. -/
theorem existsUnique_equiv : ∃! e : G ≃* SL,
    (∀ a : C.source.vertexGroup, e a = (C.similarity.vertexIso a : SL)) ∧
    (∀ a : C.source.H, e a = (C.similarity.localIso a : SL)) := by
  let := model_simple
  exact C.similarity.existsUnique_mulEquiv_of_isEquivalence_of_isBase
    C.equivalent nativeSystem_isBase

include C in
/-- Recognition once the source normalizer geometry and comparisons have been constructed. -/
theorem nonempty_equiv : Nonempty (G ≃* SL) :=
  let ⟨e, _, _⟩ := C.existsUnique_equiv
  ⟨e⟩
end SourceComparison
end Theory.GroupTheory.TransvectionFive.UniquenessLinear
