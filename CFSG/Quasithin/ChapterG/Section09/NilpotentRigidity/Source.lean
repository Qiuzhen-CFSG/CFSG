module

public import CFSG.Quasithin.ChapterG.Section08.Applications
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
public import Theory.Representation.BinaryDihedralSplitting.Halves

/-!
# The original nilpotent-action rigidity theorem

The proved G.8 extraction supplies the actual dihedral factors. The binary
dihedral splitting is applied to the literal rotation and its two conjugate
reflection halves, discharging the last earlier input to G.9.2. The complete
internal group and module decompositions, including rank zero, follow with
no extraction, splitting, degree or recognition assumption.

Source: Aschbacher--Smith G.9.2, printed pp.351--353.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
universe u v

/-- A.1.44 in the exact half-space convention used by G.9.2. -/
theorem dihedralSplittingTheorem : DihedralSplittingTheorem.{v} := by
  intro W _ _ _ p hp ho σ _
  exact Representation.BinaryDihedralSplitting.rotation_reflection_halves p hp ho σ

/-- All original G.9.2 conclusions with the earlier source inputs discharged. -/
theorem source_lemma_G_9_2
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {A X : Subgroup G} {m : ℕ}
    (h : Hypothesis ρ A X m) : Conclusion ρ A X m :=
  conclusion_of_extraction_and_splitting h h.dihedralExtraction dihedralSplittingTheorem

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
