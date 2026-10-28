module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularLines
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalGeneration

/-!
# The root closure inside a singular-line stabilizer

Take the normal closure of the first simple root group inside the stabilizer
of the first singular line. Its image in Spin is contained in that stabilizer
and normal there. It contains a nonidentity root element, so its ambient
normal closure is all of Spin by the proved root-normal-generation theorem.

Commutativity is a separate geometric obligation: the closure must be shown
to lie in the abelian group of Siegel transformations in the fixed singular
direction. The definition does not presume that fact. In particular, normality
here is relative to the line stabilizer, not ambient normality in Spin.
Source: the classical type-D argument underlying GLS3, 1.10.1(b),
`refs/KGroup/GLS3/Chapter1.tex`.
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.NormalRootExtraction
open Theory.AlgebraicGroup Pinning
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The stabilizer of the specified singular line under the natural action. -/
abbrev lineStabilizer : Subgroup (Points k) := MulAction.stabilizer (Points k) (baseLine k)

theorem firstRoot_le_lineStabilizer : rootPointSubgroup k (simpleRoot 0) ≤ lineStabilizer k := by
  rintro g ⟨a, rfl⟩
  exact positiveSimplePoint_zero_fixes_baseLine k a.toAdd

/-- Normal closure taken in the line stabilizer itself. -/
def stabilizerRootClosure : Subgroup (lineStabilizer k) :=
  Subgroup.normalClosure
    ((rootPointSubgroup k (simpleRoot 0)).subgroupOf (lineStabilizer k) : Set (lineStabilizer k))

/-- The image of the relative normal closure in the ambient Spin group. -/
def lineRootClosure : Subgroup (Points k) :=
  (stabilizerRootClosure k).map (lineStabilizer k).subtype

theorem lineRootClosure_le_stabilizer : lineRootClosure k ≤ lineStabilizer k :=
  Subgroup.map_subtype_le _

theorem lineRootClosure_normal_in_stabilizer :
    ((lineRootClosure k).subgroupOf (lineStabilizer k)).Normal := by
  change (((stabilizerRootClosure k).map (lineStabilizer k).subtype).comap
    (lineStabilizer k).subtype).Normal
  rw [Subgroup.comap_map_eq_self_of_injective (lineStabilizer k).subtype_injective]
  exact Subgroup.normalClosure_normal

theorem positiveSimplePoint_zero_mem_lineRootClosure (a : k) :
    positiveSimplePoint k 0 a ∈ lineRootClosure k := by
  refine ⟨⟨positiveSimplePoint k 0 a, positiveSimplePoint_zero_fixes_baseLine k a⟩,
    Subgroup.subset_normalClosure ?_, rfl⟩
  exact ⟨Multiplicative.ofAdd a, rfl⟩

theorem lineRootClosure_normalClosure_eq_top :
    Subgroup.normalClosure (lineRootClosure k : Set (Points k)) = ⊤ := by
  apply normal_eq_top_of_rootPoint_mem k _ inferInstance (simpleRoot 0) 1 one_ne_zero
  exact Subgroup.subset_normalClosure (positiveSimplePoint_zero_mem_lineRootClosure k 1)

end Triality.SimplyConnected.NormalRootExtraction
