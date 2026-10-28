module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinear
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceRecognition

/-!
# Uniqueness for the two surviving transvection fusion types

For a finite simple group with a marked full transvection centralizer and
point-core fusion, the 21/21 and 21/45 fusion patterns recognize the actual
groups SL₅(2) and M₂₄, respectively. The two source constructions derive
their ambient normalizers and compatible uniqueness systems from these
counts; the Mathieu construction uses the native 759-octad geometry.

This pairs the proved source branches without adding a normalizer,
generation or graph-comparison premise. It is the uniqueness input for
the dimension-four recognition argument.

Source: Aschbacher, *Sporadic Groups* (1994), 40.3–40.5 and 41.1–41.6,
pp.217–222.
-/

public section
namespace Theory.GroupTheory.TransvectionFive
variable {G : Type*} [Group G] [Finite G]

/-- Both source uniqueness implications, with their original finite-simple,
marked-centralizer and point-core-fusion hypotheses. -/
theorem uniqueness_of_fusion (hG : IsSimpleGroup G) (z : G)
    (F : MarkedCentralizer z) (hcore : PointCoreFusion z) :
    (F.LinearFusion → Nonempty (G ≃* BinaryLinear.TransvectionFiveLocal.SL)) ∧
    (F.MathieuFusion → Nonempty (G ≃* Sporadic.Mathieu.M24)) :=
  ⟨linear_of_linearFusion F hG hcore, mathieu_of_mathieuFusion_source F hG hcore⟩

end Theory.GroupTheory.TransvectionFive
