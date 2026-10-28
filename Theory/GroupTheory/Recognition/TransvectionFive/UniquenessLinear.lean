module

public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSecondLocal

/-!
# Recognition of the linear transvection-centralizer branch

The two 21-element fusion sets determine the full row and rectangle
normalizers. Their compatible local maps give a uniqueness system on the
literal row-normalizer cosets, with lines the plane-normalizer cosets.
The second-centralizer argument proves ambient generation, and the binary
matrix cycle base extends the local comparison to an isomorphism with SL₅(2).

This assembles the linear case of Aschbacher, *Sporadic Groups* (1994),
40.3, 40.5(1), and 41.1–41.6, pp.217–222. The public source statement retains
finite simplicity and point-core fusion; the proved comparison construction
already follows from the marked full centralizer and the two fusion counts.
No local-data, generation, or graph-comparison premise remains.
-/

public section
namespace Theory.GroupTheory.TransvectionFive
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The linear source fusion pattern recognizes the actual binary degree-five
special linear group. All normalizer and uniqueness-system inputs are proved
from the original marking and fusion counts. -/
theorem linear_of_linearFusion (F : MarkedCentralizer z)
    (_hG : IsSimpleGroup G) (_hcore : PointCoreFusion z) :
    F.LinearFusion → Nonempty (G ≃* BinaryLinear.TransvectionFiveLocal.SL) := by
  intro hlinear
  obtain ⟨C⟩ := UniquenessLinear.nonempty_sourceComparison F hlinear
  exact C.nonempty_equiv

end Theory.GroupTheory.TransvectionFive
