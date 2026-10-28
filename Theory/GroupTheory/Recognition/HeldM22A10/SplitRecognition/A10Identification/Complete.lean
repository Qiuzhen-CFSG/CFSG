module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.TauFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Tau

/-!
# The alternating branch of Held's recognition theorem

The initial fusion analysis constructs pi--tau fusion from the original
finite simple local data. The resulting noncentral alternating-six section
and corrected six/seven local geometry construct an actual alternating-ten
overgroup, which simplicity identifies with the whole group.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240, Section 2,
DOI 10.1215/ijm/1256053756.
-/

namespace Theory.GroupTheory.HeldM22A10

universe u

/-- The alternating local centralizer determines the actual ambient A10 group.
All fusion, section and overgroup premises are produced from the local data. -/
public theorem a10Identification_of_centralizer
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer) :
    Nonempty (G ≃* alternatingGroup (Fin 10)) :=
  a10Identification_of_tau_fusion D e
    (A10Identification.NoncentralAnalysis.Fusion.tau_fusion_of_simple D e)

end Theory.GroupTheory.HeldM22A10
