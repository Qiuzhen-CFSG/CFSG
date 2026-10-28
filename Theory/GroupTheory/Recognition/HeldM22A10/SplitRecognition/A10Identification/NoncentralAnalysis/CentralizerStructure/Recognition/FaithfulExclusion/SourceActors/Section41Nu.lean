module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Relations
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.Commutator

/-!
# The final normalization in Held's Section 4.1

An initial actor satisfying the first paragraph of 4.1 has two possible
conjugation actions on the chosen xi. Section 2.14 makes tau*lambda*xi a
conjugate of pi, whereas the supplied alpha makes xi a conjugate of mu.
The assumed pi--mu nonfusion therefore forces nu to commute with xi.
The construction below also establishes the two required actions on pi*mu
and tau*lambda.

The requested existence theorem still requires construction of the initial
actor and proof of the fusion conclusion for its normalized lambda. They
are explicit inputs here, not consequences asserted by this module. Final
assembly remains in this module once both source obligations are discharged.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 2.13--2.14 and 4.1, pp.231--232.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion

universe u
variable {G : Type u} [Group G] {D : LocalData G}
  {e : D.centralizer ≃* CentralizerModels.a10Centralizer}

/-- Conditional completion of the nu construction from the first paragraph of
4.1 and the fusion conclusion of 2.14. The supplied alpha determines xi. -/
public noncomputable def nuRelationsOfSourceFusion {b d : Bit} [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (a : AlphaRelations D e d) (n : NuSeedRelations D e b)
    (hcross : IsConj D.z (D.a10ModelEmbedding e (coreTau b * normalizedXi d))) :
    NuRelations D e b d :=
  n.toNuRelations (fun h => hfusion ((hcross.trans h.symm).trans a.xi_isConj_mu))

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
