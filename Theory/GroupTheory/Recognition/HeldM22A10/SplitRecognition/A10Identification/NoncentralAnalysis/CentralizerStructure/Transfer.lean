module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.Completion

/-!
# Assembly of Held's intermediate quotient core

The transfer calculation has two inputs: the normalized source fusion
geometry in Q = C_G(mu)/<mu>, and a normal index-four subgroup with the
specified Sylow intersection. From these, this module constructs every
field of `QuotientCore`, including its actual dihedral Sylow equivalence,
trivial odd core, and absence of normal subgroups of index two.

The source existence theorem remains open until both inputs are proved
from D, e and nonfusion. The conditional assembly below neither assumes
nor concludes an A6 recognition statement.

Source: Held, Illinois J. Math. 13 (1969), 224--240, pp.233--234,
DOI 10.1215/ijm/1256053756, proof of Lemma 4.2.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
universe u
open TransferModel (R)

variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

public theorem quotientCore_of_transfer_kernel (F : TransferFusion (Q D e) (CentralizerStructure.p D e))
    (M : Subgroup (Q D e)) [M.Normal] (hM : M.index = 4)
    (hinter : M ⊓ (F.sylow : Subgroup (Q D e)) = R.map F.into) :
    Nonempty (QuotientCore D e) := by
  obtain ⟨S, ⟨equiv⟩, hcentralizer⟩ := F.sylow_structure M hinter
  exact ⟨{
    subgroup := M
    normal := inferInstance
    index := hM
    p_mem := F.p_mem M hinter
    sylow := S
    sylowEquiv := equiv
    centralizer_eq := hcentralizer
    oddCore := F.oddCore_subgroup M
    no_index_two := fun N hN => by
      let := hN
      exact F.no_index_two M hM hinter N
  }⟩

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
