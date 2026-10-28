module

public import Theory.GroupTheory.Recognition.HeldM22A10.Setup
public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.CentralizerModels
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.JankoModel
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationData

/-!
# The M22 branch of involution-centralizer recognition

The terminal group in Janko's 1968 proof is identified with the genuine
Steiner-design carrier by explicit checked words. A faithful action whose
image is conjugate to that terminal group therefore identifies its group
with the Steiner carrier.

Recognition from `LocalData` and the supplied concrete centralizer equivalence
remains open. The remaining obligations are the ambient order and Sylow
3-normalizer calculation (Janko Sections 2--7), construction of the action
specified in `PermutationData` (Sections 7--8), and the final permutation
classification (Section 9). Neither that action nor its image is assumed in
the intended centralizer-recognition statement.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification

universe u

/-- Turn the final conjugacy of faithful action images into a concrete group
equivalence. The existence of this conjugacy remains a separate obligation. -/
public noncomputable def equivM22OfRangeConjugacy
    {G : Type u} [Group G] (rho : G →* Equiv.Perm (Fin 22))
    (hfaithful : Function.Injective rho) (p : Equiv.Perm (Fin 22))
    (hp : rho.range.map (MulAut.conj p).toMonoidHom = JankoModel.model) :
    G ≃* Sporadic.Mathieu.M22 :=
  (MonoidHom.ofInjective hfaithful).trans
    (((MulAut.conj p).subgroupMap rho.range).trans
      ((MulEquiv.subgroupCongr hp).trans JankoModel.equivM22))

end Theory.GroupTheory.HeldM22A10.M22Identification
