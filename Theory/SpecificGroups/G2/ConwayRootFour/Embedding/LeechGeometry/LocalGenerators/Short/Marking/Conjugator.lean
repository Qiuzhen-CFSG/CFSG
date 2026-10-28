module

public import Theory.SpecificGroups.G2.ConwayRootFour.MarkedLift

/-!
# A signed Golay permutation for the scalar marking

The displayed permutation preserves the Golay code: its images on the twelve
published basis vectors are certified by explicit encoder parameters. Combining
it with the displayed Golay sign gives a genuine integral Leech isometry.
`Marking.ScalarAction` checks that this isometry intertwines inverse right
multiplication by the icosian unit i with the literal `markedLift`.

This is the coordinate marking needed for the root-four fusion in Aschbacher,
*Sporadic Groups* (1994), pp.269 and 283–284 (Lemma 49.5). The code, its basis,
and the lattice isometries are the attributed ATLAS constructions already
imported by `MarkedLift`; the permutation and certificates here are new.
-/

@[expose] public section
open Atlas.Codes Atlas.Lattices Atlas.Conway
open Atlas.G2.ConwayRootFour
open scoped BigOperators Matrix
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Marking

def coordinateIndex : Omega ≃ Fin 24 :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

def permData : Equiv.Perm (Fin 24) where
  toFun := ![0,2,4,5,7,6,1,3,8,11,20,22,21,23,10,9,16,19,12,14,13,15,18,17]
  invFun := ![0,6,1,7,2,3,5,4,8,15,14,9,18,20,19,21,16,23,22,17,10,12,11,13]
  left_inv := by decide
  right_inv := by decide

def markingPerm : Equiv.Perm Omega :=
  coordinateIndex.trans (permData.trans coordinateIndex.symm)

def encodedWord (t : Fin 12 → Bit) : golay :=
  ⟨golayEncoder (⟨hexEncoder (![t 0,t 1,t 2], ![t 3,t 4], t 5), ⟨_, rfl⟩⟩,
    ⟨parityEncoder 5 ![t 6,t 7,t 8,t 9,t 10], ⟨_, rfl⟩⟩, t 11), ⟨_, rfl⟩⟩

def generatorImages : Fin 12 → golay := fun i => encodedWord
  (![![1,1,1,0,1,1,0,0,1,0,1,0],
    ![0,1,0,0,1,0,1,0,1,0,0,0],
    ![0,0,1,1,0,0,1,0,0,0,1,0],
    ![0,0,1,0,1,1,1,0,0,0,1,0],
    ![0,1,0,0,1,1,1,0,1,0,0,0],
    ![0,0,1,0,1,1,1,1,0,1,0,1],
    ![0,0,0,0,0,0,1,0,0,0,0,0],
    ![0,0,1,0,1,1,1,1,0,0,1,0],
    ![0,0,1,0,1,1,1,0,0,0,0,0],
    ![0,1,0,0,1,1,1,0,1,1,0,0],
    ![0,1,0,0,1,1,1,0,0,0,0,0],
    ![1,1,0,1,0,1,1,0,1,0,0,1]] i)

private theorem generator_images (i : Fin 12) :
    coordinatePermutation markingPerm (golayGenerators i) = (generatorImages i).val := by
  revert i
  decide +kernel

theorem markingPerm_preserves : CodePreserving markingPerm := by
  apply codePreserving_of_forward
  intro w hw
  have he := congrArg Subtype.val (golayBasis.sum_repr (⟨w,hw⟩ : golay))
  change (∑ i, (golayBasis.repr ⟨w,hw⟩) i • (golayBasis i : BinaryWord)) = w at he
  rw [← he, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul, golayBasis_coe, generator_images]
  exact golay.smul_mem _ (generatorImages i).property

def markingCodePerm : Mathieu24CodeModel := ⟨markingPerm, markingPerm_preserves⟩
def markingSign : golay := encodedWord ![0,0,1,1,0,0,0,0,0,0,0,1]

noncomputable def markingConjugator : LeechIsometryGroup :=
  signIsometry markingSign * permutationIsometry markingCodePerm

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Marking
