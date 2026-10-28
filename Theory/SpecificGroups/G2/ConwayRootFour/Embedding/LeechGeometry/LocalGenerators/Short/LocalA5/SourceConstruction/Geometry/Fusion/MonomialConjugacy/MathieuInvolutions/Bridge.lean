module

public import Theory.SpecificGroups.G2.ConwayRootFour.MarkedLift
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.MonomialConjugacy.MathieuInvolutions.PointStabilizer
/-!
# A Golay-preserving conjugator between the two representatives

The finite stabilizer calculation leaves two representatives. The explicit
permutation below conjugates the second to `coordinateSwap`. Its inverse
is checked on the 24 coordinates, and the images of all twelve Golay basis
words are checked against actual encoder preimages. The resulting
conjugator therefore belongs to the literal Mathieu code group.

The Golay encoder, basis and coordinate action are the attributed ATLAS
ports. This is the remaining finite calculation used by the supporting
Mathieu argument for Aschbacher, *Sporadic Groups* (1994), Lemma 49.5.
-/

@[expose] public section
open Atlas.Codes Atlas.G2.ConwayRootFour
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.MathieuInvolutions
open scoped BigOperators

def pointIndex : Omega ≃ Fin 24 :=
  (Equiv.prodCongr hexIndexEquiv (Equiv.refl (Fin 4))).trans finProdFinEquiv
def bridgeForward : Fin 24 → Fin 24 := ![3,5,1,7,6,0,4,2,18,19,11,10,12,13,20,21,9,8,16,17,22,23,14,15]
def bridgeBackward : Fin 24 → Fin 24 := ![5,2,7,0,6,1,4,3,17,16,11,10,12,13,22,23,18,19,8,9,14,15,20,21]
def bridgePerm : Equiv.Perm Omega :=
  pointIndex.trans ((Equiv.mk bridgeForward bridgeBackward (by decide) (by decide)).trans pointIndex.symm)
def imageHex : Fin 12 → Fin 6 → Bit := ![![1,0,0,0,0,0],![1,0,0,1,0,1],![1,1,1,1,0,1],![1,0,0,0,1,0],![1,0,0,1,0,0],![1,0,0,1,1,1],![0,0,0,0,0,0],![1,0,0,0,0,0],![1,0,0,1,1,0],![1,0,0,0,0,0],![1,0,0,1,1,0],![1,0,1,1,1,0]]
def imageParity : Fin 12 → Fin 5 → Bit := ![![0,0,0,1,0],![1,1,1,0,0],![1,0,1,1,0],![1,0,0,0,1],![1,0,0,1,0],![0,1,0,1,0],![1,0,0,0,0],![0,0,0,0,0],![0,0,1,0,1],![0,1,0,1,0],![0,0,0,0,0],![1,1,0,1,0]]
def imageBit : Fin 12 → Bit := ![0,1,1,0,0,0,0,0,0,0,0,1]
def imageWord (i : Fin 12) : golay :=
  let h : hexacode := ⟨hexEncoder (hexFlatParameters (imageHex i)), ⟨_,rfl⟩⟩
  let r : P6 := ⟨parityEncoder 5 (imageParity i), ⟨_,rfl⟩⟩
  ⟨golayEncoder (h,r,imageBit i), ⟨_,rfl⟩⟩
theorem image_correct : ∀ i, coordinatePermutation bridgePerm (golayGenerators i) = (imageWord i).val := by
  intro i
  funext x
  revert i x
  decide

theorem codePreserving_of_basis (σ : Equiv.Perm Omega)
    (hσ : ∀ i, coordinatePermutation σ (golayGenerators i) ∈ golay) : CodePreserving σ := by
  apply codePreserving_of_forward
  intro w hw
  have he := congrArg (fun v : golay => coordinatePermutation σ v.val) (golayBasis.sum_repr ⟨w,hw⟩)
  rw [← he]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, golayBasis_coe]
  exact golay.sum_mem (fun i _ => golay.smul_mem _ (hσ i))
def bridge : Mathieu24CodeModel :=
  ⟨bridgePerm, codePreserving_of_basis _ (fun i => (image_correct i).symm ▸ (imageWord i).property)⟩
def badTable : Fin 24 → Fin 24 := ![2,3,0,1,6,7,4,5,18,19,16,17,22,23,20,21,10,11,8,9,14,15,12,13]
theorem bridge_equation : ∀ x : Fin 24,
    bridgeForward (badTable x) = pointIndex (coordinateSwap.val (pointIndex.symm (bridgeForward x))) := by decide


theorem bridge_coordinates (x : Omega) :
    pointIndex (bridge.val x) = bridgeForward (pointIndex x) := by
  change pointIndex (pointIndex.symm (bridgeForward (pointIndex x))) = _
  exact pointIndex.apply_symm_apply _

theorem badTable_coordinates : ∀ x : Omega,
    pointIndex ((coordinateSwap * model badIndex).val x) = badTable (pointIndex x) := by
  decide

theorem bad_isConj : IsConj (coordinateSwap * model badIndex) coordinateSwap := by
  have he : bridge * (coordinateSwap * model badIndex) = coordinateSwap * bridge := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply pointIndex.injective
    change pointIndex (bridge.val ((coordinateSwap * model badIndex).val x)) =
      pointIndex (coordinateSwap.val (bridge.val x))
    rw [bridge_coordinates, badTable_coordinates]
    change _ = pointIndex (coordinateSwap.val (pointIndex.symm (bridgeForward (pointIndex x))))
    exact bridge_equation (pointIndex x)
  exact isConj_iff.mpr ⟨bridge, by rw [he]; simp [mul_assoc]⟩

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.MathieuInvolutions
