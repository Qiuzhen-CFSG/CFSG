module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Pair

/-!
# The pair-centralizer intersection in the model amalgam

The pair-stabilizer equivalence carries the actual fourth-power field
involution to a reflection in its D₁₀ factor. Its centralizer in S₃ × D₁₀
is therefore S₃ × C₂. The equivalence below is on the literal intersection
of the pair subgroup with C_H(f), preserving the ambient involution.

Source: Baumeister, *A geometry for groups of J₃-type* (2007), p.498,
the model instance of Lemma 2.7(iii) used in Corollary 2.10.
-/

public noncomputable section
open Subgroup MulAction Matrix
open BenderSuzuki.Converse Theory.PSL2 Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam

def fieldCoordinate : CyclicCoordinates.Normalizer :=
  SemidirectProduct.inl ⟨1, twoGenerator⟩

theorem pairLift_fieldCoordinate : pairLift fieldCoordinate = involution := by
  change SemidirectProduct.lift _ _ _ (SemidirectProduct.inl _) = _
  rw [SemidirectProduct.lift_inl]
  change torusLift (torusCoordinates.symm ⟨1, twoGenerator⟩) = _
  have hc : torusCoordinates ⟨1, actorGenerator⟩ = ⟨1, twoGenerator⟩ := by
    apply SemidirectProduct.ext
    · exact unitsEquiv.map_one
    · exact actorEquiv_generator
  rw [← hc, torusCoordinates.symm_apply_apply]
  apply SemidirectProduct.ext
  · exact torusHom.map_one
  · rfl

theorem pairEquiv_pairLift (x : CyclicCoordinates.Normalizer) :
    pairEquiv ⟨pairLift x, pairLift_range ▸ ⟨x,rfl⟩⟩ = CyclicCoordinates.pairEquiv x := by
  let e := (MonoidHom.ofInjective pairLift_injective).trans
    (MulEquiv.subgroupCongr pairLift_range)
  change CyclicCoordinates.pairEquiv (e.symm (e x)) = _
  rw [e.symm_apply_apply]

def involutionInPair : pair := ⟨involution, involution_mem_overlap.2⟩

theorem pairEquiv_involution : pairEquiv involutionInPair = (1, DihedralGroup.sr 0) := by
  have h := pairEquiv_pairLift fieldCoordinate
  have he : (⟨pairLift fieldCoordinate, pairLift_range ▸ ⟨fieldCoordinate,rfl⟩⟩ : pair) =
      involutionInPair := Subtype.ext pairLift_fieldCoordinate
  rw [he] at h
  exact h.trans (by decide +kernel)

private def centralizerTransport {A B : Type*} [Group A] [Group B] (e : A ≃* B) (s : A) :
    centralizer ({s} : Set A) ≃* centralizer ({e s} : Set B) where
  toFun x := ⟨e x, mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul]
    exact congrArg e (mem_centralizer_singleton_iff.mp x.property))⟩
  invFun y := ⟨e.symm y, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (e.map_mul _ _)

def pairIntersectionCentralizer : (pair ⊓ Triangle : Subgroup Model) ≃*
    centralizer ({involutionInPair} : Set pair) where
  toFun x := ⟨⟨x, x.property.1⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
  invFun y := ⟨y.val, ⟨y.val.property, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp y.property))⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def standardCentralizerHom : (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) →*
    (Equiv.Perm (Fin 3) × DihedralGroup 5) where
  toFun x := (x.1, if x.2 = 1 then 1 else DihedralGroup.sr 0)
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem standardCentralizerHom_injective : Function.Injective standardCentralizerHom := by
  decide +kernel

theorem standardCentralizerHom_range : standardCentralizerHom.range =
    centralizer ({(1, DihedralGroup.sr 0)} : Set (Equiv.Perm (Fin 3) × DihedralGroup 5)) := by
  ext x
  rw [MonoidHom.mem_range, mem_centralizer_singleton_iff]
  revert x
  decide +kernel

def standardCentralizerEquiv :
    centralizer ({(1, DihedralGroup.sr 0)} : Set (Equiv.Perm (Fin 3) × DihedralGroup 5)) ≃*
      (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) :=
  ((MonoidHom.ofInjective standardCentralizerHom_injective).trans
    (MulEquiv.subgroupCongr standardCentralizerHom_range)).symm

def overlap23 : (pair ⊓ Triangle : Subgroup Model) ≃*
    (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)) :=
  pairIntersectionCentralizer.trans ((centralizerTransport pairEquiv involutionInPair).trans
    ((MulEquiv.subgroupCongr (congrArg (fun t => centralizer ({t} : Set _)) pairEquiv_involution)).trans
      standardCentralizerEquiv))

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
