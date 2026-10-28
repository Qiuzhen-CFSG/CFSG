module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Pair

/-!
# The noninner pair automorphism extends to the sixteen-field model

Coefficient square Frobenius commutes with the fourth-power field actor and
therefore acts on the whole PSL₂(16):2 model. On its literal pair subgroup it
squares the order-fifteen torus and fixes both involutory actors. In the
dihedral coordinates this squares both rotations and fixes both reflections.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open BenderSuzuki.Converse Theory.PSL2 Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam

def squareField : F ≃+* F := iterateFrobeniusEquiv F 2 1

theorem squareField_apply (x : F) : squareField x = x ^ 2 :=
  iterateFrobeniusEquiv_def _ 2 1 x

/-- Coefficient square Frobenius on the full fourth-power extension. -/
def squareModel : MulAut Model :=
  SemidirectProduct.congr (fieldAut squareField) (MulEquiv.refl Actor) (by
    intro a
    have hc : Commute squareField a.val := by
      apply RingEquiv.ext
      intro x
      change squareField (a.val x) = a.val (squareField x)
      rw [squareField_apply, squareField_apply, map_pow]
    apply MulEquiv.ext
    intro x
    exact congrArg (fun v : MulAut (BinaryGroup 4) => v x) ((hc.map fieldAutHom).eq))

theorem squareModel_inr (a : Actor) :
    squareModel (SemidirectProduct.inr a) = SemidirectProduct.inr a := by
  apply SemidirectProduct.ext
  · exact map_one _
  · rfl

theorem squareModel_torus (u : Fˣ) :
    squareModel (linearInclusion (torusHom u)) = linearInclusion (torusHom (u ^ 2)) := by
  apply SemidirectProduct.ext
  · change fieldAut squareField (quotientMap F (tor u)) = quotientMap F (tor (u ^ 2))
    rw [fieldAut_apply_quotientMap]
    apply congrArg (quotientMap F)
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.map_apply_coe, tor_val, squareField_apply]
  · rfl

theorem squareModel_swap : squareModel swap = swap := by
  apply SemidirectProduct.ext
  · change fieldAut squareField (quotientMap F (weyl F)) = quotientMap F (weyl F)
    rw [fieldAut_apply_quotientMap]
    apply congrArg (quotientMap F)
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.map_apply_coe, weyl_val]
  · rfl

private theorem squareModel_swapHom (a : CyclicCoordinates.Two) :
    squareModel (swapHom a) = swapHom a := by
  rcases two_cases a with rfl | rfl
  · rw [map_one,map_one]
  · rw [swapHom_generator,squareModel_swap]

private theorem squareModel_torusLift (x : Fˣ ⋊[unitsAction] Actor) :
    squareModel (torusLift x) = torusLift ⟨x.left ^ 2,x.right⟩ := by
  rw [torusLift_eq,torusLift_eq,map_mul,squareModel_torus,squareModel_inr]

/-- Rotation squaring in the order-sixty coordinates. Its inverse uses exponent eight. -/
def coordinateSquare : MulAut CyclicCoordinates.Normalizer where
  toFun x := ⟨⟨x.left.left ^ 2,x.left.right⟩,x.right⟩
  invFun x := ⟨⟨x.left.left ^ 8,x.left.right⟩,x.right⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

/-- The actual matrix automorphism realizes rotation squaring on the full pair subgroup. -/
theorem squareModel_pairLift (x : CyclicCoordinates.Normalizer) :
    squareModel (pairLift x) = pairLift (coordinateSquare x) := by
  obtain ⟨l,r⟩ := x
  obtain ⟨t,rfl⟩ := torusCoordinates.surjective l
  change squareModel (torusLift (torusCoordinates.symm (torusCoordinates t)) * swapHom r) =
    torusLift (torusCoordinates.symm
      ⟨(torusCoordinates t).left ^ 2,(torusCoordinates t).right⟩) * swapHom r
  have hco : (⟨(torusCoordinates t).left ^ 2,(torusCoordinates t).right⟩ :
      CyclicCoordinates.AffineTorus) = torusCoordinates ⟨t.left ^ 2,t.right⟩ := by
    apply SemidirectProduct.ext
    · exact (map_pow unitsEquiv t.left 2).symm
    · rfl
  rw [hco,torusCoordinates.symm_apply_apply,torusCoordinates.symm_apply_apply,
    map_mul,squareModel_torusLift,squareModel_swapHom]

/-- The full literal pair subgroup is invariant under coefficient square Frobenius. -/
theorem squareModel_pair : pair.map squareModel.toMonoidHom = pair := by
  rw [←pairLift_range]
  apply le_antisymm
  · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    exact ⟨coordinateSquare x,(squareModel_pairLift x).symm⟩
  · rintro _ ⟨x,rfl⟩
    refine ⟨pairLift (coordinateSquare.symm x),⟨_,rfl⟩,?_⟩
    change squareModel (pairLift (coordinateSquare.symm x)) = pairLift x
    rw [squareModel_pairLift,coordinateSquare.apply_symm_apply]

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
