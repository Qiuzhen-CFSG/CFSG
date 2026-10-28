module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusData
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SplitTorus

/-!
# Positive coroot coordinates for the binary Ree spectrum

The product of the four positive coroot words is the split-torus morphism
at the inverse tuple of diagonal parameters. Comparing the literal matrix
coroot words proves this identity, including its sign. Consequently the
coroot product is an injective group homomorphism and parametrizes precisely
the split torus. Conjugacy of a binary Ree element to this product preserves
the order of the entire parameter tuple through the actual coefficient map.

These results supply the coordinate and order transfers for the torus-placement
and finite-spectrum steps of Guralnick--Malle II, Lemma 8.8 (internal p.57).
The torus conventions are those of GLS3, Sections 1.12 and 1.14, and of
`BasicWeights`. No semisimple containment or Ree spectrum is asserted here.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4.BinaryDegree.ExceptionalTensor
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage
variable {F : Type*} [Field F] [IsAlgClosed F]

noncomputable def diagonalPointEquiv :
    Variety.Point (dVariety F 4) ≃* (Fin 4 → Fˣ) :=
  { dPointEquiv 4 with map_mul' := dPointEquiv_mul 4 }

noncomputable def positiveTorusHom :
    (Fin 4 → Fˣ) →* Variety.Point (F4Chevalley.Carrier (k := F)) where
  toFun t := F4Chevalley.splitTorusMorphism.onPoints
    ((diagonalPointEquiv (F := F)).symm (t⁻¹))
  map_one' := by simp
  map_mul' u v := by simp only [mul_inv, map_mul]

theorem positiveTorusHom_single (i : Fin 4) (t : Fˣ) :
    positiveTorusHom (Pi.mulSingle i t) =
      algebraicCorootElement (typeF4SimpleRootIndex i) t := by
  apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
  change (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
    (F4Chevalley.splitTorusMorphism.onPoints
      ((diagonalPointEquiv (F := F)).symm ((Pi.mulSingle i t)⁻¹))) = _
  rw [F4Chevalley.splitTorusMorphism_inclusion_apply,
    F4Chevalley.torusAmbientMorphism_matrix, algebraicCorootElement_ambient,
    F4Chevalley.matrixH_simple]
  apply congrArg F4Chevalley.matrixToAmbient
  change F4Chevalley.torusElement ((Pi.mulSingle i t)⁻¹) = _
  have hp : F4Chevalley.torusParameter ((Pi.mulSingle i t)⁻¹) =
      RootPairing.IntegralGeckConstruction.integralChevalleySimpleCorootParameter
        (typeF4RootPairing_baseEquiv i) t⁻¹ := by
    funext q
    simp only [F4Chevalley.torusParameter,
      RootPairing.IntegralGeckConstruction.integralChevalleySimpleCorootParameter,
      Pi.inv_apply, Pi.mulSingle_apply, Equiv.symm_apply_eq]
    split_ifs <;> simp
  exact congrArg (RootPairing.IntegralGeckConstruction.integralChevalleyTorusElement
    (P := typeF4RootPairing)) hp

theorem positiveTorusHom_eq (t : Fin 4 → Fˣ) :
    positiveTorusHom t = corootTorusElement t := by
  have he : t = Pi.mulSingle 0 (t 0) * Pi.mulSingle 1 (t 1) *
      Pi.mulSingle 2 (t 2) * Pi.mulSingle 3 (t 3) := by
    funext i
    fin_cases i <;> simp
  conv_lhs => rw [he]
  simp only [map_mul, positiveTorusHom_single, corootTorusElement]

theorem corootTorusElement_injective :
    Function.Injective (corootTorusElement (F := F)) := by
  intro t u h
  rw [← positiveTorusHom_eq, ← positiveTorusHom_eq] at h
  have he := F4Chevalley.splitTorusMorphism_injective h
  have hi := (diagonalPointEquiv (F := F)).symm.injective he
  exact inv_injective hi

theorem corootTorusElement_one : corootTorusElement (1 : Fin 4 → Fˣ) = 1 := by
  rw [← positiveTorusHom_eq, map_one]

theorem corootTorusElement_pow (t : Fin 4 → Fˣ) (n : ℕ) :
    corootTorusElement (t ^ n) = corootTorusElement t ^ n := by
  simp only [← positiveTorusHom_eq, map_pow]

theorem orderOf_corootTorusElement (t : Fin 4 → Fˣ) :
    orderOf (corootTorusElement t) = orderOf t := by
  rw [← positiveTorusHom_eq]
  apply orderOf_injective
  intro u v h
  apply corootTorusElement_injective
  simpa only [positiveTorusHom_eq] using h

theorem mem_splitTorus_iff (g : Variety.Point (F4Chevalley.Carrier (k := F))) :
    g ∈ F4Chevalley.splitTorus (k := F) ↔ ∃ t, corootTorusElement t = g := by
  change (∃ x, F4Chevalley.splitTorusMorphism.onPoints x = g) ↔ _
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(diagonalPointEquiv x)⁻¹, ?_⟩
    rw [← positiveTorusHom_eq]
    change F4Chevalley.splitTorusMorphism.onPoints
      (diagonalPointEquiv.symm (((diagonalPointEquiv x)⁻¹)⁻¹)) = _
    rw [inv_inv, MulEquiv.symm_apply_apply]
  · rintro ⟨t, rfl⟩
    refine ⟨(diagonalPointEquiv (F := F)).symm (t⁻¹), ?_⟩
    exact positiveTorusHom_eq t

theorem parameter_orderOf_of_conjugate
    (f : CoefficientField 0 →+* F) (x : Model 0)
    (c : Variety.Point (F4Chevalley.Carrier (k := F))) (t : Fin 4 → Fˣ)
    (he : Classification.splitEmbedding f (toSplitGroup 0 x) =
      c * corootTorusElement t * c⁻¹) : orderOf t = orderOf x := by
  calc
    orderOf t = orderOf (corootTorusElement t) := (orderOf_corootTorusElement t).symm
    _ = orderOf (c * corootTorusElement t * c⁻¹) :=
      ((MulAut.conj c).orderOf_eq (corootTorusElement t)).symm
    _ = orderOf (Classification.splitEmbedding f (toSplitGroup 0 x)) :=
      congrArg orderOf he.symm
    _ = orderOf x := orderOf_injective
      ((Classification.splitEmbedding f).comp (toSplitGroup 0))
      ((Classification.splitEmbedding_injective f).comp (toSplitGroup_injective 0)) x

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage
