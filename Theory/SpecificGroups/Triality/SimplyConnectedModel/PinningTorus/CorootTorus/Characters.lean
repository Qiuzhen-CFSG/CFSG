module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Coordinates

/-!
# Fundamental characters in Spin coroot coordinates

An actual algebraic isomorphism from the standard four-dimensional torus
transports Laurent characters injectively to the closed Spin diagonal preimage.
When its inclusion is the source coroot product, the coordinate characters
have Kronecker evaluations on the actual simple coroots. All integral weights
have the corresponding Laurent-product evaluation formula.

The algebraic isomorphism is an explicit input; a point-group equivalence would
not suffice. Source: GLS3, Proposition 1.14.1 and Definition 1.14.2,
`refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Pinning.CorootTorus
open Theory Theory.AlgebraicGroup
open scoped BigOperators
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Integral characters transported along an actual algebraic torus isomorphism. -/
def weightEmbeddingOfIso
    (e : AlgebraicGroup.Iso (dVariety k 4) (closedSubgroup k).carrierVariety) :
    (Fin 4 → ℤ) ↪ TorusWeight (closedSubgroup k) where
  toFun z := (dLaurentCharacter 4 z).comp e.inv
  inj' := by
    intro z w h
    apply dLaurentCharacter_injective (k := k) 4
    apply AlgebraicGroup.Morphism.ext
    funext x
    have hx := congrArg (fun χ : TorusWeight (closedSubgroup k) =>
      χ.onPoints (e.hom.onPoints x)) h
    change (dLaurentCharacter 4 z).onPoints (e.inv.onPoints (e.hom.onPoints x)) =
      (dLaurentCharacter 4 w).onPoints (e.inv.onPoints (e.hom.onPoints x)) at hx
    rw [e.hom_inv_id] at hx
    exact hx

omit [CharP k 2] in
/-- The units-valued Laurent formula in the isomorphism's coordinates. -/
theorem weightEmbeddingOfIso_apply
    (e : AlgebraicGroup.Iso (dVariety k 4) (closedSubgroup k).carrierVariety)
    (z : Fin 4 → ℤ) (x : Variety.Point (dVariety k 4)) :
    dPointEquiv 1 ((weightEmbeddingOfIso k e z).onPoints (e.hom.onPoints x)) 0 =
      ∏ i, dPointEquiv 4 x i ^ z i := by
  change dPointEquiv 1 ((dLaurentCharacter 4 z).onPoints
    (e.inv.onPoints (e.hom.onPoints x))) 0 = _
  rw [e.hom_inv_id, dLaurentCharacter_apply]

private theorem iso_apply_parameter
    (e : AlgebraicGroup.Iso (dVariety k 4) (closedSubgroup k).carrierVariety)
    (he : ∀ x, (closedSubgroup k).inclusion.onPoints (e.hom.onPoints x) =
      parameter k (dPointEquiv 4 x)) (t : Fin 4 → kˣ) :
    e.hom.onPoints ((dPointEquiv 4).symm t) = parameterPoint k t := by
  apply (closedSubgroup k).inclusion_injective
  rw [he, inclusion_parameterPoint, Equiv.apply_symm_apply]

/-- The scalar Laurent formula on the literal coroot products. -/
theorem weightEmbeddingOfIso_parameter
    (e : AlgebraicGroup.Iso (dVariety k 4) (closedSubgroup k).carrierVariety)
    (he : ∀ x, (closedSubgroup k).inclusion.onPoints (e.hom.onPoints x) =
      parameter k (dPointEquiv 4 x)) (z : Fin 4 → ℤ) (t : Fin 4 → kˣ) :
    (weightEmbeddingOfIso k e z).pointCharacter (parameterPoint k t) =
      ∏ i, (t i : k) ^ z i := by
  rw [← iso_apply_parameter k e he t]
  change (dPointEquiv 1 ((weightEmbeddingOfIso k e z).onPoints
    (e.hom.onPoints ((dPointEquiv 4).symm t))) 0 : k) = _
  rw [weightEmbeddingOfIso_apply, Equiv.apply_symm_apply]
  simp

/-- The four fundamental algebraic characters, dual to the simple coroots. -/
def fundamentalCharacterOfIso
    (e : AlgebraicGroup.Iso (dVariety k 4) (closedSubgroup k).carrierVariety)
    (i : Fin 4) : TorusWeight (closedSubgroup k) :=
  weightEmbeddingOfIso k e (Pi.single i 1)

/-- Fundamental characters recover the individual coroot parameters. -/
theorem fundamentalCharacterOfIso_parameter
    (e : AlgebraicGroup.Iso (dVariety k 4) (closedSubgroup k).carrierVariety)
    (he : ∀ x, (closedSubgroup k).inclusion.onPoints (e.hom.onPoints x) =
      parameter k (dPointEquiv 4 x)) (i : Fin 4) (t : Fin 4 → kˣ) :
    (fundamentalCharacterOfIso k e i).pointCharacter (parameterPoint k t) = (t i : k) := by
  classical
  rw [fundamentalCharacterOfIso, weightEmbeddingOfIso_parameter k e he]
  simp [Pi.single_apply]

/-- The point used in the evaluation theorem includes as the actual simple coroot. -/
theorem inclusion_single_parameter (j : Fin 4) (t : kˣ) :
    (closedSubgroup k).inclusion.onPoints
      (parameterPoint k (Function.update (fun _ => 1) j t)) = simpleCoroot k j t := by
  rw [inclusion_parameterPoint, parameter_single]

/-- The Kronecker evaluation required for fundamental weights in GLS3 1.14.2. -/
theorem fundamentalCharacterOfIso_simpleCoroot
    (e : AlgebraicGroup.Iso (dVariety k 4) (closedSubgroup k).carrierVariety)
    (he : ∀ x, (closedSubgroup k).inclusion.onPoints (e.hom.onPoints x) =
      parameter k (dPointEquiv 4 x)) (i j : Fin 4) (t : kˣ) :
    (fundamentalCharacterOfIso k e i).pointCharacter
      (parameterPoint k (Function.update (fun _ => 1) j t)) =
        if i = j then (t : k) else 1 := by
  classical
  rw [fundamentalCharacterOfIso, weightEmbeddingOfIso_parameter k e he]
  by_cases hij : i = j <;> simp [Pi.single_apply, Function.update_apply, hij, eq_comm]

end Triality.SimplyConnected.Pinning.CorootTorus
