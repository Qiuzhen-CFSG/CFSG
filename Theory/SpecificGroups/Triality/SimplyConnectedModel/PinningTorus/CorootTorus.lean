module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootPoints
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Coordinates
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.RegularProduct
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.CoordinateRecovery
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Maximality
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Characters
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.SpinCoefficient
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.CliffordCurves
public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalTorusRootExhaustiveness

/-!
# The algebraic Spin coroot torus and its fundamental characters

Over an algebraically closed field of characteristic two, `closedSubgroup k`
is a closed maximal torus of the actual Clifford Spin carrier. `coordinateIso`
is an algebraic-group isomorphism from the standard four-dimensional torus;
its inclusion is exactly the ordered product of the four source simple coroots.

The forward morphism is constructed from the explicit Clifford root curves.
The inverse is regular because the polynomial `spinCoefficient` recovers `t₃`,
and the ordinary diagonal coordinates recover `t₀`, `t₁`, and `t₂ / t₃`.
Maximality follows from self-centralization of the ordinary diagonal torus:
any containing torus is commutative and its image under the Spin cover must
lie in that diagonal torus. Transporting Laurent characters through this
algebraic isomorphism gives `weightEmbedding` and the four
`fundamentalCharacter`s, with their exact Kronecker coroot evaluations.

These are the concrete torus and character constructions used in the source
criterion; the comparison with semantic universality is a separate theorem.

Source: GLS3, Theorems 1.12.1 and 1.12.5(b), Proposition 1.14.1 and
Definition 1.14.2, `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Pinning.CorootTorus
open Theory Theory.AlgebraicGroup
open scoped BigOperators
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The regular ordered product of the four actual Spin simple coroots. -/
def regularParameter : AlgebraicGroup.Morphism (dVariety k 4) (groupVariety k) :=
  productOfRegularRoots k (cliffordRootMorphism k) (cliffordRootMorphism_kPlusPoint k)

/-- The regular product preserves the published coroot-word normalization. -/
theorem regularParameter_apply (x : Variety.Point (dVariety k 4)) :
    (regularParameter k).onPoints x = parameter k (dPointEquiv 4 x) :=
  productOfRegularRoots_apply k _ _ x

/-- The algebraic Spin coroot coordinates, including the regular inverse
constructed from the actual polynomial Clifford coefficient. -/
def coordinateIso : AlgebraicGroup.Iso (dVariety k 4) (closedSubgroup k).carrierVariety :=
  isoOfRegularParameter k (regularParameter k) (regularParameter_apply k)
    (spinCoefficient k) (spinCoefficient_parameter k)

/-- Inclusion of the torus is exactly the source's ordered simple-coroot product. -/
theorem coordinateIso_inclusion (x : Variety.Point (dVariety k 4)) :
    (closedSubgroup k).inclusion.onPoints ((coordinateIso k).hom.onPoints x) =
      (List.ofFn fun i : Fin 4 => simpleCoroot k i (dPointEquiv 4 x i)).prod :=
  isoOfRegularParameter_inclusion k _ _ _ _ x

/-- The isomorphism agrees with the previously constructed torus points. -/
@[simp] theorem coordinateIso_hom_apply (x : Variety.Point (dVariety k 4)) :
    (coordinateIso k).hom.onPoints x = parameterPoint k (dPointEquiv 4 x) := by
  apply (closedSubgroup k).inclusion_injective
  rw [coordinateIso_inclusion, inclusion_parameterPoint]
  rfl

/-- The regular inverse recovers every simple-coroot parameter. -/
@[simp] theorem coordinateIso_inv_parameter (t : Fin 4 → kˣ) :
    (coordinateIso k).inv.onPoints (parameterPoint k t) = (dPointEquiv 4).symm t := by
  have h := (coordinateIso k).hom_inv_id ((dPointEquiv 4).symm t)
  rwa [coordinateIso_hom_apply, Equiv.apply_symm_apply] at h

/-- The inverse coordinates are the explicit polynomial recovery functions. -/
theorem coordinateIso_inv_coordinate
    (x : Variety.Point (closedSubgroup k).carrierVariety) (i : Fin 4) :
    (dPointEquiv 4 ((coordinateIso k).inv.onPoints x) i : k) =
      recoveryScalar k (spinCoefficient k) i x := by
  obtain ⟨y, rfl⟩ := (coordinateIso k).toMulEquiv.surjective x
  change (dPointEquiv 4 ((coordinateIso k).inv.onPoints
    ((coordinateIso k).hom.onPoints y)) i : k) =
      recoveryScalar k (spinCoefficient k) i ((coordinateIso k).hom.onPoints y)
  rw [(coordinateIso k).hom_inv_id, coordinateIso_hom_apply,
    recoveryScalar_parameter k (spinCoefficient k) (spinCoefficient_parameter k)]

/-- The closed diagonal preimage is a four-dimensional algebraic torus. -/
theorem isSubtorus : IsSubtorus (closedSubgroup k) := ⟨4, ⟨coordinateIso k⟩⟩

/-- The Spin coroot torus is maximal among all closed subtori. -/
theorem isMaximal : IsMaximalTorus (closedSubgroup k) := by
  apply isMaximal_of_isSubtorus k _ (isSubtorus k)
  change (evenOrthogonalDiagonalTorus (k := k) 4 (le_refl 4)).centralizer.toSubgroup ≤ _
  rw [evenOrthogonalDiagonalTorus_centralizer_eq (k := k) 4 (le_refl 4)]

/-- Integral Laurent weights as actual algebraic characters of the Spin torus. -/
def weightEmbedding : (Fin 4 → ℤ) ↪ TorusWeight (closedSubgroup k) :=
  weightEmbeddingOfIso k (coordinateIso k)

/-- The units-valued Laurent formula in algebraic coroot coordinates. -/
theorem weightEmbedding_apply (z : Fin 4 → ℤ) (x : Variety.Point (dVariety k 4)) :
    dPointEquiv 1 ((weightEmbedding k z).onPoints ((coordinateIso k).hom.onPoints x)) 0 =
      ∏ i, dPointEquiv 4 x i ^ z i :=
  weightEmbeddingOfIso_apply k (coordinateIso k) z x

/-- The scalar Laurent formula on the literal coroot products. -/
theorem weightEmbedding_parameter (z : Fin 4 → ℤ) (t : Fin 4 → kˣ) :
    (weightEmbedding k z).pointCharacter (parameterPoint k t) =
      ∏ i, (t i : k) ^ z i :=
  weightEmbeddingOfIso_parameter k (coordinateIso k) (coordinateIso_inclusion k) z t

/-- The four algebraic characters dual to the published simple coroots. -/
def fundamentalCharacter (i : Fin 4) : TorusWeight (closedSubgroup k) :=
  fundamentalCharacterOfIso k (coordinateIso k) i

/-- Fundamental characters read off the four simple-coroot coordinates. -/
theorem fundamentalCharacter_parameter (i : Fin 4) (t : Fin 4 → kˣ) :
    (fundamentalCharacter k i).pointCharacter (parameterPoint k t) = (t i : k) :=
  fundamentalCharacterOfIso_parameter k (coordinateIso k) (coordinateIso_inclusion k) i t

/-- Kronecker evaluation on each actual simple coroot, whose inclusion is
`inclusion_single_parameter`. -/
theorem fundamentalCharacter_simpleCoroot (i j : Fin 4) (t : kˣ) :
    (fundamentalCharacter k i).pointCharacter
      (parameterPoint k (Function.update (fun _ => 1) j t)) =
        if i = j then (t : k) else 1 :=
  fundamentalCharacterOfIso_simpleCoroot k (coordinateIso k) (coordinateIso_inclusion k) i j t

end Triality.SimplyConnected.Pinning.CorootTorus
