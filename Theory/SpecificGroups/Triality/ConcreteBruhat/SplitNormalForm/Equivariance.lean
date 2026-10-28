module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.SplitNormalForm.Inputs

/-!
# Graph-field transport of split Bruhat coordinates

The diagram permutes positive roots and conjugates the Weyl action. Consequently
it transports inversion support, including zero coordinates, to the inversion
support of the transformed Weyl element. The existing equivariant positive-root
product then gives equivariance of the four-factor matrix expression.

These assertions concern proposed normal forms. Coverage and injectivity of the
full expression are separate obligations; no fixed-point generation is used.
Source: GLS3 2.3.5 and 2.3.8(c), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.ConcreteBruhat.SplitNormalForm
open Parabolics

theorem diagram_isPos_iff (r : TypeDRootIndex 4) :
    (typeDRootPairing_base 2).IsPos (typeD4DiagramEquiv.indexEquiv r) ↔
      (typeDRootPairing_base 2).IsPos r := by
  change typeD4DiagramEquiv.indexEquiv r ∈ {r | (typeDRootPairing_base 2).IsPos r} ↔
    r ∈ {r | (typeDRootPairing_base 2).IsPos r}
  rw [← PositiveCoordinates.range_rootIndex]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨PositiveCoordinates.diagram.symm i, ?_⟩
    apply typeD4DiagramEquiv.indexEquiv.injective
    rw [PositiveCoordinates.diagram_rootIndex, Equiv.apply_symm_apply, hi]
  · rintro ⟨i, rfl⟩
    exact ⟨PositiveCoordinates.diagram i, (PositiveCoordinates.diagram_rootIndex i).symm⟩

/-- Diagram transport takes the precise inversion set to the new inversion set. -/
theorem inversion_diagram_iff {P : Parameters} (D : Inputs P) (w : rootWeylGroup)
    (i : Fin 12) :
    (typeDRootPairing_base 2).IsPos
        ((D.weylTwist w).val (PositiveCoordinates.rootIndex (PositiveCoordinates.diagram i))) ↔
      (typeDRootPairing_base 2).IsPos (w.val (PositiveCoordinates.rootIndex i)) := by
  rw [← PositiveCoordinates.diagram_rootIndex, D.weylTwist_apply_diagram, diagram_isPos_iff]

/-- Zeroes outside the inversion set survive the actual coefficient Frobenius. -/
theorem supported_twist {P : Parameters} (D : Inputs P) {w : rootWeylGroup}
    {a : PositiveCoordinates.Coordinates P} (ha : Supported P w a) :
    Supported P (D.weylTwist w) (PositiveCoordinates.twist P a) := by
  intro i hi
  have hp : (typeDRootPairing_base 2).IsPos
      (w.val (PositiveCoordinates.rootIndex (PositiveCoordinates.diagram.symm i))) := by
    apply (inversion_diagram_iff D w (PositiveCoordinates.diagram.symm i)).mp
    simpa only [Equiv.apply_symm_apply] using hi
  simp only [PositiveCoordinates.twist, ha _ hp, map_zero]

/-- Graph-field action on the four factors, with inversion support proved. -/
def twist {P : Parameters} (D : Inputs P) (a : Coordinates P) : Coordinates P where
  left := ⟨graphFieldAutomorphism P a.left.val, by
    exact (positiveSubgroup_invariant P).le ⟨a.left.val, a.left.property, rfl⟩⟩
  torus := ⟨graphFieldAutomorphism P a.torus.val, by
    exact (splitTorus_invariant P).le ⟨a.torus.val, a.torus.property, rfl⟩⟩
  weyl := D.weylTwist a.weyl
  right := PositiveCoordinates.twist P a.right
  supported := supported_twist D a.supported

/-- The matrix expression intertwines the genuine graph-field automorphism. -/
theorem evaluate_twist_binary (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (a : Coordinates (binaryParameters n hn)) :
    evaluate D (twist D a) = graphFieldAutomorphism (binaryParameters n hn) (evaluate D a) := by
  simp only [evaluate, twist, map_mul, Inputs.graphField_lift,
    PositiveCoordinates.graphField_orderedProduct_binary]

theorem twist_eq_self_iff {P : Parameters} (D : Inputs P) (a : Coordinates P) :
    twist D a = a ↔
      a.left.val ∈ fixedSubgroup P ∧ a.torus.val ∈ fixedSubgroup P ∧
      D.weylTwist a.weyl = a.weyl ∧
      ∀ i, a.right (PositiveCoordinates.diagram i) = fieldFrobenius P (a.right i) := by
  constructor
  · intro h
    refine ⟨congrArg (fun c : Coordinates P => c.left.val) h,
      congrArg (fun c : Coordinates P => c.torus.val) h,
      congrArg Coordinates.weyl h, ?_⟩
    exact (PositiveCoordinates.twist_eq_self_iff P a.right).mp
      (congrArg Coordinates.right h)
  · rintro ⟨hu, ht, hw, hv⟩
    apply Coordinates.ext
    · exact Subtype.ext hu
    · exact Subtype.ext ht
    · exact hw
    · exact (PositiveCoordinates.twist_eq_self_iff P a.right).mpr hv

/-- Once separation has been proved, fixed matrices have fixed individual
factors and exactly the inversion-coordinate Frobenius equations. -/
theorem evaluate_mem_fixed_iff_of_injective (n : ℕ) (hn : 0 < n)
    (D : Inputs (binaryParameters n hn)) (hinj : Function.Injective (evaluate D))
    (a : Coordinates (binaryParameters n hn)) :
    evaluate D a ∈ fixedSubgroup (binaryParameters n hn) ↔
      a.left.val ∈ fixedSubgroup (binaryParameters n hn) ∧
      a.torus.val ∈ fixedSubgroup (binaryParameters n hn) ∧
      D.weylTwist a.weyl = a.weyl ∧
      ∀ i, a.right (PositiveCoordinates.diagram i) =
        fieldFrobenius (binaryParameters n hn) (a.right i) := by
  have h : evaluate D a ∈ fixedSubgroup (binaryParameters n hn) ↔ twist D a = a := by
    constructor
    · intro hf
      exact hinj ((evaluate_twist_binary n hn D a).trans hf)
    · intro ha
      exact (evaluate_twist_binary n hn D a).symm.trans (congrArg (evaluate D) ha)
  exact h.trans (twist_eq_self_iff D a)

end Triality.Standard.ConcreteBruhat.SplitNormalForm
