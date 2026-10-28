module

public import Theory.AlgebraicGroup.Variety.GeometricClosedImage
public import Theory.AlgebraicGroup.Variety.GeometricDimension

/-!
# Nonconstant maps into irreducible curves are dominant

The irreducible image closure of a nonconstant map cannot be a proper closed
subset of a one-dimensional irreducible variety: a proper image has dimension
at most zero, so it has at most one rational point. This discharges density
for the explicit monomial parametrization in the proof of Borel §13.13.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem subsingleton_points_of_irreducible_dimension_le_zero
    (X : Geometric k) [IrreducibleSpace X.toScheme] (hdim : dimension X ≤ 0) :
    Subsingleton (Point X) := by
  constructor
  intro p q
  let z := pointEquivClosedPoint X.structureMap p
  let Z : IrreducibleCloseds X.toScheme := ⟨{z.1}, isIrreducible_singleton, z.2⟩
  let W : IrreducibleCloseds X.toScheme :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have hZW : Z ≤ W := Set.subset_univ _
  have hWZ : W ≤ Z := (Order.krullDim_nonpos_iff_forall_isMax.mp hdim) Z hZW
  have he : (pointEquivClosedPoint X.structureMap q).1 = z.1 := hWZ (Set.mem_univ _)
  apply (pointEquivClosedPoint X.structureMap).injective
  exact Subtype.ext he.symm

theorem Morphism.dominant_of_nonconstant_to_irreducible_curve
    {X Y : Geometric k} (f : Morphism X Y)
    [IrreducibleSpace X.toScheme] [IrreducibleSpace Y.toScheme]
    (hdim : dimension Y = 1) (p q : Point X) (hpq : f p ≠ f q) : IsDominant f.hom := by
  classical
  by_contra hdom
  let Z := f.schemeTheoreticRangeClosure
  have hnot : ¬ Function.Surjective Z.inclusion.hom := by
    intro hs
    apply hdom
    constructor
    rw [DenseRange, dense_iff_closure_eq]
    exact (f.range_schemeTheoreticRangeClosure_inclusion).symm.trans hs.range_eq
  have hd : dimension Z.toGeometric < 1 := by
    rw [← hdim]
    exact closedSubvariety_dimension_lt Y Z hnot
  have hz : dimension Z.toGeometric ≤ 0 := by
    have hd' : dimension Z.toGeometric < (0 : WithBot ℕ∞) + 1 := by simpa using hd
    exact (ENat.WithBot.lt_add_one_iff (m := 0)).mp hd'
  have : IrreducibleSpace Z.toGeometric.toScheme :=
    f.schemeTheoreticRangeClosure_isIrreducible inferInstance inferInstance
  have : Subsingleton (Point Z.toGeometric) :=
    subsingleton_points_of_irreducible_dimension_le_zero Z.toGeometric hz
  apply hpq
  rw [← f.toSchemeTheoreticRangeClosure_inclusion_apply p,
    ← f.toSchemeTheoreticRangeClosure_inclusion_apply q]
  exact congrArg Z.inclusion (Subsingleton.elim _ _)

end Theory.AlgebraicGroup.Variety.Geometric
