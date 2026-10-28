module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent
public import Theory.Representation.Quotient

/-!
# The complete algebraic fixed group is the literal finite Ree carrier

The actual exceptional morphism has the required root formula and its square
is coefficient Frobenius. A point fixed by its odd power consequently has all
coordinates in the finite coefficient field. The proved rational Bruhat
parameter descent then places it in the finite root-generated split group,
and the fixed equation places its preimage in the original Ree model.

The resulting group equivalence preserves the exact coefficient embedding.
Its irreducibility consumer compares the restriction to the whole algebraic
fixed group with the original finite action. Thus finite restriction no longer
needs a fixed-point coverage hypothesis. Universality and the restricted
representation theorem remain separate obligations.
Source: Steinberg, Representations of Algebraic Groups (1963), Section 12;
Lectures on Chevalley Groups, Theorem 7 and its third corollary.
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SourceFixedPoints
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The whole fixed group of the actual odd exceptional algebraic endomorphism. -/
@[expose] def fixedGroup (m : ℕ) : Subgroup (PointGroup F) :=
  let ψ : Monoid.End (PointGroup F) := ExceptionalMorphism.morphism.onPoints
  let φ : Monoid.End (PointGroup F) := ψ ^ (2 * m + 1)
  φ.eqLocus (MonoidHom.id _)

/-- The coefficient embedding exhausts the full algebraic fixed group. -/
theorem modelEmbedding_range {m : ℕ} (f : CoefficientField m →+* F) :
    (modelEmbedding f).range = fixedGroup (F := F) m := by
  apply SetLike.coe_injective
  exact modelEmbedding_range_eq_fixed_of_descent f
    (RationalDescent.mem_splitEmbedding_range_of_coordinates f)
    ExceptionalMorphism.morphism.onPoints ExceptionalMorphism.morphism_rootFormula

/-- The literal finite Ree carrier and the complete algebraic fixed group. -/
@[expose] def modelEquiv (m : ℕ) (f : CoefficientField m →+* F) :
    Model m ≃* fixedGroup (F := F) m :=
  (MonoidHom.ofInjective (modelEmbedding_injective f)).trans
    (MulEquiv.subgroupCongr (modelEmbedding_range f))

/-- The group comparison retains the original coefficient embedding. -/
@[simp] theorem modelEquiv_coe (m : ℕ) (f : CoefficientField m →+* F) (g : Model m) :
    (modelEquiv m f g : PointGroup F) = modelEmbedding f g := rfl

/-- The full algebraic fixed group is finite, by the actual native carrier comparison. -/
instance fixedGroup_finite (m : ℕ) : Finite (fixedGroup (F := F) m) :=
  Finite.of_equiv (Model m) (modelEquiv m (coefficientHom F m)).toEquiv

/-- Pullback through the actual group comparison recovers the original source action. -/
theorem restrict_comp_modelEquiv (m : ℕ) (f : CoefficientField m →+* F)
    (A : AlgebraicFactor F) :
    ((A.restrict (fixedGroup m).subtype).ρ.comp (modelEquiv m f).toMonoidHom) =
      (A.restrict (modelEmbedding f)).ρ := by
  ext g v
  rfl

/-- Actual consumer: irreducibility on the complete fixed group is precisely
irreducibility on the original finite Ree carrier. No coverage premise remains. -/
theorem restriction_irreducible_iff (m : ℕ) (f : CoefficientField m →+* F)
    (A : AlgebraicFactor F) :
    Representation.IsIrreducible (A.restrict (fixedGroup m).subtype).ρ ↔
      Representation.IsIrreducible (A.restrict (modelEmbedding f)).ρ := by
  rw [← restrict_comp_modelEquiv]
  exact (Representation.irreducible_comp_surjective_iff
    (modelEquiv m f).toMonoidHom (modelEquiv m f).surjective _).symm

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SourceFixedPoints
