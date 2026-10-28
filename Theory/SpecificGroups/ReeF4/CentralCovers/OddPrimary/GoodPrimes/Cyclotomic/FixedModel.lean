module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic.AlgebraicTwist
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent

/-!
# Comparing algebraic Ree fixed points with the finite matrix model

The existing coefficient embedding of `Model m` is fixed by the algebraic
Ree twist. Conversely, rational-point descent for the actual root-generated
F4 carrier puts every exceptional fixed point in that embedding's range.
The resulting equivalence has no additional descent premise; its inverse is
the original coefficient-extension map, as recorded by the final theorem.

This assembles the proved exceptional-morphism and rational-descent APIs,
without using the broader unfinished representation-geometry assembly.
Sources: Steinberg, *Lectures on Chevalley Groups*, Theorem 7 and its third
corollary, `refs/KGroup/GLS3/Chapter2St1.tex`; GLS3 §§2.1–2.2.
-/

public section
namespace ReeF4.CentralCovers.OddPrimary.Cyclotomic
open Theory.AlgebraicGroup
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

def modelIntoFixed {m : ℕ} (f : CoefficientField m →+* F) :
    Model m →* algebraicFixed (algebraicReeTwist (F := F) m).onPoints :=
  (modelEmbedding f).codRestrict _ (fun x => by
    change (algebraicReeTwist (F := F) m).onPoints (modelEmbedding f x) = modelEmbedding f x
    rw [algebraicReeTwist_onPoints]
    exact modelEmbedding_fixed f _ ExceptionalMorphism.morphism_rootFormula x)

theorem modelIntoFixed_injective {m : ℕ} (f : CoefficientField m →+* F) :
    Function.Injective (modelIntoFixed f) := by
  intro x y h
  exact modelEmbedding_injective f (congrArg Subtype.val h)

theorem modelIntoFixed_surjective {m : ℕ} (f : CoefficientField m →+* F) :
    Function.Surjective (modelIntoFixed f) := by
  intro x
  have hx : x.val ∈ (modelEmbedding f).range := by
    rw [← SetLike.mem_coe,
      modelEmbedding_range_eq_fixed_of_descent f
        (RationalDescent.mem_splitEmbedding_range_of_coordinates f)
        (ExceptionalMorphism.morphism (F := F)).onPoints ExceptionalMorphism.morphism_rootFormula]
    have hx := x.property
    change (algebraicReeTwist (F := F) m).onPoints x.val = x.val at hx
    have he := DFunLike.congr_fun (algebraicReeTwist_onPoints (F := F) m) x.val
    exact he.symm.trans hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

/-- Inverse of the actual coefficient embedding onto the whole Ree fixed subgroup. -/
def fixedModelEquiv {m : ℕ} (f : CoefficientField m →+* F) :
    algebraicFixed (algebraicReeTwist (F := F) m).onPoints ≃* Model m :=
  (MulEquiv.ofBijective (modelIntoFixed f)
    ⟨modelIntoFixed_injective f, modelIntoFixed_surjective f⟩).symm

/-- The comparison retains the literal coefficient-extension embedding. -/
theorem fixedModelEquiv_symm_val {m : ℕ} (f : CoefficientField m →+* F) (x : Model m) :
    ((fixedModelEquiv f).symm x).val = modelEmbedding f x := by rfl

end
end ReeF4.CentralCovers.OddPrimary.Cyclotomic
