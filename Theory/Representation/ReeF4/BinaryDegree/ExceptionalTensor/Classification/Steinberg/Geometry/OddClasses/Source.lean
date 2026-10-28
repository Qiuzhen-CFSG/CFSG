module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.Counting
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.Source
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The unconditional q² bound for odd-order Ree conjugacy classes

Over the algebraic closure of the binary prime field, the actual coefficient
embedding identifies the finite model with the full exceptional fixed group.
Connected semisimple centralizers supply the Lang fusion theorem. The proved
fundamental-coordinate injection therefore bounds the odd-order conjugacy
classes by q², exactly the number of restricted binary weights.

Source: Steinberg (1963), §§3.9 and 12.2. This theorem has only the original
Ree parameter as input; no class-bound, torus, fusion, or catalogue premise
remains. It supplies finite irreducible-family exhaustion in the source B.4
application.
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses
theorem model_odd_class_bound (m : ℕ) :
    Nat.card (ConjClasses.mk '' {g : Model m | ¬ 2 ∣ orderOf g}) ≤ Nat.card (RestrictedWeight m) := by
  let F := AlgebraicClosure (ZMod 2)
  exact model_odd_class_bound_of_connected_centralizers m (coefficientHom F m)
    (SemisimpleCentralizers.model_pointCentralizer_isConnected m (coefficientHom F m))
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses
