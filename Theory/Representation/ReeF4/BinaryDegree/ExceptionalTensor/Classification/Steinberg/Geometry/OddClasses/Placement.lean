module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SourceFixedPoints
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Placement
public import Theory.AlgebraicGroup.Borel.ElementCoverage.Source

/-!
# Torus placement for every odd-order element of the finite Ree carrier

Finite odd order makes the actual characteristic-two algebraic point
semisimple. Connected-group Borel coverage and maximal-torus conjugacy
then give a conjugator into the literal four-coroot torus. The result also
applies directly to the complete fixed group, retaining the source
coefficient embedding and the native finite carrier.

Source: Steinberg (1963), §3.9(5) and §12.2. This is the torus-placement
input to the odd-order conjugacy-class count; it is not a class-count or
fixed-group fusion theorem.
-/

public section
open Theory.AlgebraicGroup
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

/-- Every odd-order element in the actual finite Ree group is semisimple
under its original coefficient embedding. -/
theorem modelEmbedding_semisimple {m : ℕ} (f : CoefficientField m →+* F)
    (x : Model m) (hx : ¬ 2 ∣ orderOf x) :
    IsSemisimpleElement (F4Chevalley.Carrier (k := F)) (modelEmbedding f x) := by
  apply finiteOrder_coprimeChar_implies_semisimple _ (orderOf x)
  · exact orderOf_pos x
  · rw [ringChar.eq F 2]
    exact hx
  · rw [← map_pow, pow_orderOf_eq_one, map_one]

/-- Semisimple points of the actual connected F4 carrier lie in a conjugate
of its displayed coroot torus. -/
theorem exists_coroot_conjugate (s : PointGroup F)
    (hs : IsSemisimpleElement (F4Chevalley.Carrier (k := F)) s) :
    ∃ (c : PointGroup F) (t : Fin 4 → Fˣ),
      s = c * corootTorusElement t * c⁻¹ := by
  obtain ⟨B, hB⟩ := exists_borelSubgroup (F4Chevalley.Carrier (k := F))
  obtain ⟨b, hb⟩ := BorelElementCoverage.exists_conjugate_mem
    F4Chevalley.carrier_isConnected hB s
  apply ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage.exists_coroot_conjugate_of_mem_borel (B.conjugate b) (hB.conjugate b) s hs
  exact (B.mem_conjugate_iff b s).mpr hb

/-- The literal native odd-order torus-placement input for the class bound. -/
theorem model_exists_coroot_conjugate {m : ℕ} (f : CoefficientField m →+* F)
    (x : Model m) (hx : ¬ 2 ∣ orderOf x) :
    ∃ (c : PointGroup F) (t : Fin 4 → Fˣ),
      modelEmbedding f x = c * corootTorusElement t * c⁻¹ :=
  exists_coroot_conjugate _ (modelEmbedding_semisimple f x hx)

/-- Odd-order points of the complete fixed group have the same semisimplicity
and torus placement, through the proved native-carrier equivalence. -/
theorem fixed_exists_coroot_conjugate (m : ℕ)
    (x : SourceFixedPoints.fixedGroup (F := F) m) (hx : ¬ 2 ∣ orderOf x) :
    ∃ (c : PointGroup F) (t : Fin 4 → Fˣ),
      (x : PointGroup F) = c * corootTorusElement t * c⁻¹ := by
  let e := SourceFixedPoints.modelEquiv m (coefficientHom F m)
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy : ¬ 2 ∣ orderOf y := by simpa only [e.orderOf_eq] using hx
  exact model_exists_coroot_conjugate (coefficientHom F m) y hy

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses
