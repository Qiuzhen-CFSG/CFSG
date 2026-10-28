module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.PointTwist
public import Theory.AlgebraicGroup.RootSystems.F4WeightAction.IteratedCoordinates
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses.CoordinateCount
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.ToralConjugacy
/-!
# Frobenius-compatible coordinates of actual Ree fixed points

The literal positive coroot product is realized inside the split torus, and
its left characters evaluate as the displayed integral lattice characters.
Actual ambient toral conjugacy therefore preserves the four fundamental
orbit sums. Applying this to the exceptional transform of a representative
of a fixed point proves the two Frobenius-compatible coordinate pairs.
Their equality is exactly equality of all four fundamental orbit sums.

Source: Steinberg (1963), §§3.9 and 12.2. The coordinate target has q² points
by CoordinateCount; fixed-group fusion is the separate input to the final
conjugacy-class injection.
-/

public noncomputable section
open scoped BigOperators
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses
open F4WeightAction RootModel.Corrected
open scoped F4WeightAction
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
noncomputable local instance coordinatesTorusGroup : AlgebraicGroup (F4Chevalley.splitTorus (k:=F)).carrierVariety :=
  (F4Chevalley.splitTorus (k:=F)).carrierAlgebraicGroup
local instance coordinatesWeylFinite : Finite Weyl := weylGroup_finite typeF4RootPairing

private noncomputable def unitPoint (t : Fˣ) : Variety.Point (KMult F) :=
  (dPointEquiv 1).symm (fun _ => t)

noncomputable def corootPoint (t : Fin 4 → Fˣ) :
    Variety.Point (F4Chevalley.splitTorus (k:=F)).carrierVariety :=
  (F4Chevalley.splitTorusSimpleCoroot 0).onPoints (unitPoint (t 0)) *
  (F4Chevalley.splitTorusSimpleCoroot 1).onPoints (unitPoint (t 1)) *
  (F4Chevalley.splitTorusSimpleCoroot 2).onPoints (unitPoint (t 2)) *
  (F4Chevalley.splitTorusSimpleCoroot 3).onPoints (unitPoint (t 3))

omit [CharP F 2] in
lemma corootPoint_inclusion (t : Fin 4 → Fˣ) :
    (F4Chevalley.splitTorus (k:=F)).includePoint (corootPoint t) = corootTorusElement t := by
  change (F4Chevalley.splitTorus (k:=F)).inclusion.onPoints (corootPoint t) = _
  simp [corootPoint, corootTorusElement, map_mul, splitTorusSimpleCoroot_eq_algebraicCoroot, unitPoint]

omit [CharP F 2] in
lemma leftCharacter_corootPoint (t : Fin 4 → Fˣ) (a : F4WeightAction.Weight) :
    (leftCharacter a).pointCharacter (corootPoint t) = (character t (Multiplicative.ofAdd a) : F) := by
  have he (i : Fin 4) : (leftCharacter a).pointCharacter
      ((F4Chevalley.splitTorusSimpleCoroot i).onPoints (unitPoint (t i))) = (t i : F) ^ a i := by
    simpa only [unitPoint, Equiv.apply_symm_apply] using
      leftCharacter_representationCoroot (F:=F) a i (unitPoint (t i))
  simp [corootPoint, map_mul, he, character, Fin.prod_univ_four]

lemma exists_weyl_of_corootTorus_isConj (t s : Fin 4 → Fˣ)
    (h : IsConj (corootTorusElement t) (corootTorusElement s)) :
    ∃ w : Weyl, ∀ a : Lattice, character s a = character t (w • a) := by
  obtain ⟨w, hw⟩ := SemisimpleCentralizers.exists_weyl_leftCharacter_of_toral_conjugacy
    (corootPoint t) (corootPoint s) (by simpa only [corootPoint_inclusion] using h)
  refine ⟨w, fun a => ?_⟩
  apply Units.ext
  have he := hw a.toAdd
  rw [leftCharacter_corootPoint, leftCharacter_corootPoint] at he
  exact he

lemma fundamentalValue_eq_of_corootTorus_isConj (t s : Fin 4 → Fˣ)
    (h : IsConj (corootTorusElement t) (corootTorusElement s)) (i : Fin 4) :
    fundamentalValue t i = fundamentalValue s i := by
  obtain ⟨w, hw⟩ := exists_weyl_of_corootTorus_isConj t s h
  exact (Theory.MonoidAlgebraOrbitSums.orbitSumValue_eq_of_point_equiv
    (character t) (character s) w hw (fundamental i)).symm

lemma fixed_torus_coordinates_compatible (m : ℕ)
    (x : SourceFixedPoints.fixedGroup (F:=F) m) (c : PointGroup F) (t : Fin 4 → Fˣ)
    (hx : (x : PointGroup F) = c * corootTorusElement t * c⁻¹) :
    (fundamentalValue t 3 ^ (2^(m+1)) = fundamentalValue t 0 ∧
      fundamentalValue t 0 ^ (2^m) = fundamentalValue t 3) ∧
    (fundamentalValue t 2 ^ (2^(m+1)) = fundamentalValue t 1 ∧
      fundamentalValue t 1 ^ (2^m) = fundamentalValue t 2) := by
  have he (i : Fin 4) := fundamentalValue_eq_of_corootTorus_isConj
    ((torusTwist (F:=F))^[2*m+1] t) t (fixed_torus_twist_isConj m x c t hx) i
  simp only [fundamentalValue_torusTwist_iterate_odd] at he
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa [Fin.revPerm, Fin.rev] using he 0
  · simpa [Fin.revPerm, Fin.rev] using he 3
  · simpa [Fin.revPerm, Fin.rev] using he 1
  · simpa [Fin.revPerm, Fin.rev] using he 2
@[expose] noncomputable def fixedCoordinateCode (m : ℕ)
    (x : SourceFixedPoints.fixedGroup (F:=F) m) (c : PointGroup F) (t : Fin 4 → Fˣ)
    (hx : (x : PointGroup F) = c * corootTorusElement t * c⁻¹) :
    CoordinateCount.TwistedPair m F × CoordinateCount.TwistedPair m F :=
  let h := fixed_torus_coordinates_compatible m x c t hx
  (⟨(fundamentalValue t 3, fundamentalValue t 0), h.1⟩,
    ⟨(fundamentalValue t 2, fundamentalValue t 1), h.2⟩)

lemma fixedCoordinateCode_eq_iff (m : ℕ)
    (x y : SourceFixedPoints.fixedGroup (F:=F) m)
    (c d : PointGroup F) (t s : Fin 4 → Fˣ)
    (hx : (x : PointGroup F) = c * corootTorusElement t * c⁻¹)
    (hy : (y : PointGroup F) = d * corootTorusElement s * d⁻¹) :
    fixedCoordinateCode m x c t hx = fixedCoordinateCode m y d s hy ↔
      ∀ i : Fin 4, fundamentalValue t i = fundamentalValue s i := by
  constructor
  · intro h i
    have h1 := congrArg (fun v : CoordinateCount.TwistedPair m F × CoordinateCount.TwistedPair m F => v.1.val) h
    have h2 := congrArg (fun v : CoordinateCount.TwistedPair m F × CoordinateCount.TwistedPair m F => v.2.val) h
    fin_cases i
    · exact congrArg Prod.snd h1
    · exact congrArg Prod.snd h2
    · exact congrArg Prod.fst h2
    · exact congrArg Prod.fst h1
  · intro h
    apply Prod.ext <;> apply Subtype.ext
    · exact Prod.ext (h 3) (h 0)
    · exact Prod.ext (h 2) (h 1)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OddClasses
