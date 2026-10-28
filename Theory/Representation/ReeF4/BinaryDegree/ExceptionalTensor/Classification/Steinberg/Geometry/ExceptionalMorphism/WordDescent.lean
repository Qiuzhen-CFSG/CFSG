module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.AdjointData

/-!
# Descent of the exceptional F4 root formula to algebraic points

Free root words evaluate surjectively onto the literal closed F4 carrier.
The quotient-to-ideal comparison intertwines their ordinary and exceptional
matrix evaluations. Restricted adjoint transport implies faithfulness on the
short ideal, so relations descend and yield a point endomorphism with exactly
the long/short root formula.

This construction retains restricted adjoint transport as an explicit premise.
It does not yet assert an unconditional exceptional algebraic morphism:
transport over the algebraic closure and polynomial regularity remain separate
obligations. The word intertwining identity proved here also applies to any
endomorphism with the root formula and supplies its short-coordinate data.

Sources: Steinberg, *Lectures on Chevalley Groups*, Theorem 28
(`refs/KGroup/GLS3/Chapter2St1.tex`); GLS3, Theorem 1.15.4(b)
(`refs/KGroup/GLS3/Chapter1.tex`). The existing finite-field construction is
`Theory/SpecificGroups/ReeF4/ExceptionalEndomorphism.lean`.
-/

@[expose] public section

open scoped Classical Matrix
open Theory.AlgebraicGroup
open ReeF4.WordRelations

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism

/-- The existing finite-field transport proof inhabits the same operator
interface. This does not extend its field of definition to an algebraic closure. -/
theorem hasShortAdjointTransport_coefficientField (m : ℕ) :
    HasShortAdjointTransport (CoefficientField m) :=
  Faithfulness.RestrictedAdjoint.generated_equivariantOnShort m

section Matrices
variable {K : Type*} [CommRing K]

/-- Free evaluation in the actual integral F4 matrices over any base ring. -/
noncomputable def matrixWordEval :
    FreeGroup (F4Chevalley.Root × K) →* (Matrix Coordinate Coordinate K)ˣ :=
  FreeGroup.lift (fun rt => F4Chevalley.rootCurve rt.1 rt.2)

/-- Exceptional substitution in the actual integral matrix root curves. -/
noncomputable def matrixTwistedEval :
    FreeGroup (F4Chevalley.Root × K) →* (Matrix Coordinate Coordinate K)ˣ :=
  FreeGroup.lift (fun rt => F4Chevalley.rootCurve
    (exceptionalRootPermutation rt.1) (exceptionalParameter rt.1 rt.2))

@[simp] theorem matrixWordEval_of (r : F4Chevalley.Root) (t : K) :
    matrixWordEval (FreeGroup.of (r, t)) = F4Chevalley.rootCurve r t :=
  FreeGroup.lift_apply_of

@[simp] theorem matrixTwistedEval_of (r : F4Chevalley.Root) (t : K) :
    matrixTwistedEval (FreeGroup.of (r, t)) =
      F4Chevalley.rootCurve (exceptionalRootPermutation r) (exceptionalParameter r t) :=
  FreeGroup.lift_apply_of

theorem matrixWordEval_range : (matrixWordEval (K := K)).range = matrixGroup K :=
  FreeGroup.range_lift_eq_closure

theorem matrixTwistedEval_mem (w : FreeGroup (F4Chevalley.Root × K)) :
    matrixTwistedEval w ∈ matrixGroup K := by
  have h : (matrixTwistedEval (K := K)).range ≤ matrixGroup K := by
    apply FreeGroup.range_lift_le
    rintro _ ⟨⟨r, t⟩, rfl⟩
    exact Subgroup.subset_closure
      ⟨(exceptionalRootPermutation r, exceptionalParameter r t), rfl⟩
  exact h ⟨w, rfl⟩

/-- The singular comparison intertwines both evaluations, over every
commutative ring of characteristic two. -/
theorem matrixWordEval_intertwines [CharP K 2]
    (w : FreeGroup (F4Chevalley.Root × K)) :
    quotientToIdeal * (matrixWordEval w : Matrix Coordinate Coordinate K) =
      (matrixTwistedEval w : Matrix Coordinate Coordinate K) * quotientToIdeal :=
  lift_intertwines
    (fun rt : F4Chevalley.Root × K => F4Chevalley.rootCurve rt.1 rt.2)
    (fun rt : F4Chevalley.Root × K => F4Chevalley.rootCurve
      (exceptionalRootPermutation rt.1) (exceptionalParameter rt.1 rt.2))
    quotientToIdeal (fun rt => quotientToIdeal_intertwines_rootCurve rt.1 rt.2) w

/-- The actual generated matrix group preserves the short-coordinate ideal,
without using an exceptional point map or restricted adjoint transport. -/
theorem matrixGroup_preserves_short [CharP K 2]
    (g : (Matrix Coordinate Coordinate K)ˣ) (hg : g ∈ matrixGroup K)
    (v : Coordinate → K) (hv : Faithfulness.RestrictedAdjoint.ShortSupported v) :
    Faithfulness.RestrictedAdjoint.ShortSupported ((g : Matrix Coordinate Coordinate K) *ᵥ v) := by
  rw [← matrixWordEval_range] at hg
  obtain ⟨w, rfl⟩ := hg
  exact Faithfulness.RestrictedAdjoint.shortSupported_mulVec_of_intertwines _ _
    (matrixWordEval_intertwines w) hv

/-- Restricted transport suffices for every concrete matrix relation to
survive exceptional substitution. -/
theorem matrixWordEval_ker_le [CharP K 2] (htransport : HasShortAdjointTransport K) :
    (matrixWordEval (K := K)).ker ≤ (matrixTwistedEval (K := K)).ker := by
  intro w hw
  apply eq_one_of_short_transport htransport _ (matrixTwistedEval_mem w)
  have h := matrixWordEval_intertwines w
  change matrixWordEval w = 1 at hw
  rw [hw, Units.val_one, mul_one] at h
  exact h.symm
end Matrices

section Points
variable {F : Type*} [Field F] [IsAlgClosed F]

/-- Faithful matrix realization of the literal algebraic carrier. -/
noncomputable def pointMatrix : PointGroup F →* (Matrix Coordinate Coordinate F)ˣ :=
  ambientUnitsEquiv.symm.toMonoidHom.comp
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints

theorem pointMatrix_injective : Function.Injective (pointMatrix (F := F)) :=
  ambientUnitsEquiv.symm.injective.comp
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective

@[simp] theorem pointMatrix_root (r : F4Chevalley.Root) (t : F) :
    pointMatrix (algebraicRootElement r t) = F4Chevalley.rootCurve r t := by
  apply ambientUnitsEquiv.injective
  change ambientUnitsEquiv (ambientUnitsEquiv.symm _) = _
  rw [MulEquiv.apply_symm_apply]
  change (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
    ((F4Chevalley.rootMorphism r).onPoints (kPlusPoint t)) = _
  rw [F4Chevalley.rootMorphism_inclusion_apply, ambientUnitsEquiv_rootCurve]

/-- Root-word evaluation directly in the literal closed carrier. -/
noncomputable def pointWordEval : FreeGroup (F4Chevalley.Root × F) →* PointGroup F :=
  FreeGroup.lift (fun rt => algebraicRootElement rt.1 rt.2)

/-- Exceptional root-word evaluation directly in the literal closed carrier. -/
noncomputable def pointTwistedEval : FreeGroup (F4Chevalley.Root × F) →* PointGroup F :=
  FreeGroup.lift (fun rt => algebraicRootElement
    (exceptionalRootPermutation rt.1) (exceptionalParameter rt.1 rt.2))

@[simp] theorem pointWordEval_of (r : F4Chevalley.Root) (t : F) :
    pointWordEval (FreeGroup.of (r, t)) = algebraicRootElement r t :=
  FreeGroup.lift_apply_of

@[simp] theorem pointTwistedEval_of (r : F4Chevalley.Root) (t : F) :
    pointTwistedEval (FreeGroup.of (r, t)) =
      algebraicRootElement (exceptionalRootPermutation r) (exceptionalParameter r t) :=
  FreeGroup.lift_apply_of

theorem pointMatrix_comp_wordEval :
    (pointMatrix (F := F)).comp pointWordEval = matrixWordEval := by
  apply FreeGroup.ext_hom
  rintro ⟨r, t⟩
  simp only [MonoidHom.comp_apply, pointWordEval_of, pointMatrix_root, matrixWordEval_of]

theorem pointMatrix_comp_twistedEval :
    (pointMatrix (F := F)).comp pointTwistedEval = matrixTwistedEval := by
  apply FreeGroup.ext_hom
  rintro ⟨r, t⟩
  simp only [MonoidHom.comp_apply, pointTwistedEval_of, pointMatrix_root,
    matrixTwistedEval_of]

/-- Actual root generation makes point evaluation surjective. -/
theorem pointWordEval_surjective : Function.Surjective (pointWordEval (F := F)) := by
  apply MonoidHom.range_eq_top.mp
  exact FreeGroup.range_lift_eq_closure.trans algebraicRootElements_generate

/-- Every carrier point belongs to the actual root-generated matrix group. -/
theorem pointMatrix_mem (x : PointGroup F) : pointMatrix x ∈ matrixGroup F := by
  obtain ⟨w, rfl⟩ := pointWordEval_surjective x
  change (pointMatrix.comp pointWordEval) w ∈ matrixGroup F
  rw [pointMatrix_comp_wordEval, ← matrixWordEval_range]
  exact ⟨w, rfl⟩

/-- The specified root formula determines exceptional evaluation on all words. -/
theorem exceptional_comp_wordEval (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) : ψ.comp pointWordEval = pointTwistedEval := by
  apply FreeGroup.ext_hom
  rintro ⟨r, t⟩
  change ψ (pointWordEval (FreeGroup.of (r, t))) = pointTwistedEval (FreeGroup.of (r, t))
  rw [pointWordEval_of, pointTwistedEval_of]
  exact hψ r t

variable [CharP F 2]

/-- Every endomorphism with the exceptional formula has the same polynomial
short-coordinate comparison, independently of its construction. -/
theorem pointMatrix_intertwines (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) (x : PointGroup F) :
    quotientToIdeal * (pointMatrix x : Matrix Coordinate Coordinate F) =
      (pointMatrix (ψ x) : Matrix Coordinate Coordinate F) * quotientToIdeal := by
  obtain ⟨w, rfl⟩ := pointWordEval_surjective x
  have hψw : ψ (pointWordEval w) = pointTwistedEval w :=
    DFunLike.congr_fun (exceptional_comp_wordEval ψ hψ) w
  have hm := DFunLike.congr_fun (pointMatrix_comp_wordEval (F := F)) w
  have ht := DFunLike.congr_fun (pointMatrix_comp_twistedEval (F := F)) w
  change pointMatrix (pointWordEval w) = matrixWordEval w at hm
  change pointMatrix (pointTwistedEval w) = matrixTwistedEval w at ht
  rw [hψw, hm, ht]
  exact matrixWordEval_intertwines w

/-- Every short column of the exceptional image is read directly from the
long quotient block of the input matrix. -/
theorem pointMatrix_exceptional_short_column (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) (x : PointGroup F)
    (i j : Coordinate) (hj : IsShortCoordinate j) :
    (pointMatrix (ψ x) : Matrix Coordinate Coordinate F) i j =
      if IsShortCoordinate i then
        (pointMatrix x : Matrix Coordinate Coordinate F)
          (coordinatePermutation i) (coordinatePermutation j) else 0 := by
  have hn : ¬IsShortCoordinate (coordinatePermutation j) := by
    simpa only [coordinatePermutation_short_iff, not_not] using hj
  have h := congrArg (fun A : Matrix Coordinate Coordinate F =>
    A i (coordinatePermutation j)) (pointMatrix_intertwines ψ hψ x)
  simpa only [quotientToIdeal_mul, mul_quotientToIdeal, if_neg hn,
    coordinatePermutation_involutive j] using h.symm

/-- Matrix faithfulness descends relations in the literal carrier. -/
theorem pointWordEval_ker_le (htransport : HasShortAdjointTransport F) :
    (pointWordEval (F := F)).ker ≤ (pointTwistedEval (F := F)).ker := by
  intro w hw
  apply pointMatrix_injective
  rw [map_one]
  change (pointMatrix.comp pointTwistedEval) w = 1
  rw [pointMatrix_comp_twistedEval]
  apply matrixWordEval_ker_le htransport
  change matrixWordEval w = 1
  rw [← pointMatrix_comp_wordEval]
  change pointMatrix (pointWordEval w) = 1
  change pointWordEval w = 1 at hw
  rw [hw, map_one]

/-- Descent to a genuine point endomorphism. Restricted adjoint transport must
still be supplied, and no regularity is asserted by this definition. -/
noncomputable def pointEndomorphismOfShortTransport
    (htransport : HasShortAdjointTransport F) : Monoid.End (PointGroup F) :=
  pointWordEval.liftOfSurjective pointWordEval_surjective
    ⟨pointTwistedEval, pointWordEval_ker_le htransport⟩

theorem pointEndomorphismOfShortTransport_word (htransport : HasShortAdjointTransport F)
    (w : FreeGroup (F4Chevalley.Root × F)) :
    pointEndomorphismOfShortTransport htransport (pointWordEval w) = pointTwistedEval w := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The descended point map has the exact source root formula. -/
theorem pointEndomorphismOfShortTransport_rootFormula
    (htransport : HasShortAdjointTransport F) :
    HasExceptionalRootFormula (pointEndomorphismOfShortTransport htransport) := by
  intro r t
  rw [← pointWordEval_of, pointEndomorphismOfShortTransport_word, pointTwistedEval_of]

end Points
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism
