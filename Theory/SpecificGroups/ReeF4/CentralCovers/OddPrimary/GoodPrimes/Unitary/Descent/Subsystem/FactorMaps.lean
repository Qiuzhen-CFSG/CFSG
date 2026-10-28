module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ScalarKernel
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.RootTwist

/-!
# From the short SL₃ matrix chart to the two actual F₄ factors

Generation places a marked short-factor matrix homomorphism in the literal
closed F₄ carrier. Apply inverse field Frobenius, the exceptional isogeny,
and the certified Weyl placement to obtain the long factor with unchanged
root parameters. Both maps remain faithful; their root formulas supply the
commutation and diagonal-kernel results of `ScalarKernel`.
Source: GLS3 §2.6.2 and Example 2.6.3.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
open ReeF4.CentralCovers.OddPrimary.Cyclotomic
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.RestrictedCells
open TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2
variable {F : Type*} [Field F]

/-- Entrywise coefficient maps preserve every marked elementary generator. -/
theorem map_simpleGenerator {E : Type*} [Field E] (f : F →+* E)
    (s k : Bool) (t : F) :
    Matrix.SpecialLinearGroup.map f (simpleGenerator s k t) = simpleGenerator s k (f t) := by
  cases s <;> cases k <;> apply Subtype.ext
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> simp [simpleGenerator, modelGenerator, Matrix.SpecialLinearGroup.map_apply_coe,
      Matrix.SpecialLinearGroup.transvection_coe]

/-- Entrywise maps along field embeddings are injective on full SL₃. -/
theorem sl_map_injective {E : Type*} [Field E] (f : F →+* E) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 3) f) := by
  intro A B h
  ext i j
  exact f.injective (congrArg (fun C : SL3 E => C i j) h)

variable [IsAlgClosed F] [CharP F 2]

abbrev MatrixUnit := (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ

omit [CharP F 2] in
/-- The marked matrix image belongs to the actual algebraic carrier by generation. -/
theorem matrixMap_mem_range (f : SL3 F →* MatrixUnit)
    (hr : ∀ s k t, f (simpleGenerator s k t) =
      F4Chevalley.rootCurve (signedRoot s (shortRoot k)) t) (A : SL3 F) :
    f A ∈ (literalMatrix (k := F)).range := by
  have ht : (literalMatrix.range).comap f = ⊤ := by
    apply model_generates F
    intro s k t
    exact ⟨rootPoint (signedRoot s (shortRoot k)) t,
      (literalMatrix_rootPoint _ _).trans (hr s k t).symm⟩
  exact show A ∈ (literalMatrix.range).comap f from ht ▸ mem_top A

/-- Convert the concrete marked matrices to points of the closed root-generated F₄. -/
def pointMap (f : SL3 F →* MatrixUnit)
    (hr : ∀ s k t, f (simpleGenerator s k t) =
      F4Chevalley.rootCurve (signedRoot s (shortRoot k)) t) :
    SL3 F →* AlgebraicPoints F :=
  (MonoidHom.ofInjective literalMatrix_injective).symm.toMonoidHom.comp
    (f.codRestrict literalMatrix.range (matrixMap_mem_range f hr))

omit [CharP F 2] in
@[simp] theorem pointMap_matrix (f : SL3 F →* MatrixUnit)
    (hr : ∀ s k t, f (simpleGenerator s k t) =
      F4Chevalley.rootCurve (signedRoot s (shortRoot k)) t) (A : SL3 F) :
    literalMatrix (pointMap f hr A) = f A := by
  exact congrArg Subtype.val ((MonoidHom.ofInjective literalMatrix_injective).apply_symm_apply
    (⟨f A, matrixMap_mem_range f hr A⟩ : literalMatrix.range))

omit [CharP F 2] in
theorem pointMap_injective (f : SL3 F →* MatrixUnit)
    (hr : ∀ s k t, f (simpleGenerator s k t) =
      F4Chevalley.rootCurve (signedRoot s (shortRoot k)) t)
    (hi : Function.Injective f) : Function.Injective (pointMap f hr) := by
  intro A B h
  apply hi
  simpa only [pointMap_matrix] using congrArg literalMatrix h

omit [CharP F 2] in
theorem pointMap_marked (f : SL3 F →* MatrixUnit)
    (hr : ∀ s k t, f (simpleGenerator s k t) =
      F4Chevalley.rootCurve (signedRoot s (shortRoot k)) t) :
    MarkedMap (pointMap f hr) shortRoot := by
  intro s k t
  apply literalMatrix_injective
  rw [pointMap_matrix, hr, literalMatrix_rootPoint]

/-- The long factor, with parameter squaring undone before the exceptional map. -/
def longMap (S : SL3 F →* AlgebraicPoints F) : SL3 F →* AlgebraicPoints F :=
  ((MulAut.conj (wordElement (F := F) placementWord)).toMonoidHom.comp exceptionalPointEnd).comp
    (S.comp (Matrix.SpecialLinearGroup.map (frobeniusEquiv F 2).symm.toRingHom))

theorem longMap_injective (S : SL3 F →* AlgebraicPoints F) (hi : Function.Injective S) :
    Function.Injective (longMap S) :=
  (MulAut.conj (wordElement placementWord)).injective.comp
    (ExceptionalMorphism.morphism_bijective.injective.comp
      (hi.comp (sl_map_injective (frobeniusEquiv F 2).symm.toRingHom)))

theorem longMap_marked {S : SL3 F →* AlgebraicPoints F} (hs : MarkedMap S shortRoot) :
    MarkedMap (longMap S) longRoot := by
  intro s k t
  change wordElement placementWord *
      exceptionalPointEnd (S (Matrix.SpecialLinearGroup.map (frobeniusEquiv F 2).symm.toRingHom
        (simpleGenerator s k t))) * (wordElement placementWord)⁻¹ = _
  rw [map_simpleGenerator, hs]
  have ht : ((frobeniusEquiv F 2).symm.toRingHom t) ^ 2 = t :=
    frobeniusEquiv_symm_pow_p F 2 t
  rw [exceptional_rootPoint, exceptionalParameter_of_short (signed_short s k),
    ht, wordElement_root]
  congr 1
  cases s <;>
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte,
      ReeF4.WordRelations.exceptionalRootPermutation_neg, rootWord_neg, placement_target]

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
