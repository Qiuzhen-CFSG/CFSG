module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootPlanePresentation
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CorootSquares
public import Theory.AlgebraicGroup.RootSystems.F4RootLattice
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Faithful parameters for the literal F4 coroot matrices

Field maps preserve the integral root curves and the diagonal torus. Passing to
an algebraic closure therefore extends the checked coroot-word identity on
squares to every unit of the original field. This avoids a square-root
assumption over finite odd fields, in particular over F3.

A torus parameter defines a character of the integral weight lattice. If its
matrix is the identity, that character kills every root. The proved equality
of the F4 root and weight lattices makes the character trivial on each dual
simple-coroot coordinate, recovering all four parameters. The final theorem
identifies this faithful diagonal with the actual six-letter words.

Source: Steinberg, *Lectures on Chevalley Groups*, §3, Lemma 28 and
Theorem 8 (`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

open RootPairing.IntegralGeckConstruction
open ExceptionalSplit.TheoremDRootNormalizer
open Theory.AlgebraicGroup.StandardRootSystem
@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _

variable {F K : Type*} [Field F] [Field K]
private abbrev P := typeF4RootPairing
private abbrev b := typeF4RootPairing_base
private abbrev Idx := typeF4RootPairing_base.support ⊕ typeF4Roots

private def matMap (f : F →+* K) : (Matrix Idx Idx F)ˣ →* (Matrix Idx Idx K)ˣ :=
  Units.map (f.mapMatrix : Matrix Idx Idx F →+* Matrix Idx Idx K).toMonoidHom

private lemma map_root (f : F →+* K) (r : typeF4Roots) (t : F) :
    matMap f (rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) r t) =
      rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) r (f t) := by
  apply Units.ext
  ext i j
  simp [matMap, rootCurveUnit, rootCurveMatrix, specializeMatrix,
    Matrix.one_apply, apply_ite f]

private lemma map_torus (f : F →+* K) (u : b.support → Fˣ) :
    matMap f (integralChevalleyTorusElement (P := P) u) =
      integralChevalleyTorusElement (P := P) (fun i => Units.map f.toMonoidHom (u i)) := by
  apply Units.ext
  ext i j
  simp [matMap, integralChevalleyTorusElement, Matrix.diagonal_apply,
    chevalleyBasisTorusUnit]

private lemma map_h (f : F →+* K) (r : typeF4Roots) (t : F) :
    matMap f (matrixH (b := b) r t) = matrixH (b := b) r (f t) := by
  simp [matrixH, matrixN, map_root]

/-- The rank-one matrix identity holds over every field, including odd fields. -/
theorem rootPlane_matrixH_simple (i : typeF4RootPairing_base.support) (t : Fˣ) :
    matrixH (b := typeF4RootPairing_base) (F := F) i t =
      integralChevalleyTorusElement (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter i t⁻¹) := by
  let f := algebraMap F (AlgebraicClosure F)
  let t' : (AlgebraicClosure F)ˣ := Units.map f.toMonoidHom t
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (t' : AlgebraicClosure F)
    (by decide : 0 < 2)
  have hane : a ≠ 0 := by
    intro hz
    exact t'.ne_zero (by simpa [hz] using ha.symm)
  let u : (AlgebraicClosure F)ˣ := Units.mk0 a hane
  have hu : u ^ 2 = t' := Units.ext ha
  have h := TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CorootMatrices.matrixH_square
    (b := b) i u
  have h' : matrixH (b := b) (F := AlgebraicClosure F) i t' =
      integralChevalleyTorusElement (P := P)
        (integralChevalleySimpleCorootParameter i t'⁻¹) := by
    simpa only [← Units.val_pow_eq_pow_val, hu] using h
  apply (Units.map_injective (f := f.mapMatrix.toMonoidHom)
    (Matrix.map_injective f.injective))
  change matMap f _ = matMap f _
  rw [map_h, map_torus]
  have hp : (fun j => Units.map f.toMonoidHom (integralChevalleySimpleCorootParameter i t⁻¹ j)) =
      integralChevalleySimpleCorootParameter i t'⁻¹ := by
    funext j
    by_cases hji : j = i <;> simp [integralChevalleySimpleCorootParameter, t', hji]
  rw [hp]
  exact h'

private def weightEval (u : b.support → Fˣ) : typeF4WeightModule →+ Additive Fˣ where
  toFun w := Additive.ofMul (∏ i : b.support, u i ^ w (P.corootSpanMem ℤ i))
  map_zero' := by simp
  map_add' w z := by simp [zpow_add, Finset.prod_mul_distrib]

private lemma weightEval_root (u : b.support → Fˣ) (r : typeF4Roots) :
    weightEval u (typeF4RootWeight r) =
      Additive.ofMul (integralChevalleyRootScale (P := P) u r) := by
  simp [weightEval, typeF4RootWeight, integralChevalleyRootScale]

private lemma torus_faithful (u : b.support → Fˣ)
    (h : integralChevalleyTorusElement (P := P) u = 1) : u = 1 := by
  have hr := (integralChevalleyTorusElement_eq_one_iff_rootScale_eq_one u).mp h
  have hk : typeF4RootLattice ≤ (weightEval u).ker := by
    change AddSubgroup.closure (Set.range typeF4RootWeight) ≤ _
    rw [AddSubgroup.closure_le]
    rintro _ ⟨r, rfl⟩
    change weightEval u (typeF4RootWeight r) = 0
    rw [weightEval_root, hr]
    rfl
  rw [typeF4_rootLattice_eq_weightLattice] at hk
  let B : Module.Basis b.support ℤ (P.corootSpan ℤ) := b.flip.toWeightBasisInt
  funext i
  have he := hk (show B.coord i ∈ typeF4WeightLattice from trivial)
  change weightEval u (B.coord i) = 0 at he
  have hb (j : b.support) :
      P.corootSpanMem ℤ j = B j := by
    apply Subtype.ext
    exact (RootPairing.Base.coe_toWeightBasisInt_apply b.flip j).symm
  change (∏ j : b.support, u j ^ (B.coord i) (P.corootSpanMem ℤ j)) = 1 at he
  have hc (j : b.support) :
      (B.coord i) (P.corootSpanMem ℤ j) =
        if j = i then 1 else 0 := by
    rw [hb]
    change B.repr (B j) i = _
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
  simp only [hc] at he
  simpa using he

variable (F : Type*) [Field F]

/-- The diagonal torus with the parameters of the six-letter coroot words. -/
def rootTorusMatrixHom : (Fin 4 → Fˣ) →*
    (Matrix (typeF4RootPairing_base.support ⊕ typeF4Roots)
      (typeF4RootPairing_base.support ⊕ typeF4Roots) F)ˣ where
  toFun u := integralChevalleyTorusElement (P := typeF4RootPairing)
    (fun q => (u (typeF4RootPairing_baseEquiv.symm q))⁻¹)
  map_one' := integralChevalleyTorusElement_one
  map_mul' u v := by
    rw [← integralChevalleyTorusElement_mul]
    congr 1
    funext q
    simp only [Pi.mul_apply, mul_inv_rev]
    exact mul_comm _ _

/-- F4 root-lattice equality makes the literal torus parameter map faithful. -/
theorem rootTorusMatrixHom_injective : Function.Injective (rootTorusMatrixHom F) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro u hu
  have hc := torus_faithful _ (show integralChevalleyTorusElement (P := P)
    (fun q => (u (typeF4RootPairing_baseEquiv.symm q))⁻¹) = 1 from hu)
  funext i
  have hi := congrFun hc (typeF4RootPairing_baseEquiv i)
  simpa using hi

/-- The six-letter word evaluates to the corresponding actual diagonal matrix. -/
theorem rootHWord_matrix (i : Fin 4) (t : Fˣ) :
    (rootEvaluation F (rootHWord F (sourceIndex i) t)).val =
      rootTorusMatrixHom F (Pi.mulSingle i t) := by
  have hm : (rootEvaluation F (rootHWord F (sourceIndex i) t)).val =
      matrixH (b := b) (F := F) (sourceIndex i) t := by
    simp only [rootHWord, rootNWord, map_mul, rootEvaluation_of, Subgroup.coe_mul]
    rfl
  rw [hm, rootPlane_matrixH_simple]
  change integralChevalleyTorusElement (P := P) _ = integralChevalleyTorusElement (P := P) _
  congr 1
  funext j
  have he : typeF4RootPairing_baseEquiv.symm j = i ↔ j = sourceIndex i :=
    typeF4RootPairing_baseEquiv.symm_apply_eq
  by_cases hji : j = sourceIndex i <;>
    simp [integralChevalleySimpleCorootParameter, he, hji]

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
