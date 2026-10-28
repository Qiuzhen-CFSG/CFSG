module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Index
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120.Code

/-!
# Native fifth-exterior coordinates and their compound matrices

The public code basis from the independently proved `Native120.Code` consists
of native Golay rows 0 through 10 modulo constants. Its generator matrices are
exactly the eleven-dimensional matrices published for this construction.
Reindexing Mathlib's exterior basis by `fiveSubsetEquiv` gives actual coordinates
on the fifth exterior power of that quotient. The exterior pairing computes
each matrix entry as a minor; transposing the pairing's matrix gives precisely
the required column convention.

Only the finite equality of these compound matrices with the saved exterior
rows remains explicit in `of_compoundCertificates`. No degree-120 or degree-220
realization, irreducibility, presentation, or spectrum result is used.

Sources: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1;
`NativeActions/source/README.md` fixes the literal native generators and order.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates
open MathieuCode Sporadic.Mathieu
open scoped BigOperators

/-- Reuse the certified first eleven Golay rows modulo the constant line. -/
abbrev nativeCodeBasis := Degrees120252.Native120.codeBasis

lemma nativeCodeBasis_generator (b : Bool) :
    LinearMap.toMatrix nativeCodeBasis nativeCodeBasis
      (codeRepresentation (if b then generatorB else generatorA)) = codeMatrix b := by
  have hm : ∀ b : Bool,
      Degrees120252.Native120.codeMatrix (if b then 1 else 0) = codeMatrix b := by
    decide +kernel
  have ha : (if b then generatorB else generatorA) =
      Degrees120252.actor (if b then 1 else 0) := by cases b <;> rfl
  rw [ha, ← hm b]
  rw [← Degrees120252.Native120.coordinateCodeRepresentation_actor]
  ext i j
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix'_apply,
    Degrees120252.Native120.coordinateCodeRepresentation_single,
    Degrees120252.Native120.codeBasis_apply]
  rfl

/-- Literal fifth compound matrix in the published order and column convention. -/
def compoundMatrix (M : Matrix (Fin 11) (Fin 11) (ZMod 2)) :
    Matrix (Fin 462) (Fin 462) (ZMod 2) :=
  fun i j => (M.submatrix (fiveTuple i) (fiveTuple j)).det

/-- Wedges of the native Golay-row quotient basis in lexicographic order. -/
def nativeExteriorBasis : Module.Basis (Fin 462) (ZMod 2) (⋀[ZMod 2]^5 Code) :=
  (nativeCodeBasis.exteriorPower 5).reindex fiveSubsetEquiv.symm

/-- Coordinates of the genuine fifth exterior power of the native code. -/
def coordinateEquiv : (⋀[ZMod 2]^5 Code) ≃ₗ[ZMod 2] (Fin 462 → ZMod 2) :=
  nativeExteriorBasis.equivFun

lemma nativeExteriorBasis_apply (i : Fin 462) :
    nativeExteriorBasis i = exteriorPower.ιMulti (ZMod 2) 5
      (fun k => nativeCodeBasis (fiveTuple i k)) := by
  rw [nativeExteriorBasis, Module.Basis.reindex_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family]
  simp only [Equiv.symm_symm, fiveSubsetEquiv_embedding]
  rfl

lemma nativeExteriorBasis_matrix (g : M24) :
    LinearMap.toMatrix nativeExteriorBasis nativeExteriorBasis (exteriorRepresentation g) =
      compoundMatrix (LinearMap.toMatrix nativeCodeBasis nativeCodeBasis
        (codeRepresentation g)) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (nativeCodeBasis.exteriorPower 5).repr
    (exteriorRepresentation g (nativeExteriorBasis j)) (fiveSubsetEquiv i) = _
  rw [exteriorPower.basis_repr_apply, nativeExteriorBasis_apply]
  change exteriorPower.ιMultiDual (ZMod 2) 5 nativeCodeBasis (fiveSubsetEquiv i)
    (exteriorPower.map 5 (codeRepresentation g)
      (exteriorPower.ιMulti (ZMod 2) 5 _)) = _
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [fiveSubsetEquiv_embedding, Function.comp_apply, Module.Basis.coord_apply]
  change (Matrix.of (fun k l : Fin 5 =>
    nativeCodeBasis.repr (codeRepresentation g (nativeCodeBasis (fiveTuple j k)))
      (fiveTuple i l))).det = _
  rw [← Matrix.det_transpose]
  unfold compoundMatrix
  congr 1
  ext k l
  simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.submatrix_apply,
    LinearMap.toMatrix_apply]

private lemma toMatrix_equivFun {n : ℕ} {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (b : Module.Basis (Fin n) (ZMod 2) V) (f : Module.End (ZMod 2) V) :
    LinearMap.toMatrix' (b.equivFun.conjRingEquiv f) = LinearMap.toMatrix b b f := by
  ext i j
  rw [LinearMap.toMatrix'_apply, LinearMap.toMatrix_apply]
  change b.equivFun (f (b.equivFun.symm (Pi.single j 1))) i = b.repr (f (b j)) i
  have hj : b.equivFun.symm (Pi.single j 1) = b j := by
    simp [Module.Basis.equivFun_symm_apply, Pi.single_apply]
  rw [hj]
  rfl

lemma coordinateEquiv_matrix (g : M24) :
    LinearMap.toMatrix' (coordinateEquiv.conjRingEquiv (exteriorRepresentation g)) =
      compoundMatrix (LinearMap.toMatrix nativeCodeBasis nativeCodeBasis
        (codeRepresentation g)) :=
  (toMatrix_equivFun nativeExteriorBasis (exteriorRepresentation g)).trans
    (nativeExteriorBasis_matrix g)

lemma coordinateEquiv_generator (b : Bool) :
    LinearMap.toMatrix' (coordinateEquiv.conjRingEquiv
      (exteriorRepresentation (if b then generatorB else generatorA))) =
        compoundMatrix (codeMatrix b) := by
  rw [coordinateEquiv_matrix, nativeCodeBasis_generator]

/-- The exact finite comparison still needed to identify the saved exterior rows. -/
def CompoundCertificates : Prop :=
  ∀ b : Bool, compoundMatrix (codeMatrix b) = exteriorMatrix b

/-- Construct the published native-coordinate contract from the literal minor identities. -/
def of_compoundCertificates (h : CompoundCertificates) :
    NativeActions.ExteriorCoordinates where
  equiv := coordinateEquiv
  first := (coordinateEquiv_generator false).trans (h false)
  second := (coordinateEquiv_generator true).trans (h true)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates
