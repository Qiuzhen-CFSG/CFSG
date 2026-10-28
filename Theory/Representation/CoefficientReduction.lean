module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Trace

/-!
# Coefficient maps for finite matrix representations

A ring homomorphism acts on the entries of the matrices of a representation
on a finite coordinate module. This constructs reduction modulo a prime as
well as scalar extension. The characteristic polynomial and group-algebra
action commute with the coefficient map. In particular, an identity detected
after an embedding holds integrally and survives every reduction.

These are the matrix identities underlying integral lattice reduction in
Serre, *Linear Representations of Finite Groups*, Chapter 15. Unlike transport
along a field isomorphism, the coefficient map here may have a kernel.
-/

public section

noncomputable section
open scoped BigOperators
namespace Representation
variable {R S G ι : Type*} [CommRing R] [CommRing S] [Monoid G]
  [Fintype ι] [DecidableEq ι]

/-- Apply a ring homomorphism to every entry of the action matrices. -/
@[expose] def mapCoefficients (f : R →+* S) (ρ : Representation R G (ι → R)) :
    Representation S G (ι → S) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    (f.mapMatrix.toMonoidHom.comp (LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp ρ))

@[simp] theorem mapCoefficients_toMatrix (f : R →+* S)
    (ρ : Representation R G (ι → R)) (g : G) :
    LinearMap.toMatrix' (mapCoefficients f ρ g) = (LinearMap.toMatrix' (ρ g)).map f := by
  exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _

/-- Traces commute with coefficient extension or reduction. -/
theorem mapCoefficients_trace (f : R →+* S)
    (ρ : Representation R G (ι → R)) (g : G) :
    LinearMap.trace S _ (mapCoefficients f ρ g) = f (LinearMap.trace R _ (ρ g)) := by
  rw [LinearMap.trace_eq_matrix_trace S (Pi.basisFun S ι),
    LinearMap.trace_eq_matrix_trace R (Pi.basisFun R ι)]
  change (LinearMap.toMatrix' (mapCoefficients f ρ g)).trace =
    f (LinearMap.toMatrix' (ρ g)).trace
  rw [mapCoefficients_toMatrix, AddMonoidHom.map_trace]

theorem mapCoefficients_charpoly (f : R →+* S)
    (ρ : Representation R G (ι → R)) (g : G) :
    (mapCoefficients f ρ g).charpoly = (ρ g).charpoly.map f := by
  rw [← LinearMap.charpoly_toMatrix (mapCoefficients f ρ g) (Pi.basisFun S ι),
    ← LinearMap.charpoly_toMatrix (ρ g) (Pi.basisFun R ι)]
  change (LinearMap.toMatrix' (mapCoefficients f ρ g)).charpoly =
    (LinearMap.toMatrix' (ρ g)).charpoly.map f
  rw [mapCoefficients_toMatrix]
  exact Matrix.charpoly_map _ _

theorem mapCoefficients_asAlgebraHom (f : R →+* S)
    (ρ : Representation R G (ι → R)) (a : MonoidAlgebra R G) :
    LinearMap.toMatrix' ((mapCoefficients f ρ).asAlgebraHom
      (MonoidAlgebra.mapRingHom G f a)) =
      (LinearMap.toMatrix' (ρ.asAlgebraHom a)).map f := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, ha, hb]
    ext i j
    simp
  | single g r =>
    simp only [MonoidAlgebra.mapRingHom_single, asAlgebraHom_single, map_smul,
      mapCoefficients_toMatrix]
    ext i j
    simp [Matrix.map_apply, map_mul]

/-- An integral identity is preserved by coefficient reduction. -/
theorem mapCoefficients_asAlgebraHom_eq_one (f : R →+* S)
    (ρ : Representation R G (ι → R)) (a : MonoidAlgebra R G)
    (ha : ρ.asAlgebraHom a = 1) :
    (mapCoefficients f ρ).asAlgebraHom (MonoidAlgebra.mapRingHom G f a) = 1 := by
  apply LinearMap.toMatrix'.injective
  rw [mapCoefficients_asAlgebraHom, ha]
  simp

/-- An embedding detects the integral identity before reduction. -/
theorem asAlgebraHom_eq_one_of_mapCoefficients (f : R →+* S)
    (hf : Function.Injective f) (ρ : Representation R G (ι → R))
    (a : MonoidAlgebra R G)
    (ha : (mapCoefficients f ρ).asAlgebraHom (MonoidAlgebra.mapRingHom G f a) = 1) :
    ρ.asAlgebraHom a = 1 := by
  have hinj : Function.Injective (f.mapMatrix : Matrix ι ι R → Matrix ι ι S) := by
    intro M N h
    ext i j
    exact hf (congrFun (congrFun h i) j)
  apply LinearMap.toMatrix'.injective
  apply hinj
  change (LinearMap.toMatrix' (ρ.asAlgebraHom a)).map f =
    (LinearMap.toMatrix' 1).map f
  rw [← mapCoefficients_asAlgebraHom, ha]
  simp

end Representation
