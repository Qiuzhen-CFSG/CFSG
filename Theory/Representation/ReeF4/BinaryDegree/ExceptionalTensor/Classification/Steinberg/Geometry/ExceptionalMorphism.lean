module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.WordDescent
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.ShortTransport
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism.PolynomialRegularity

/-!
# Construction of the exceptional algebraic F4 morphism

Over every algebraically closed field of characteristic two, `morphism` is an
algebraic-group endomorphism of the literal closed F4 Chevalley carrier. On a
long root it changes the root and preserves the parameter; on a short root it
changes the root and squares the parameter. In particular the construction
applies to the algebraic closure of every finite characteristic-two field.

Unconditional adjoint transport supplies faithfulness on the short ideal and
therefore descends exceptional substitution in root words to a point
endomorphism. The short columns of its matrix and its inverse then recover
every matrix entry polynomially; the auxiliary presented coordinate is the
determinant of the inverse matrix. This gives polynomial regularity on every
coordinate, with no remaining transport or relation-preservation premise.
The results in `Geometry.Basic` give uniqueness, bijectivity, the square
identity with Frobenius, and the Steinberg property.

Sources: Steinberg, *Lectures on Chevalley Groups*, Theorem 28
(`refs/KGroup/GLS3/Chapter2St1.tex`); GLS3, Theorem 1.15.4(b)
(`refs/KGroup/GLS3/Chapter1.tex`).
-/

public section

open Theory.AlgebraicGroup

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism

universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- Exceptional substitution descends unconditionally to the actual point group. -/
noncomputable def pointEndomorphism : Monoid.End (PointGroup F) :=
  pointEndomorphismOfShortTransport hasShortAdjointTransport

/-- The descended endomorphism has the prescribed formula on every root curve. -/
theorem pointEndomorphism_rootFormula :
    HasExceptionalRootFormula (pointEndomorphism (F := F)) :=
  pointEndomorphismOfShortTransport_rootFormula hasShortAdjointTransport

/-- The exceptional algebraic endomorphism of the literal closed F4 carrier. -/
noncomputable def morphism :
    Theory.AlgebraicGroup.Morphism
      (F4Chevalley.Carrier (k := F)) (F4Chevalley.Carrier (k := F)) where
  toVariety :=
    { toFun := pointEndomorphism
      regular := exceptional_polynomial_regularity hasShortAdjointTransport
        pointEndomorphism pointEndomorphism_rootFormula }
  map_one := pointEndomorphism.map_one
  map_mul := pointEndomorphism.map_mul

/-- The algebraic morphism realizes the constructed point endomorphism. -/
@[simp] theorem morphism_onPoints :
    (morphism (F := F)).onPoints = pointEndomorphism := by
  ext x
  rfl

/-- The actual algebraic morphism satisfies Steinberg's exceptional root formula. -/
theorem morphism_rootFormula :
    HasExceptionalRootFormula (morphism (F := F)).onPoints :=
  pointEndomorphism_rootFormula

/-- The exceptional formula on each literal algebraic root element. -/
theorem morphism_root (r : F4Chevalley.Root) (t : F) :
    morphism.onPoints (algebraicRootElement r t) =
      algebraicRootElement (exceptionalRootPermutation r) (exceptionalParameter r t) :=
  morphism_rootFormula r t

/-- The exceptional morphism is an automorphism of the abstract point group. -/
theorem morphism_bijective : Function.Bijective (morphism (F := F)).onPoints :=
  exceptional_bijective morphism.onPoints morphism_rootFormula

/-- Squaring the exceptional algebraic morphism gives coordinate Frobenius. -/
theorem morphism_square :
    (morphism (F := F)).comp morphism = frobeniusMorphism :=
  exceptional_morphism_square morphism morphism_rootFormula

/-- The constructed algebraic morphism is surjective with finite fixed group. -/
theorem morphism_isSteinberg : IsAlgebraicSteinbergEndomorphism (morphism (F := F)) :=
  exceptional_isSteinberg morphism morphism_rootFormula

/-- The root formula determines the algebraic morphism uniquely. -/
theorem morphism_unique
    (Ψ : Theory.AlgebraicGroup.Morphism
      (F4Chevalley.Carrier (k := F)) (F4Chevalley.Carrier (k := F)))
    (hΨ : HasExceptionalRootFormula Ψ.onPoints) : Ψ = morphism := by
  apply Theory.AlgebraicGroup.Morphism.ext
  funext x
  exact DFunLike.congr_fun (exceptional_unique Ψ.onPoints morphism.onPoints
    hΨ morphism_rootFormula) x

/-- Existence and uniqueness of the exceptional algebraic morphism, with no
additional existence, transport, relation-preservation, or regularity premise. -/
theorem existsUnique_morphism :
    ∃! Ψ : Theory.AlgebraicGroup.Morphism
      (F4Chevalley.Carrier (k := F)) (F4Chevalley.Carrier (k := F)),
      HasExceptionalRootFormula Ψ.onPoints :=
  ⟨morphism, morphism_rootFormula, morphism_unique⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.ExceptionalMorphism
