module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagData
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.Ambient
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.Degenerate
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ExteriorRegularity
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.ClosedOrbit

/-!
# Complete full-flag geometry with its regular representation action

The ambient product is a genuine complete reduced separated finite-type scheme,
and `flagEmbedding` is injective and equivariant for the exterior action.
The Plücker/incidence rank conditions identify its rational-point image with
a closed locus, whose reduced closed subscheme carries the restricted regular
action. Its rational points are equivalent to exactly the original
natural-indexed `FullFlag`.

The final theorem `nonempty_flagModel` discharges both inputs to the assembly:
`ClosedImage` proves the incidence comparison and closedness, while
`ExteriorRegularity` proves rationality of the exterior powers using polynomial
matrix minors. Thus every rational representation admits a complete flag model,
without faithfulness or connectedness assumptions. Dimension zero is included:
the empty ambient product is the complete point scheme `Spec k`.

Source: Borel, *Linear Algebraic Groups*, §11.1, the flag variety used before
closed-orbit selection. No Borel subgroup or fixed-point premise is used.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped ExteriorAlgebra LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry

open Variety.Geometric

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {G : Variety k} [AlgebraicGroup G]

/-- Construct the flag model from closedness of the actual Plücker image and
algebraic morphisms inducing the actual exterior-power operators. -/
public theorem nonempty_flagModel_of_closed_plucker
    (ρ : RationalRepresentation G V) (b : CoordinateBases (k := k) V)
    (φ : (i : Fin (Module.finrank k V)) →
      Theory.AlgebraicGroup.Morphism G (glVarietyOf k (⋀[k]^(i : ℕ) V)))
    (hφ : ∀ i g, glPointEquivOf k _ (b i) ((φ i).onPoints g) =
      (exteriorPowerRepresentation ρ i).action g)
    (Z : Closeds (flagAmbient (k := k) V).toScheme)
    (hZ : ∀ x : Point (flagAmbient (k := k) V),
      x.1 (IsLocalRing.closedPoint k) ∈ Z ↔ x ∈ Set.range (flagEmbedding b)) :
    Nonempty (FlagModel ρ) := by
  classical
  let A := ambientAction φ
  have hstable (g : Variety.Point G) (x : Point (flagAmbient (k := k) V))
      (hx : x.1 (IsLocalRing.closedPoint k) ∈ Z) :
      (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∈ Z := by
    obtain ⟨F, rfl⟩ := (hZ x).mp hx
    exact (hZ _).mpr ⟨(flagAction ρ).smul g F,
      flagEmbedding_equivariant ρ b φ hφ g F⟩
  let C := reducedClosedSubvariety (flagAmbient (k := k) V) Z
  have hinj : Function.Injective C.inclusion := by
    intro x y hxy
    apply Subtype.ext
    apply (cancel_mono C.inclusion.hom).mp
    exact congrArg Subtype.val hxy
  have hmem (x : Point C.toGeometric) :
      (C.inclusion x).1 (IsLocalRing.closedPoint k) ∈ Z := by
    apply (point_mem_reducedClosedSubvariety_iff _ Z _).mpr
    exact ⟨x, rfl, fun y hy => hinj hy⟩
  have hex (x : Point C.toGeometric) :
      ∃ F : FullFlag k V, flagEmbedding b F = C.inclusion x :=
    (hZ _).mp (hmem x)
  let f : Point C.toGeometric → FullFlag k V := fun x => (hex x).choose
  have hf (x : Point C.toGeometric) : flagEmbedding b (f x) = C.inclusion x :=
    (hex x).choose_spec
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply hinj
      rw [← hf x, ← hf y, hxy]
    · intro F
      obtain ⟨x, hx, _⟩ := (point_mem_reducedClosedSubvariety_iff _ Z _).mp
        ((hZ (flagEmbedding b F)).mpr ⟨F, rfl⟩)
      refine ⟨x, (flagEmbedding_injective b) ?_⟩
      exact (hf x).trans hx
  let R := A.onInvariantReducedClosedSubvariety Z hstable
  refine ⟨{
    variety := C.toGeometric
    action := R
    pointEquiv := Equiv.ofBijective f hbij
    equivariant := ?_
    complete := C.isComplete (flagAmbient_isComplete V) }⟩
  intro g x
  change f (R.toMulAction.smul g x) = (flagAction ρ).smul g (f x)
  apply flagEmbedding_injective b
  rw [hf, flagEmbedding_equivariant ρ b φ hφ g (f x), hf]
  exact A.onInvariantReducedClosedSubvariety_inclusion Z hstable g x

/-- Final assembly of the two independent geometric prerequisites. Rationality
of exterior powers and closedness of the Plücker image remain explicit here. -/
public theorem nonempty_flagModel_of_plucker_prerequisites
    (ρ : RationalRepresentation G V)
    (hExterior : ∀ i : Fin (Module.finrank k V),
      IsRationalRepresentation (exteriorPowerRepresentation ρ i))
    (hClosed : ∀ b : CoordinateBases (k := k) V,
      ∃ Z : Closeds (flagAmbient (k := k) V).toScheme,
        ∀ x : Point (flagAmbient (k := k) V),
          x.1 (IsLocalRing.closedPoint k) ∈ Z ↔ x ∈ Set.range (flagEmbedding b)) :
    Nonempty (FlagModel ρ) := by
  classical
  choose b φ hφ using hExterior
  obtain ⟨Z, hZ⟩ := hClosed b
  exact nonempty_flagModel_of_closed_plucker ρ b φ hφ Z hZ

/-- Every rational representation has a complete geometric full-flag variety
whose regular action induces its actual general-linear action on flags.
This includes dimension zero and does not require a faithful representation
or a connected group. -/
public theorem nonempty_flagModel
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ) :
    Nonempty (FlagModel ρ) :=
  nonempty_flagModel_of_plucker_prerequisites ρ
    (fun i => exteriorPowerRepresentation_isRational ρ hρ i)
    exists_flagEmbedding_locus

end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry
