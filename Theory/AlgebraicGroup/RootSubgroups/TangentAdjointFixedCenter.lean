module

public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialIntertwining
public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialSubspace
public import Theory.AlgebraicGroup.RootSubgroups.TangentAdjoint

/-!
# Adjoint-fixed identity tangents and the Lie center

For a connected algebraic group over an algebraically closed field of
characteristic zero, an identity-point derivation is fixed by conjugation by
every group point if and only if it lies in the center of the canonical
convolution Lie algebra.

The differential/bracket calculation in `TangentAdjoint` identifies the
infinitesimal adjoint action with `E \mapsto [E,D]`.  For the nontrivial
direction, place `(1,D)` in the direct sum of the trivial and adjoint
representations.  Lie-centrality makes the differential vanish on the graph
line `k \cdot (1,D)`.  Characteristic-zero integration makes that line
group-invariant, and its first coordinate forces the resulting scalar to be
one.  The last step uses the explicit equality between the Bor1 and
RootSubgroups tangent-conjugation maps, so both identity-tangent APIs remain
interchangeable at this boundary.

This is the affine-coordinate form of `d(Ad)(D) = ad D` from Bor1 Chapter 1,
Sections 3.13--3.14, followed by the connected characteristic-zero
integration principle used in Bor1 Chapter 2, Section 7.6.  No root-subgroup
existence or multiplicity theorem, and in particular no clause of GLS3
Theorem 1.9.5, enters the proof.
-/

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {G : Variety k} [AlgebraicGroup G]

private def trivialRepresentation : RationalRepresentation G k := ⟨1⟩

omit [CharZero k] in
private theorem trivialRepresentation_isRational :
    IsRationalRepresentation (trivialRepresentation (G := G)) := by
  let e : Module.Basis (Fin (Module.finrank k k)) k k := Module.finBasis k k
  let coefficient : Fin (Module.finrank k k) → Fin (Module.finrank k k) →
      G.PolynomialFunction := fun i j =>
    algebraMap k G.PolynomialFunction (e.repr (e j) i)
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    e (trivialRepresentation (G := G)).action coefficient coefficient
    (by
      intro i j g
      rw [polynomialFunction_algebraMap_apply]
      simp [trivialRepresentation])
    (by
      intro i j g
      rw [polynomialFunction_algebraMap_apply]
      simp [trivialRepresentation])
  refine ⟨e, f, ?_⟩
  intro g
  change glPointEquivOf k k e
    (generalLinearRepresentationPoint e
      ((trivialRepresentation (G := G)).action g)) = _
  exact glPointEquivOf_generalLinearRepresentationPoint e
    ((trivialRepresentation (G := G)).action g)

omit [CharZero k] in
private theorem trivialRepresentation_differential_eq_zero
    (b : Module.Basis (Fin (Module.finrank k k)) k k)
    (f : AlgebraicGroup.Morphism G (glVarietyOf k k))
    (hf : ∀ g, glPointEquivOf k k b (f.onPoints g) =
      (trivialRepresentation (G := G)).action g)
    (D : IdentityPointDerivation G) (c : k) :
    rationalRepresentationDifferential
      (trivialRepresentation (G := G)) b f D c = 0 := by
  apply b.ext_elem
  intro i
  change b.coord i
      (rationalRepresentationDifferential
        (trivialRepresentation (G := G)) b f D c) = b.coord i 0
  rw [rationalRepresentationDifferential_linearMatrixCoefficient]
  have hCoefficient :
      rationalRepresentationLinearMatrixCoefficient
          (trivialRepresentation (G := G)) b f (b.coord i) c =
        algebraMap k G.PolynomialFunction (b.coord i c) := by
    apply Variety.PolynomialFunction.ext
    intro g
    rw [rationalRepresentationLinearMatrixCoefficient_apply
      (trivialRepresentation (G := G)) b f hf]
    rw [polynomialFunction_algebraMap_apply]
    simp [trivialRepresentation]
  rw [hCoefficient, D.map_algebraMap]
  simp

/-- For a connected algebraic group in characteristic zero, the tangents
fixed by all Bor1 point-conjugation maps are exactly the center of the
canonical RootSubgroups tangent Lie algebra. -/
public theorem identityTangent_pointwise_fixed_iff_mem_lieCenter
    (G : Variety k) [AlgebraicGroup G]
    (hG : _root_.IsConnected (Set.univ : Set (Variety.Point G)))
    (D : Theory.AlgebraicGroup.IdentityPointDerivation G) :
    (∀ g : G.Point,
        Bor1.identityTangentConjugationLinearMap G g D = D) ↔
      D ∈ LieAlgebra.center k
        (Theory.AlgebraicGroup.IdentityPointDerivation G) := by
  change Variety.IsConnected G at hG
  constructor
  · exact identityTangent_pointwise_fixed_to_mem_lieCenter G D
  · intro hD
    obtain ⟨b, f, hf⟩ :=
      Theory.AlgebraicGroup.identityTangentRepresentation_isRational G
    obtain ⟨b0, f0, hf0⟩ := trivialRepresentation_isRational (G := G)
    obtain ⟨tau, htau, htauRational⟩ :=
      rationalRepresentation_directSum_exists
        (trivialRepresentation (G := G))
        (Theory.AlgebraicGroup.identityTangentRepresentation G)
        (trivialRepresentation_isRational (G := G))
        (Theory.AlgebraicGroup.identityTangentRepresentation_isRational G)
    obtain ⟨e, q, hq⟩ := htauRational
    let W : Submodule k
        (k × Theory.AlgebraicGroup.IdentityPointDerivation G) :=
      k ∙ ((1 : k), D)
    have hstable : ∀ E v, v ∈ W →
        rationalRepresentationDifferential tau e q E v ∈ W := by
      intro E v hv
      rcases Submodule.mem_span_singleton.mp hv with ⟨c, rfl⟩
      rw [map_smul]
      suffices hzero :
          rationalRepresentationDifferential tau e q E (1, D) = 0 by
        rw [hzero, smul_zero]
        exact W.zero_mem
      apply Prod.ext
      · have hintertwines : Intertwines tau
            (trivialRepresentation (G := G)) (LinearMap.fst k k _) := by
          intro g x
          rcases x with ⟨c, X⟩
          rw [htau]
          simp [trivialRepresentation]
        have hfst := rationalRepresentationDifferential_intertwines tau
          (trivialRepresentation (G := G)) (LinearMap.fst k k _)
          hintertwines e q hq b0 f0 hf0 E (1, D)
        change (rationalRepresentationDifferential tau e q E (1, D)).1 = 0
        calc
          _ = rationalRepresentationDifferential
              (trivialRepresentation (G := G)) b0 f0 E 1 := by
            simpa only [LinearMap.fst_apply] using hfst
          _ = 0 := trivialRepresentation_differential_eq_zero b0 f0 hf0 E 1
      · have hintertwines : Intertwines tau
            (Theory.AlgebraicGroup.identityTangentRepresentation G)
            (LinearMap.snd k k _) := by
          intro g x
          rcases x with ⟨c, X⟩
          rw [htau]
          rfl
        have hsnd := rationalRepresentationDifferential_intertwines tau
          (Theory.AlgebraicGroup.identityTangentRepresentation G)
          (LinearMap.snd k k _) hintertwines e q hq b f hf E (1, D)
        change (rationalRepresentationDifferential tau e q E (1, D)).2 = 0
        calc
          _ = rationalRepresentationDifferential
              (Theory.AlgebraicGroup.identityTangentRepresentation G)
                b f E D := by
            simpa only [LinearMap.snd_apply] using hsnd
          _ = ⁅E, D⁆ :=
            Theory.AlgebraicGroup.identityTangentRepresentation_differential_apply
              G b f hf E D
          _ = 0 := by
            rw [LieModule.mem_maxTrivSubmodule] at hD
            exact hD E
    have hWinvariant : IsInvariantSubmodule tau W :=
      differential_stable_subspace_invariant tau e q hq W hG hstable
    intro g
    have hmem := hWinvariant g ((1 : k), D)
      (Submodule.mem_span_singleton_self ((1 : k), D))
    rw [htau] at hmem
    rcases Submodule.mem_span_singleton.mp hmem with ⟨c, hc⟩
    have hc1 := congrArg Prod.fst hc
    simp [trivialRepresentation] at hc1
    have hc2 := congrArg Prod.snd hc
    rw [hc1] at hc2
    simp only [one_smul] at hc2
    have haction :
        (((Theory.AlgebraicGroup.identityTangentRepresentation G).action g).1 D) =
          Theory.AlgebraicGroup.identityTangentConjugationLinearMap G g D := by
      apply Derivation.ext
      intro a
      rw [Theory.AlgebraicGroup.identityTangentRepresentation_action_apply,
        Theory.AlgebraicGroup.identityTangentConjugationLinearMap_apply]
    calc
      Bor1.identityTangentConjugationLinearMap G g D =
          Theory.AlgebraicGroup.identityTangentConjugationLinearMap G g D :=
        LinearMap.congr_fun
          (Bor1.identityTangentConjugationLinearMap_eq_root G g) D
      _ = (((Theory.AlgebraicGroup.identityTangentRepresentation G).action g).1 D) :=
        haction.symm
      _ = D := hc2.symm

end Theory.AlgebraicGroup.Bor1
