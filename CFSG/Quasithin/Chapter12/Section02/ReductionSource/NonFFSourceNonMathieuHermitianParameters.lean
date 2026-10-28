module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceParameters

/-!
# Hermitian offender parameters for the original chosen orbit

The component marking constructs the embedding of the actual full automizer.
The source orbit itself supplies E.3.22, and coordinate transport supplies
both the dimension and two-rank bounds. Thus the rank-saturation theorem
applies to the original offender and its literal ambient intersection.

The remaining premises are the preceding source weak-closure bounds, the
canonical offender kernel and H.4.4(3). Their construction, the n > 1
exclusion and the field-four endgame remain with
qt-d-1222-nonmathieu-hermitian-exclusion.

Source: Aschbacher–Smith 8.2.2(7), 8.2.3 and 8.2.4, printed pp.714–716.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (n : ℕ) [NeZero n]
  (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
    (overgroupAction n (binaryImage n)))

include d in
/-- The source dimension and rank inputs are discharged on the exact chosen
orbit; the canonical offender is the original conjugate subgroup in G. -/
theorem sourceOrbit_hermitian_offender_parameters
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hgeometry : ∀ A : Subgroup (binaryNormalizer n), IsElementaryTwo A →
      3 * n ≤ rank A → 5 * n ≤ fixedCodim (overgroupAction n (binaryNormalizer n)) A)
    (g : G) (hOff : IsWOffenderAt D.sourceOrbit T g)
    (hw : globalW D.sourceOrbit T = n) (hr : ((4 * n : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit)
    (hkernel : offenderNormalizer D.sourceOrbit g ⊓ centralizer (D.sourceOrbit : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom) :
    rank (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)) = 4 * n ∧
      rank (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)) = 4 * n ∧
      D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
        D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ∧
      globalR D.sourceOrbit ≤ ((5 * n : ℕ) : ℕ∞) := by
  obtain ⟨j, hj, he, _⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  exact Chapter8.Section02.HermitianSource.offender_parameters_of_coordinates
    D.sourceOrbit T n (D.hermitianOrbitCoordinates n d) j hj he hgeometry g
    D.sourceOrbit_weakClosure_setup hOff hw hr hkernel

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
