module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair.Geometry.LineCharacter
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair.Geometry.Splitting

/-!
# The scalar marking in the point-radical GO input

The original Cartan acts through all field scalars on the marked quotient line.
Odd-order averaging and the corrected center identity extend this to coordinates
on the actual radical omega center, retaining its literal fixed subspace.
This constructs the scalar-marking input of the existing Cartan–TI assembly.

The fixed-line identity is preceding flag geometry owned by
qt-d-1222-natural-flag-cartan. The center and radical-normalization inputs
are supplied by qt-d-1222-natural-point-cohomology. Centralizer control,
stabilizer factorization and the exceptional block actions remain local
obligations of qt-d-1222-natural-point-fixed-summand; final assembly of the
earlier source inputs belongs to qt-d-1222-natural-normalizer-source.
Source: Aschbacher–Smith, 11.1.5, printed p.766.
-/

open Subgroup Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField} {c : Coordinates D F}

/-- Scalar coordinates on the literal omega center, with its original fixed
subspace as second factor, including a nontrivial central kernel in V₁. -/
theorem scalarDecomposition_of_fixed_line (f : InvariantFlag c)
    (hF : 1 < F.degree) {X : Subgroup G} (hX : IsCartan T L X)
    (hXY : X ≤ normalizer (f.Ri 0 : Set G))
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L) :
    Nonempty (ScalarDecomposition (f.Ri 0) L X F) :=
  scalarDecomposition_of_line_character f hF hX hXY
    (hX.1.trans (cartanNormalizer_normalizes_line f hfixed)) hcenter
    (cartanLineCharacter f hX hfixed) (cartanLineCharacter_surjective f hX hfixed)
    (cartanLineCharacter_apply f hX hfixed)

/-- Application to the original GO input: the scalar marking is now
constructed from the source fixed-line and center identities. The remaining
theta, centralizer-control and stabilizer-factorization premises retain their
source obligations with the fixed-summand assembly owner. -/
theorem input_of_fixed_line
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) {X : Subgroup G}
    (hX : IsCartan T L X) (hXY : X ≤ normalizer (f.Ri 0 : Set G))
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hθ : theta (sourceOrders L S.field.degree) (normalizer (L : Set G)) = L)
    (hcontrol : ∀ U : Subgroup G, U ≤ radicalFixedCenter (f.Ri 0) L → U ≠ ⊥ →
      centralizer (U : Set G) ≤ normalizer (L : Set G))
    (hcover : (normalizer (L : Set G)).subgroupOf (normalizer (f.Ri 0 : Set G)) ≤
      kernel (f.Ri 0) ⊔ normalizer (X.subgroupOf (normalizer (f.Ri 0 : Set G)) : Set _))
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥) :
    Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) := by
  obtain ⟨m⟩ := scalarDecomposition_of_fixed_line f S.nonbinary hX hXY hfixed hcenter
  exact input_of_scalar_decomposition D S f hX hXY m hθ hcontrol hcover hne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
