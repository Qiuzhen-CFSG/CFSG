module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair.Geometry.Stabilizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair.Theta
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.Complete

/-!
# The Cartan geometry for the literal point-radical action

The block calculations produce a Cartan subgroup normalizing R₁. The source
fixed-line identity then supplies its scalar marking, while relative Frattini
and Hall conjugacy supply the stabilizer factorization. Together they discharge
the entire `CartanGeometry` premise of the Cartan–TI pair assembly.

The final theorem also uses the proved theta identity from the genuine 11.0.4
residual and cubic-containment clauses. Fixed-center centralizer control and
the exceptional order-21 exclusion remain obligations of
qt-d-1222-natural-point-fixed-summand. The fixed-line and 11.0.4 inputs retain
their preceding source owners, qt-d-1222-natural-flag-cartan and
qt-d-1222-natural-preliminary-source; qt-d-1222-natural-normalizer-source owns
their final discharge. These conditional consumers do not assert source 11.1.5.
Source: Aschbacher–Smith, 11.1.5, printed p.766.
-/

open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The GO normality clause on the original quotient, with its factorization
proved from the fixed-line and center identities. -/
theorem normal_in_stabilizer_of_fixed_line
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) {X : Subgroup G}
    (hX : IsCartan T L X) (hXY : X ≤ normalizer (f.Ri 0 : Set G))
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥) :
    ∀ a : Actor (f.Ri 0),
      (fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)).map
        (representation (f.Ri 0) a) =
        fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) →
      (cartanImage (f.Ri 0) X).map (MulAut.conj a).toMonoidHom =
        cartanImage (f.Ri 0) X := by
  obtain ⟨m⟩ := scalarDecomposition_of_fixed_line f S.nonbinary hX hXY hfixed hcenter
  exact chosen_normal_in_stabilizer D S f hne (m.fixedSpace_eq S.nonbinary)
    (stabilizer_cover_of_fixed_line f hX hXY hfixed hcenter)

/-- The actual GO input, retaining only theta and centralizer control beyond
the source fixed-line and center identities. -/
theorem input_of_fixed_line_geometry
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) {X : Subgroup G}
    (hX : IsCartan T L X) (hXY : X ≤ normalizer (f.Ri 0 : Set G))
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hθ : theta (sourceOrders L S.field.degree) (normalizer (L : Set G)) = L)
    (hcontrol : ∀ U : Subgroup G, U ≤ radicalFixedCenter (f.Ri 0) L → U ≠ ⊥ →
      centralizer (U : Set G) ≤ normalizer (L : Set G))
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥) :
    Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) :=
  input_of_fixed_line D S f hX hXY hfixed hcenter hθ hcontrol
    (stabilizer_cover_of_fixed_line f hX hXY hfixed hcenter) hne

/-- The scalar-marking and stabilizer-factorization construction on the original
chosen flag; both clauses hold for the Cartan supplied by the block geometry. -/
theorem cartanGeometry_of_fixed_line
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G)) :
    CartanGeometry D S f := by
  intro _ _ hb hc
  obtain ⟨X, hX, hXY, _, _⟩ := PointCohomology.exists_point_geometry D S f hb
  exact ⟨X, hX, hXY, scalarDecomposition_of_fixed_line f S.nonbinary hX hXY hfixed hc,
    stabilizer_cover_of_fixed_line f hX hXY hfixed hc⟩

/-- Application to the original pair contract, discharging `CartanGeometry`
and theta from the fixed line and the preceding genuine 11.0.4 clauses. -/
theorem pairConstruction_of_fixed_line_and_source_residuals
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hcontrol : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      V = Source.conjugateSpan (normalizer (L : Set G)) V →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      ∀ U : Subgroup G, U ≤ radicalFixedCenter (f.Ri 0) L → U ≠ ⊥ →
      centralizer (U : Set G) ≤ normalizer (L : Set G))
    : PairConstruction D S f :=
  pairConstruction_of_source_residuals D S f hres hcubic hcontrol
    (cartanGeometry_of_fixed_line D S f hfixed)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
