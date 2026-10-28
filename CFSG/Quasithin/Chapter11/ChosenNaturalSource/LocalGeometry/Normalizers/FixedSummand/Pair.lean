module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair.TI
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair.Quotient
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair.Scalars

/-!
# Assembly of the actual Cartan--TI pair

The scalar marking proves cyclicity, odd order, regularity and the exact
fixed-space identity for the source quotient. Uniqueness over L and the
source order-generated equality theta(M)=L supply TI. The original
stabilizer equality and a local factorization modulo C_Y(Z1) give normality.
These are combined into the existing PairConstruction interface.

The concrete Cartan/scalar marking, theta equality and fixed-center
centralizer control remain explicit source obligations. Uniqueness over L
suffices for the last one, but the weaker control statement is all that the
assembly consumes. This conditional assembly does not assert that
PairConstruction, or source 11.1.5, has been completed. The preceding flag
and 11.0.4 inputs retain their existing source owners; the fixed-summand
pair task retains final discharge of these three new construction targets.
Source: Aschbacher--Smith, 11.1.5, printed p.766.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Geometric construction target on the literal source objects. Its data
are a splitting and scalar homomorphism, not a GO pair or its TI conclusion.
The factorization is inside the original Y, modulo its original kernel. -/
def CartanGeometry (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) : Prop :=
  (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
  V = Source.conjugateSpan (normalizer (L : Set G)) V →
  (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
  radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
  ∃ X : Subgroup G, IsCartan T L X ∧ X ≤ normalizer (f.Ri 0 : Set G) ∧
    Nonempty (ScalarDecomposition (f.Ri 0) L X S.field) ∧
    (normalizer (L : Set G)).subgroupOf (normalizer (f.Ri 0 : Set G)) ≤
      kernel (f.Ri 0) ⊔ normalizer (X.subgroupOf (normalizer (f.Ri 0 : Set G)) : Set _)

/-- All GO clauses for the original quotient, from concrete scalar data,
order generation, fixed-center centralizer control and the local factorization. -/
theorem input_of_scalar_decomposition
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) {X : Subgroup G}
    (hX : IsCartan T L X) (hXY : X ≤ normalizer (f.Ri 0 : Set G))
    (m : ScalarDecomposition (f.Ri 0) L X S.field)
    (hθ : theta (sourceOrders L S.field.degree) (normalizer (L : Set G)) = L)
    (hcontrol : ∀ U : Subgroup G, U ≤ radicalFixedCenter (f.Ri 0) L → U ≠ ⊥ →
      centralizer (U : Set G) ≤ normalizer (L : Set G))
    (hcover : (normalizer (L : Set G)).subgroupOf (normalizer (f.Ri 0 : Set G)) ≤
      kernel (f.Ri 0) ⊔ normalizer (X.subgroupOf (normalizer (f.Ri 0 : Set G)) : Set _))
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥) :
    Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) := by
  have hf := m.fixedSpace_eq S.nonbinary
  exact
    { faithful := representation_injective _
      nontrivial := m.nontrivial S.nonbinary
      cyclic := m.cyclic
      odd := cartanImage_odd hX hXY
      transitive := m.transitive
      fixed_nontrivial := hf.symm ▸ fixedSubspace_ne_bot hne
      ti := fixedOrbit_ti hθ hcontrol hf
      normal_in_stabilizer := chosen_normal_in_stabilizer D S f hne hf hcover }

/-- Consumer for the exact published PairConstruction contract. Final
assembly must construct the three displayed premises independently. -/
theorem pairConstruction_of_geometry
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hθ : (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      theta (sourceOrders L S.field.degree) (normalizer (L : Set G)) = L)
    (hcontrol : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      V = Source.conjugateSpan (normalizer (L : Set G)) V →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      ∀ U : Subgroup G, U ≤ radicalFixedCenter (f.Ri 0) L → U ≠ ⊥ →
      centralizer (U : Set G) ≤ normalizer (L : Set G))
    (hgeometry : CartanGeometry D S f) : PairConstruction D S f := by
  intro he hspan hb hcenter hne
  obtain ⟨X, hX, hXY, ⟨m⟩, hcover⟩ := hgeometry he hspan hb hcenter
  exact ⟨X, hX, hXY, input_of_scalar_decomposition D S f hX hXY m (hθ hb) (hcontrol he hspan hb hcenter) hcover hne,
    m.fixedSpace_eq S.nonbinary⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
