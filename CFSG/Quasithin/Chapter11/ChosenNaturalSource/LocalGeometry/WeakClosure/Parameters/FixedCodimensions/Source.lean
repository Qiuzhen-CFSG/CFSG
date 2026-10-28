module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.Involutions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.Attainment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.SymplecticOdd
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.LinearOdd
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.LinearCubic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.G2Full

/-!
# The exact natural local parameter

The full-automizer lower bound and the explicit inner attaining involution
compute the genuine E.3 minimum on the original V. In particular the value
is n in the SL₃ and Sp₄ rows and 2n in the G₂ row, including nonsplit central
attachments. There is no numerical or splitting premise in this theorem.

The odd-prime calculations complete all four FixedCodimensions clauses
for Sp₄, G₂ and for SL₃ of odd degree, and feed the actual residual consumers
below. For even-degree SL₃, only the exact earlier 11.0.4 cubic containment remains
explicit, with its preliminary-source owner. Hyperplane centralizer control and minimal fixed-space recognition
remain with the owning natural-parameter task. The parent
weak-closure task assembles the source clauses after those inputs are discharged.

Source: Aschbacher--Smith, 11.2.2(1--2), printed pp.767--768.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Source 11.2.2(1), on the literal full automizer of the original chosen module. -/
theorem localM_eq_naturalParameter (c : Coordinates D S.field) :
    @localM G _ V D.elementary = naturalParameter D S c :=
  FullAutomizer.localM_of_attainment D S (c := c) (FullAutomizer.involution_attains D S c)

/-- Only the odd-prime bound remains in the fixed-codimension specification. -/
theorem fixedCodimensions_of_odd (c : Coordinates D S.field)
    (hodd : letI := D.elementary; ∀ p : ℕ, p.Prime → Odd p → ∀ a : Automizer V,
      orderOf a = p → 2 * naturalParameter D S c ≤
        fixedCodim (automizerRepresentation V) (zpowers a)) : FixedCodimensions D S c :=
  FullAutomizer.fixedCodimensions_of_attainment_and_odd D S (c := c)
    (FullAutomizer.involution_attains D S c) hodd

/-- Actual residual application, with the owned odd-prime and global lower-bound
calculations still explicit. Both residuals retain the source O^{2′} convention. -/
theorem centralizer_control_of_odd {c : Coordinates D S.field}
    (hodd : letI := D.elementary; ∀ p : ℕ, p.Prime → Odd p → ∀ a : Automizer V,
      orderOf a = p → 2 * naturalParameter D S c ≤
        fixedCodim (automizerRepresentation V) (zpowers a))
    (hE : Section06.HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hr : (naturalParameter D S c : ℕ∞) ≤ globalR V)
    {U : Subgroup G} (hUV : U ≤ V)
    (hk : subgroupCorank V U < 2 * naturalParameter D S c)
    (hres : Section06.oddCentralizerCondition (normalizer (L : Set G)) V U) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      (primeToResidual 2 ↥(centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype ≤
          normalizer (L : Set G) ⊓ centralizer (V : Set G) :=
  centralizer_control D S (fixedCodimensions_of_odd D S c hodd) hE hr hUV hk hres

/-- All four fixed-codimension clauses are now proved for the full original
Sp₄ automizer. No numerical or splitting premise remains. -/
theorem sp4_fixedCodimensions
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    FixedCodimensions D S (Coordinates.sp4 m) :=
  fixedCodimensions_of_odd D S (Coordinates.sp4 m) (FullAutomizer.sp4_odd_prime_lower D S m)

/-- Source 11.2.2(2) in the symplectic row, with the model calculation
discharged. The hyperplane argument still supplies the independent r-bound;
the parent source assembly supplies E.6.1 from the preceding TI conclusion. -/
theorem sp4_centralizer_control
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hE : Section06.HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hr : (S.field.degree : ℕ∞) ≤ globalR V)
    {U : Subgroup G} (hUV : U ≤ V) (hk : subgroupCorank V U < 2 * S.field.degree)
    (hres : Section06.oddCentralizerCondition (normalizer (L : Set G)) V U) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      (primeToResidual 2 ↥(centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype ≤
          normalizer (L : Set G) ⊓ centralizer (V : Set G) :=
  centralizer_control D S (sp4_fixedCodimensions D S m) hE hr hUV hk hres

/-- The entire fixed-codimension family for SL₃ of odd coefficient degree. -/
theorem sl3_oddDegree_fixedCodimensions
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hn : Odd S.field.degree) : FixedCodimensions D S (Coordinates.sl3 m) :=
  fixedCodimensions_of_odd D S (Coordinates.sl3 m)
    (FullAutomizer.sl3_odd_prime_lower_of_odd_degree D S m hn)

/-- The literal residual application for SL₃ of odd degree, with its model
premise discharged. The owning parameter task supplies the independent r-bound. -/
theorem sl3_oddDegree_centralizer_control
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hn : Odd S.field.degree)
    (hE : Section06.HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hr : (S.field.degree : ℕ∞) ≤ globalR V)
    {U : Subgroup G} (hUV : U ≤ V) (hk : subgroupCorank V U < 2 * S.field.degree)
    (hres : Section06.oddCentralizerCondition (normalizer (L : Set G)) V U) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      (primeToResidual 2 ↥(centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype ≤
          normalizer (L : Set G) ⊓ centralizer (V : Set G) :=
  centralizer_control D S (sl3_oddDegree_fixedCodimensions D S m hn) hE hr hUV hk hres

/-- The full SL₃ fixed-codimension family, retaining only the exact earlier
order-three clause of 11.0.4. The preliminary-source owner constructs it;
the parent weak-closure source assembly discharges it. -/
theorem sl3_fixedCodimensions_of_cubic_source
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hthree : Even S.field.degree →
      ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    FixedCodimensions D S (Coordinates.sl3 m) :=
  fixedCodimensions_of_odd D S (Coordinates.sl3 m)
    (FullAutomizer.sl3_odd_prime_lower_of_cubic_source D S m hthree)

/-- Source 11.2.2(2) for every SL₃ degree, consuming the original normalizer's
cubic containment rather than an assumed full-automizer calculation. The owning
parameter task still supplies the independent global lower bound. -/
theorem sl3_centralizer_control_of_cubic_source
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hthree : Even S.field.degree →
      ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hE : Section06.HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hr : (S.field.degree : ℕ∞) ≤ globalR V)
    {U : Subgroup G} (hUV : U ≤ V) (hk : subgroupCorank V U < 2 * S.field.degree)
    (hres : Section06.oddCentralizerCondition (normalizer (L : Set G)) V U) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      (primeToResidual 2 ↥(centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype ≤
          normalizer (L : Set G) ⊓ centralizer (V : Set G) :=
  centralizer_control D S (sl3_fixedCodimensions_of_cubic_source D S m hthree)
    hE hr hUV hk hres

/-- All four fixed-codimension clauses hold on the full original G₂
natural automizer, retaining arbitrary central attachments. -/
theorem g2_fixedCodimensions
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) :
    FixedCodimensions D S (Coordinates.g2 m) := by
  apply fixedCodimensions_of_odd D S (Coordinates.g2 m)
  let := D.elementary
  intro p hp ho a ha
  simpa only [naturalParameter, ← Nat.mul_assoc] using
    FullAutomizer.g2_odd_prime_lower D S m p hp ho a ha

/-- The G₂ residual consumer, with its full-automizer calculation discharged.
The same parameter owner supplies the remaining global lower bound through
hyperplanes; the parent source assembly supplies E.6.1 from the earlier TI result. -/
theorem g2_centralizer_control
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (hE : Section06.HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hr : (2 * S.field.degree : ℕ∞) ≤ globalR V)
    {U : Subgroup G} (hUV : U ≤ V) (hk : subgroupCorank V U < 4 * S.field.degree)
    (hres : Section06.oddCentralizerCondition (normalizer (L : Set G)) V U) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      (primeToResidual 2 ↥(centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype ≤
          normalizer (L : Set G) ⊓ centralizer (V : Set G) := by
  apply centralizer_control D S (g2_fixedCodimensions D S m) hE _ hUV _ hres
  · simpa only [naturalParameter, Nat.cast_mul, Nat.cast_ofNat] using hr
  · simpa only [naturalParameter, ← Nat.mul_assoc] using hk

/-- The complete local calculation for every natural marking. Only the
exact earlier SL₃ cubic source clause is explicit, owned by
qt-d-1222-natural-preliminary-source and discharged by the parent source assembly. -/
theorem natural_fixedCodimensions_of_cubic_source (c : Coordinates D S.field)
    (hcubic : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    FixedCodimensions D S c := by
  cases c with
  | sl3 m => exact sl3_fixedCodimensions_of_cubic_source D S m (hcubic ⟨m⟩)
  | sp4 m => exact sp4_fixedCodimensions D S m
  | g2 m => exact g2_fixedCodimensions D S m

/-- The actual residual application in every natural marking. The remaining
r-bound is still a local obligation of this parameter task, not a new source
hypothesis; both residuals use the source O^{2′} convention. -/
theorem natural_centralizer_control_of_cubic_source {c : Coordinates D S.field}
    (hcubic : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hE : Section06.HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hr : (naturalParameter D S c : ℕ∞) ≤ globalR V)
    {U : Subgroup G} (hUV : U ≤ V) (hk : subgroupCorank V U < 2 * naturalParameter D S c)
    (hres : Section06.oddCentralizerCondition (normalizer (L : Set G)) V U) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      (primeToResidual 2 ↥(centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype ≤
          normalizer (L : Set G) ⊓ centralizer (V : Set G) :=
  centralizer_control D S (natural_fixedCodimensions_of_cubic_source D S c hcubic)
    hE hr hUV hk hres

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
