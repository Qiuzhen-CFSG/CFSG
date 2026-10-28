module
public import CFSG.Quasithin.Chapter7.Section01To05.WeakClosure
public import CFSG.Quasithin.Chapter7.Section06To07.Terminal

/-!
# Terminal inputs for the non-FF doubled rows

These predicates specify the numerical and geometric obligations on the
actual orbit, and the following lemmas apply the proved weak-closure and
relative Baer--Suzuki contradictions. They assert no model classification
and do not construct the bounds. NonFFSourceDoubled gives their actual
chosen-module consumer, retaining each source obligation explicitly.

Source: Aschbacher--Smith 7.3.5, 7.5.2(2), 7.5.5 and 7.6.1,
printed pp.699--703. The binary geometry also requires 7.7, pp.703--709.
-/


@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open Subgroup Representation.BinaryOffender ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] (W : Subgroup G)
  [IsElementaryAbelian 2 W] (T : Sylow 2 G)

/-- The numerical inputs of 7.5.2(2), on the actual whole orbit. -/
def DoubledLinearBounds (n : ℕ) : Prop :=
  primeRank 2 (Automizer W) ≤ 2 * n ∧ globalW W T ≤ n ∧
    ((4 * n : ℕ) : ℕ∞) ≤ globalR W

/-- The strict H.7 bound is required also for the derived binary row A₆. -/
def DoubledSymplecticBounds (n : ℕ) : Prop :=
  (localM W : ℕ∞) ≤ globalR W ∧ 3 * n ≤ localM W ∧
    localA W < ((2 * n : ℕ) : ℕ∞) ∧ globalW W T ≤ n

/-- A₇ requires the improved 7.5.5 bound r ≥ 6, not only the table's r ≥ 4. -/
def DoubledSevenBounds : Prop :=
  primeRank 2 (Automizer W) ≤ 3 ∧ globalW W T ≤ 2 ∧ 6 ≤ globalR W

/-- The literal centralizer-core geometry needed at the end of 7.6.1.
This defines an obligation; it does not assert the source construction. -/
def DoubledBinaryGeometry : Prop :=
  ∃ Z A : Subgroup G,
    W ≤ centralizer (Z : Set G) ∧ A ≤ W ∧
    A ≤ (centralizer (Z : Set G)).pCoreIn 2 ∧ A.relIndex W = 2 ∧
    ¬ W ≤ (centralizer (Z : Set G)).pCoreIn 2 ∧
    ∀ g ∈ centralizer (Z : Set G),
      ((centralizer (Z : Set G)).pCoreIn 2).relIndex
        (W.map (MulAut.conj g).toMonoidHom) = 2 →
      ¬ W.map (MulAut.conj g).toMonoidHom ≤ centralizer (W : Set G) →
      IsPGroup 2 (W ⊔ W.map (MulAut.conj g).toMonoidHom : Subgroup G)

theorem DoubledLinearBounds.false {n : ℕ} (h : DoubledLinearBounds W T n)
    (hT : HypothesisE322 W T) (hFF : ¬ IsFFModule (automizerRepresentation W))
    (hn : 0 < n) : False :=
  natural_dual_parameter_contradiction hT hFF hn h.1 h.2.1 h.2.2

theorem DoubledSymplecticBounds.false {n : ℕ} (h : DoubledSymplecticBounds W T n)
    (hT : HypothesisE322 W T) : False :=
  symplectic_parameter_contradiction hT h.1 h.2.1 h.2.2.1 h.2.2.2

theorem DoubledSevenBounds.false (h : DoubledSevenBounds W T)
    (hT : HypothesisE322 W T) (hFF : ¬ IsFFModule (automizerRepresentation W)) : False :=
  impossible_parameter_bounds hT hFF h.1 h.2.1 h.2.2 (by decide)

theorem DoubledBinaryGeometry.false (h : DoubledBinaryGeometry W) : False := by
  obtain ⟨Z,A,hWZ,hAW,hAc,hindex,hWc,hpair⟩ := h
  exact Section06To07.false_of_hyperplane_pair_generation Z W A
    (IsElementaryAbelian.isPGroup 2 W) hWZ hAW hAc hindex hWc hpair

end CFSG.Quasithin.Chapter7.NormalizedSource
