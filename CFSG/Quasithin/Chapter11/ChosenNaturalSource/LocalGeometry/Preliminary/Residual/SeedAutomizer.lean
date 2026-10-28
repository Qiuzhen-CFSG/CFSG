module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.CubicSeed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.FixedComplete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootGeometry.Source

/-!
# Natural seed automizers and their parameter consumers

An order-three element of the original automizer lifts to an order-three
element of N_G(V), because its action kernel has order prime to three.
The checked seed stabilizer theorem therefore places the lift in L. This
discharges the cubic premise used in the odd-prime fixed-codimension
calculation on V, including the even-degree SL₃ row.

The resulting fixed-codimension and root-geometry families use the original
D,S, quotient marking and full seed automizer. They feed the actual
centralizer/residual and global-parameter consumers of 11.2.2 below.
The global lower bound and third-space centralizer premise retain their
independent weak-closure and flag/component producers; their final discharge
belongs to qt-d-1222-natural-weak-closure-source.

Unrestricted cubic containment in N_G(L), required by the original 11.0.4
contract, remains open with qt-d-1222-natural-preliminary-source. A lift
through the seed automizer supplies seed normalization only for that lift.
The final chosen-natural assembly remains with
qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith A.3.19, printed pp.54--55; 11.0.4, p.760;
and 11.2.2, pp.767--768, combined manuscript of 1 March 2004.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

namespace FullAutomizer

/-- Every cubic in the literal seed automizer belongs to the original component image.
The same-order lift lies in N_G(V), so CubicSeed discharges its containment. -/
theorem sl3_cubic_mem_layer
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hn : Even S.field.degree)
    {a : Automizer V} (ha : orderOf a = 3) : a ∈ inducedAutomizer V L := by
  let f := V.normalizerMonoidHom.rangeRestrict
  obtain ⟨x,hx,hxp⟩ := exists_prime_exponent_lift f
    V.normalizerMonoidHom.rangeRestrict_surjective
    (sl3_even_action_kernel_coprime D S m hn) a (ha ▸ pow_orderOf_eq_one a)
  have hx1 : x ≠ 1 := by
    intro he
    have ha1 : a = 1 := hx.symm.trans (he ▸ f.map_one)
    simp only [ha1,orderOf_one] at ha
    omega
  have ho : orderOf x = 3 := orderOf_eq_prime hxp hx1
  have hxL : (x : G) ∈ L := Preliminary.sl3_orderThree_mem_of_normalizes_seed D S m hn
    (seed_normalizer_le D S x.property) x.property ((Subgroup.orderOf_coe x).trans ho)
  exact ⟨x,hxL,hx⟩

/-- The odd-prime fixed-codimension bound for the entire original SL₃ seed automizer,
in every field degree and without a global cubic-containment premise. -/
theorem sl3_odd_prime_lower
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) :
    letI := D.elementary
    ∀ p : ℕ, p.Prime → Odd p → ∀ a : Automizer V, orderOf a = p →
      2 * S.field.degree ≤ fixedCodim (automizerRepresentation V) (zpowers a) := by
  let := D.elementary
  intro p hp ho a ha
  rcases Nat.even_or_odd S.field.degree with hn | hn
  · by_cases hp3 : p = 3
    · rw [hp3] at ha
      exact sl3_inner_odd_prime_lower D S m 3 (by decide) (by decide) a ha
        (sl3_cubic_mem_layer D S m hn ha)
    · have htwo := hp.two_le
      have hp2 : p ≠ 2 := by intro he; rw [he] at ho; norm_num at ho
      exact sl3_odd_prime_lower_of_gt_three D S m p hp (by omega) a ha
  · exact sl3_odd_prime_lower_of_odd_degree D S m hn p hp ho a ha

end FullAutomizer

/-- All four fixed-codimension clauses for each original natural marking. -/
theorem natural_fixedCodimensions (c : Coordinates D S.field) : FixedCodimensions D S c := by
  cases c with
  | sl3 m =>
    exact fixedCodimensions_of_odd D S (Coordinates.sl3 m)
      (FullAutomizer.sl3_odd_prime_lower D S m)
  | sp4 m => exact sp4_fixedCodimensions D S m
  | g2 m => exact g2_fixedCodimensions D S m

/-- The actual minimal fixed-space and A₂-actor assertions on the original flag.
The preceding TI conclusion is discharged by the checked preliminary source. -/
theorem natural_rootGeometry {c : Coordinates D S.field} (f : InvariantFlag c) :
    RootGeometry D S f :=
  rootGeometry_of_fixedCodimensions D S f (natural_fixedCodimensions D S c)
    (Preliminary.seed_ti D S)

/-- The 11.2.2 centralizer and prime-to-two residual consumer, with its local model
and E.6.1 premises discharged. The independent global lower bound remains explicit. -/
theorem natural_centralizer_control {c : Coordinates D S.field}
    (hr : (naturalParameter D S c : ℕ∞) ≤ globalR V)
    {U : Subgroup G} (hUV : U ≤ V) (hk : subgroupCorank V U < 2 * naturalParameter D S c)
    (hres : Section06.oddCentralizerCondition (normalizer (L : Set G)) V U) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
      (primeToResidual 2 ↥(centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype ≤
          normalizer (L : Set G) ⊓ centralizer (V : Set G) :=
  centralizer_control D S (natural_fixedCodimensions D S c)
    (hypothesisE61_of_ti D S (Preliminary.seed_ti D S)) hr hUV hk hres

/-- The global-parameter consumer with all fixed-codimension, root-geometry and TI
premises discharged. The independent lower bound and third-space control remain explicit. -/
theorem natural_global_parameters {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hr : (naturalParameter D S c : ℕ∞) ≤ globalR V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    ((naturalParameter D S c : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S c ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S c :=
  global_parameters D S f (natural_fixedCodimensions D S c) (natural_rootGeometry D S f)
    (hypothesisE61_of_ti D S (Preliminary.seed_ti D S)) hr hthree

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
