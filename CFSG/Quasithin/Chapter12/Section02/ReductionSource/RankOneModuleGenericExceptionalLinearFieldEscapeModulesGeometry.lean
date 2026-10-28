module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscape
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesGeometry

/-!
# The original centralizer span before the cubic obstruction

The literal local data and condition (E) give G.2.1 with H₁=C_G(z).
The resulting G.2.2 conclusions apply to precisely ⟨V₂^C_G(z)⟩.
In the nonabelian branch its commutator with V₂ is exactly ⟨z⟩,
discharging the first reduction in 5.1.23. No abelian conclusion or
cubic-ratio estimate is assumed or asserted.

Source: Aschbacher--Smith, 5.1.21,23, printed pp.644--645.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H C : Subgroup G} {z : G}

/-- All original G.2.1 hypotheses on the full involution centralizer. -/
theorem linear_cubic_centralizer_setup
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : CubicEscape.LocalData T H C z) :
    (CubicEscape.setup T (centralizer ({z} : Set G)) C z).Hypothesis :=
  CubicEscape.centralizer_hypothesis d.g2 (h.simpleQTKE.evenCharacteristic T)
    (by simpa only [Nat.card_zpowers] using d.point_card)

/-- The centralizer-span reductions of 5.1.21, before 5.1.23. -/
theorem linear_cubic_centralizer_span_reductions
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : CubicEscape.LocalData T H C z) :
    let U := conjugateSpanBy (CubicEscape.plane C z) (centralizer ({z} : Set G))
    U ≤ (centralizer ({z} : Set G)).pCoreIn 2 ∧
      U ≤ (T : Subgroup G) ∧
      (frattini U).map U.subtype ≤ zpowers z ∧ ⁅U, U⁆ ≤ zpowers z :=
  CubicEscape.centralizer_span_reductions d.g2 (h.simpleQTKE.evenCharacteristic T)
    (by simpa only [Nat.card_zpowers] using d.point_card)

/-- The exact commutator in the nonabelian branch of 5.1.23. -/
theorem linear_cubic_nonabelian_plane_commutator
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : CubicEscape.LocalData T H C z)
    (hnon : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) :
    ⁅CubicEscape.plane C z,
      conjugateSpanBy (CubicEscape.plane C z) (centralizer ({z} : Set G))⁆ = zpowers z :=
  CubicEscape.nonabelian_plane_commutator d.g2 (h.simpleQTKE.evenCharacteristic T)
    (by simpa only [Nat.card_zpowers] using d.point_card) hnon

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
