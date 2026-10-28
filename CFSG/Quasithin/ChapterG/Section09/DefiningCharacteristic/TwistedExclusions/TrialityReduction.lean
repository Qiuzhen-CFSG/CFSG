module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.WeakEndpoint
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.RankApplication
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage
public import Theory.SpecificGroups.Triality.BinarySevenPlane

/-!
# Reducing the source triality exclusion to the field of order four

For the actual G.9 component and its original binary action, the constructed
seven-plane subgroup and the weak automorphism-rank bound exclude the field
of order two. The primitive-prime degree bound and the proved intrinsic rank
exclude every exponent at least three. In both ranges, inner–coefficient
coverage uses simplicity and perfectness inherited from the same component.
Thus a triality witness in the source setup forces exponent two. There are no
additional model, rank, degree or coverage premises in these reductions.

The exponent-two case still requires its separate sharp automorphism-rank
argument; the general stronger 24*n representation bound is not used here.
Source: Aschbacher–Smith, G.9.3, printed p.356 (`refs/quasithin.pdf`).
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
open Triality.Standard Triality.Standard.OuterOdd.Coverage

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : CFSG.Quasithin.GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}

/-- The original component cannot be the triality group over the field of order two. -/
theorem not_triality_two_of_source_component
    (h : ComponentHypothesis K ρ A L L m)
    (model : IsTrialityGroupAt 2 L) : False := by
  apply not_triality_two_of_weak_rank_and_coverage binarySevenPlane h model
  intro hsimple hperfect
  exact @binary_inner_coefficient 1 Nat.zero_lt_one hsimple hperfect

/-- The original component cannot be binary triality of exponent at least three. -/
theorem not_triality_ge_three_of_source_component
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 3 ≤ n)
    (model : IsTrialityGroupAt (2 ^ n) L) : False := by
  apply not_triality_of_coefficient_coverage h hn model
  intro hsimple hperfect
  exact @binary_inner_coefficient n (by omega) hsimple hperfect

/-- Every binary triality witness for the source component has exponent two. -/
theorem triality_parameter_eq_two_of_source_component
    (h : ComponentHypothesis K ρ A L L m) {n : ℕ} (hn : 0 < n)
    (model : IsTrialityGroupAt (2 ^ n) L) : n = 2 := by
  by_contra hne
  by_cases he : n = 1
  · subst n
    exact not_triality_two_of_source_component h (by simpa using model)
  · exact not_triality_ge_three_of_source_component h (by omega) model


end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
