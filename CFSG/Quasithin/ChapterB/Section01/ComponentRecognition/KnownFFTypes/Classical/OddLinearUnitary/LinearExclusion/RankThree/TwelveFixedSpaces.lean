module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.SourceBounds
public import Theory.Representation.BinaryOddDisplacement.Thirteen

/-!
# Local calculations for the degree-twelve PSL₃(3) fixed-space bounds

An outer involution inverting an element of order thirteen fixes at most six
binary dimensions. If an actor element has an order-three commutator inside
that involution's centralizer, its common fixed space has dimension at most
five. These arguments use the original representation and ambient elements.

The inner four-group calculation and the group witnesses, including the
reselection of an outer involution for a normal eight-group, remain explicit
premises here. They are independent of identifying the representation degree.
This conditional assembly has precisely the fixed-space output consumed by
`RankThree.source_exclusion_of_calculations`; it does not assert that those
remaining local calculations have been established.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript pp.9--10, PSL₃(3) case.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.TwelveFixedSpaces
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

omit [Finite G] in
/-- The actual source fixed-space contract from its inner calculation and
outer group witnesses. The latter include the normal eight-group case. -/
theorem source_bounds_of_local_calculations
    (hd : Module.finrank (ZMod 2) V = 12)
    (hinner : ∀ A : Subgroup G, IsElementaryTwo A → A ≤ generalizedFitting G →
      rank A = 2 → Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 6)
    (houter : ∀ A : Subgroup G, IsElementaryTwo A → ¬ A ≤ generalizedFitting G →
      rank A = 2 → ∃ t ∈ A, ∃ x : G, orderOf x = 13 ∧ t * x * t⁻¹ = x⁻¹)
    (hthree : ∀ A : Subgroup G, IsElementaryTwo A → rank A = 3 →
      ∃ t ∈ A, orderOf t = 2 ∧ ∃ x a c : G, a ∈ A ∧ orderOf x = 13 ∧
        t * x * t⁻¹ = x⁻¹ ∧ Commute t a ∧ Commute t c ∧
          orderOf (a * c * a⁻¹ * c⁻¹) = 3)
    (A : Subgroup G) (hA : IsElementaryTwo A) :
    (rank A = 2 → Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 6) ∧
    (rank A = 3 → Module.finrank (ZMod 2) (fixedSpace ρ A) ≤ 5) := by
  constructor
  · intro hr
    by_cases hi : A ≤ generalizedFitting G
    · exact hinner A hA hi hr
    obtain ⟨t, ht, x, hx, hinv⟩ := houter A hA hi hr
    have hle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
      intro v hv b
      exact hv ⟨b, (zpowers_le.mpr ht) b.property⟩
    exact (Submodule.finrank_mono hle).trans
      (finrank_fixedSpace_le_six_of_inverts_thirteen ρ h.faithful hd t x hx hinv)
  · intro hr
    obtain ⟨t, htA, ht, x, a, c, haA, hx, hinv, hta, htc, hcomm⟩ := hthree A hA hr
    exact finrank_fixedSpace_le_five_of_thirteen_three_witness ρ h.faithful hd
      A t x a c htA haA ht hx hinv hta htc hcomm

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.TwelveFixedSpaces
