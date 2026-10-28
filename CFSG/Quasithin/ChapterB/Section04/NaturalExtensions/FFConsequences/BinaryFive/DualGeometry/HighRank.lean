module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Contracts
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Bounds
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.QuadraticFiveAxis

/-!
# The high-rank common-axis step in B.4.9

Apply quadratic displacement to the original five-dimensional quotient of a
double-natural extension. Faithfulness and dimension come from its natural
marking, and quadraticity descends from the original module. The resulting
four-group lies in the given actor, so it remains quadratic upstairs. This
constructs the common-axis input for splitting with either quotient orientation.

Source: Aschbacher–Smith, B.4.9(2)(i), printed p.95, combined manuscript
of 1 March 2004, the rank-five and rank-six cases. The final rank-case and
splitting assembly belong to the source consumer.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {F : BinaryField} {ρ : Representation (ZMod 2) G V}

/-- A high-rank quadratic actor contains an axis four-group on the literal
quotient, still quadratic on the original extension. No orientation is needed. -/
theorem high_rank_quadratic_axis (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    {B : Subgroup G} (hB : IsElementaryTwo B) (hr : 5 ≤ rank B)
    (hq : IsQuadratic ρ B) :
    ∃ E : Subgroup G, E ≤ B ∧ QuadraticSplitting.IsAxisFour d E ∧ IsQuadratic ρ E := by
  let : Finite G := Finite.of_injective (groupEquiv d hF) (groupEquiv d hF).injective
  have hdim : Module.finrank (ZMod 2) (V ⧸ d.space.toSubmodule) = 5 := by
    rw [d.quotient_finrank, (coordinates d hF).linearEquiv.finrank_eq]
    change Module.finrank (ZMod 2) (BinaryLinear.OuterCyclic.Space 5) = 5
    simp [BinaryLinear.OuterCyclic.Space]
  have hq' : IsQuadratic d.space.quotientRepresentation B :=
    quadratic_of_equivariant_surjection ρ d.space.quotientRepresentation
      d.space.toSubmodule.mkQ d.space.toSubmodule.mkQ_surjective (fun _ _ => rfl) B hq
  obtain ⟨E, hEB, he, hc, I, hI, hfix⟩ :=
    QuadraticFiveAxis.high_rank_axis d.space.quotientRepresentation
      d.quotient_faithful hdim B hB hr hq'
  exact ⟨E, hEB, ⟨he, hc, I, hI.trans hF.symm, hfix⟩,
    fun a ha b hb v => hq a (hEB ha) b (hEB hb) v⟩

/-- The high-rank branch supplies the exact axis witness consumed by splitting. -/
theorem hasQuadraticAxisFour_of_high_rank (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)
    {B : Subgroup G} (hB : IsElementaryTwo B) (hr : 5 ≤ rank B)
    (hq : IsQuadratic ρ B) : HasQuadraticAxisFour d := by
  obtain ⟨E, _, he, hqE⟩ := high_rank_quadratic_axis d hF hB hr hq
  exact ⟨E, he, hqE⟩

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
