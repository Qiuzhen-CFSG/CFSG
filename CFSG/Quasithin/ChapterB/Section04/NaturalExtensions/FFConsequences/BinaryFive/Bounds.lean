module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Coordinates

/-!
# Actor ranks and interior-radical placement in B.4.9(2)(iv)

The proved GL₅(2) pair classification makes every elementary actor of rank
at least five quadratic on the natural module. Its displacement span has
dimension two or three, and the actor lies in the literal block radical
at that span. The radical's matrix coordinates bound its order by 64.
Transport through the original natural marking gives rank at most six
without any splitting assumption on the extension.

Together with the two-factor budget this leaves precisely actor ranks
four, five and six in the dual case. Source: Aschbacher–Smith, B.4.9(2)(iv),
printed pp.94–95, combined manuscript of 1 March 2004.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
open QuasisimpleSource BinaryLinear.OuterCyclic
open BinaryNaturalDual.FiveActors.Classification
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)

private theorem primeRank_eq_rank (A : Subgroup (LinearGroup 5))
    (hA : IsElementaryTwo A) : primeRank 2 A = rank A := by
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 (⊤ : Subgroup A) :=
    IsElementaryAbelian.of_surjective (Subgroup.topEquiv (G := A)).symm.toMonoidHom
      (Subgroup.topEquiv (G := A)).symm.surjective
  apply le_antisymm
  · exact IsElementaryAbelian.primeRank_le_of_card_le A hA.card_eq_two_pow_rank.le
  · exact IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup A)
      ((Subgroup.card_top (G := A)).trans hA.card_eq_two_pow_rank)

/-- A high-rank elementary actor lies in an actual interior block radical,
with its original matrix and module marking. No outer conjugator is used. -/
theorem interior_placement {A : Subgroup G} (hA : IsElementaryTwo A)
    (hr : 5 ≤ rank A) :
    ∃ W : Submodule (ZMod 2) (Space 5),
      (Module.finrank (ZMod 2) W = 2 ∨ Module.finrank (ZMod 2) W = 3) ∧
      A.map (groupEquiv d hF).toMonoidHom ≤ BinaryLinear.radical W := by
  let f := (groupEquiv d hF).toMonoidHom
  let E := A.map f
  let : IsElementaryAbelian 2 A := hA.2
  have hE : IsElementaryTwo E := ⟨fun h => hA.1
    ((Subgroup.map_eq_bot_iff_of_injective A (groupEquiv d hF).injective).mp h),
    IsElementaryAbelian.map f⟩
  let : IsElementaryAbelian 2 E := hE.2
  have hk : 5 ≤ primeRank 2 E := by
    rw [primeRank_eq_rank E hE, rank_map_injective f (groupEquiv d hF).injective]
    exact hr
  have hq := quadratic_of_primeRank_ge_five E hk
  exact ⟨displacementSpan E, radical_dimension E hq hk, le_radical_displacementSpan E hq⟩

include d hF

/-- The elementary-rank bound on the actual group in the source hypothesis. -/
theorem rank_le_six {A : Subgroup G} (hA : IsElementaryTwo A) : rank A ≤ 6 := by
  by_cases hr : rank A < 5
  · omega
  obtain ⟨W, hW, hle⟩ := interior_placement d hF hA (by omega)
  let f := (groupEquiv d hF).toMonoidHom
  let E := A.map f
  let : Finite G := Finite.of_injective (groupEquiv d hF) (groupEquiv d hF).injective
  have hc : Nat.card E ≤ 2 ^ ((5 - Module.finrank (ZMod 2) W) *
      Module.finrank (ZMod 2) W) :=
    (Subgroup.card_le_of_le hle).trans (card_radical_le W)
  rw [Subgroup.card_map_of_injective (groupEquiv d hF).injective,
    hA.card_eq_two_pow_rank] at hc
  rcases hW with hW | hW <;> rw [hW] at hc <;>
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

variable [FiniteDimensional (ZMod 2) V]

/-- The precise numerical alternatives before splitting. -/
theorem dual_rank_cases
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsOffender ρ A) :
    rank A = 4 ∨ rank A = 5 ∨ rank A = 6 := by
  let : Finite G := Finite.of_injective (groupEquiv d hF) (groupEquiv d hF).injective
  have := (d.dual_offender_bounds e hA).2.2
  have := rank_le_six d hF hA.1
  omega

/-- Strict offenders have rank six and cost five, with no rank premise. -/
theorem dual_strong_costs
    (e : d.space.quotientRepresentation.Equiv d.space.toRepresentation.dual)
    {A : Subgroup G} (hA : IsStrongOffender ρ A) :
    rank A = 6 ∧ fixedCodim ρ A = 5 ∧
      ((fixedCodim d.space.toRepresentation A = 2 ∧
          fixedCodim d.space.quotientRepresentation A = 3) ∨
        (fixedCodim d.space.toRepresentation A = 3 ∧
          fixedCodim d.space.quotientRepresentation A = 2)) := by
  let : Finite G := Finite.of_injective (groupEquiv d hF) (groupEquiv d hF).injective
  exact d.dual_strong_costs e hA (rank_le_six d hF hA.1)

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
