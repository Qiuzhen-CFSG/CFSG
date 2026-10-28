module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.Contracts
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct.Rank.Models

/-!
# Binary dimensions of the S₃ sections in B.5.6

An actual S₃ factor has a natural binary plane in both product alternatives.
For B.5.6(3), the existing `factor_quotient_plane` inspects all natural,
double-natural and exceptional cases: S₅ is excluded by order and SL₃ by
perfectness. Its quotient is the image modulo the global fixed space.
For B.5.6(5), perfectness again excludes the repeated SL₃ case, including
zero copies. In the remaining case, the SL₂ order formula forces field degree
one, and the given linear equivalence transports dimension two on the quotient
by the second factor's own fixed space. No splitting of the original module
is used. Factor placement is supplied independently by the group argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(3),(5),
printed p.105; applied in 13.6.10, printed p.928. The model exclusions reuse
`SolvableProduct/Rank/Models.lean` and the attributed ATLAS ports it imports.
-/

@[expose] public section

open Subgroup Representation
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products

private theorem sl2_degree_one (F : BinaryField)
    (e : SL(2, F.Carrier) ≃* Equiv.Perm (Fin 3)) : F.degree = 1 := by
  have hc : Nat.card F.Carrier * (Nat.card F.Carrier ^ 2 - 1) = 6 := by
    rw [← Atlas.card_sl_two, Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hp : 1 < Nat.card F.Carrier := Finite.one_lt_card
  have hq : Nat.card F.Carrier ^ 2 = (Nat.card F.Carrier ^ 2 - 1) + 1 := by
    have : 1 ≤ Nat.card F.Carrier ^ 2 := Nat.one_le_pow 2 _ (by omega)
    omega
  have htwo : Nat.card F.Carrier = 2 := by nlinarith
  apply Nat.pow_right_injective (by decide : 1 < 2)
  simpa using F.card_eq.symm.trans htwo

private theorem no_sl3 {K : Type*} [Field K]
    (e : SL(3, K) ≃* Equiv.Perm (Fin 3)) : False := by
  let := Atlas.sl_perfect (F := K) 3 (by decide)
  let : Group.IsPerfect (Equiv.Perm (Fin 3)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have h := Abelianization.commutator_subset_ker
    (Equiv.Perm.sign : Equiv.Perm (Fin 3) →* ℤˣ)
  rw [Group.IsPerfect.commutator_eq_top] at h
  have hx := h (mem_top (Equiv.swap (0 : Fin 3) 1))
  have hn : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) ≠ 1 := by decide
  exact hn hx

private theorem natural_dimension {D V : Type*} [Group D] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
    (F : BinaryField) (h : IsLinearNatural ρ F 2)
    (e : D ≃* Equiv.Perm (Fin 3)) : Module.finrank (ZMod 2) V = 2 := by
  obtain ⟨a⟩ := h
  have hdegree := sl2_degree_one F (a.groupEquiv.symm.trans e)
  rw [a.linearEquiv.finrank_eq]
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Fin 2 → F.Carrier)
  rw [Nat.card_fun, F.card_eq, hdegree, pow_one, Nat.card_fin, Nat.card_zmod] at hc
  exact (Nat.pow_right_injective (by decide : 1 < 2)) hc.symm

variable {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W)

/-- Every source factor whose actual actor is S₃ has a two-dimensional
image modulo the global fixed space, with all B.5.6(3) cases retained. -/
theorem cubicFactorSections : CubicFactorSections σ := by
  intro F U hc ⟨e⟩
  exact (CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct.Rank.factor_quotient_plane
    σ (hc.toBasic σ) e).2.1

/-- In both B.5.6(5) subcases, an actual S₃ second factor has dimension two
after quotienting its space by its own invariants. -/
theorem cubicHyperplaneSections : CubicHyperplaneSections σ := by
  intro F U hc ⟨e⟩
  cases hc with
  | linearThree r hr h =>
    obtain ⟨a⟩ := h
    exact (no_sl3 (a.groupEquiv.symm.trans e)).elim
  | linearTwo K h =>
    exact natural_dimension (reducedAction (U.toRepresentation.comp F.subtype)) K h e

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products
