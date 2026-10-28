module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows.HighRows.Orders

/-!
# Recovering the full G₂(2) actor from the source action

The order 6048 of the component excludes every irreducible B.4.2
constructor except the marked G₂(2) action. That mark identifies the
section's offender subgroup with the full octonion group, so its inverse
followed by the literal inclusion is an embedding of G₂(2) in the original
actor. The other three B.5.1(1) branches have incompatible linear actors.
Thus the full action, not just the component-family comparison, is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.2, printed p.86; B.5.1, p.99; the terminal proof on p.1155.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection.ComponentRows.HighRows
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

private theorem sl_card_mul (F : Type*) [Field F] [Finite F]
    (n : ℕ) [NeZero n] :
    Nat.card SL(n,F) * (Nat.card F - 1) =
      ∏ i : Fin n, (Nat.card F ^ n - Nat.card F ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(n,F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul n

private theorem not_sl_two {L : Type*} [Group L] (hc : Nat.card L = 6048)
    {F : Type*} [Field F] [Finite F] (e : L ≃* SL(2,F)) : False := by
  rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two] at hc
  let q := Nat.card F
  change q * (q ^ 2 - 1) = 6048 at hc
  by_cases hq : q ≤ 18
  · have hb : q * (q ^ 2 - 1) ≤ 18 * (18 ^ 2 - 1) := by gcongr
    omega
  · have hb : 19 * (19 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by gcongr <;> omega
    omega

private theorem not_sl_three {L : Type*} [Group L] (hc : Nat.card L = 6048)
    {F : Type*} [Field F] [Finite F] (e : L ≃* SL(3,F)) : False := by
  have hcard : Nat.card SL(3,F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(3,F)),
      Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
    exact Matrix.PSL3.LinearThree.card_projective_mul_scalar F
  rw [Nat.card_congr e.toEquiv, hcard] at hc
  let q := Nat.card F
  change q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) = 6048 at hc
  by_cases hq : q ≤ 3
  · have hb : q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) ≤
        3 ^ 3 * (3 ^ 3 - 1) * (3 ^ 2 - 1) := by gcongr
    omega
  · have hb : 4 ^ 3 * (4 ^ 3 - 1) * (4 ^ 2 - 1) ≤
        q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) := by gcongr <;> omega
    omega

private theorem not_sp_four {L : Type*} [Group L] (hc : Nat.card L = 6048)
    {F : Type*} [Field F] [Finite F] (e : L ≃* Matrix.symplecticGroup (Fin 2) F) : False := by
  rw [Nat.card_congr e.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp] at hc
  let q := Nat.card F
  change q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1) = 6048 at hc
  by_cases hq : q ≤ 2
  · have hb : q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1) ≤
        2 ^ 4 * (2 ^ 2 - 1) * (2 ^ 4 - 1) := by gcongr
    omega
  · have hb : 3 ^ 4 * (3 ^ 2 - 1) * (3 ^ 4 - 1) ≤
        q ^ 4 * (q ^ 2 - 1) * (q ^ 4 - 1) := by gcongr <;> omega
    omega

private theorem not_g2 {L : Type*} [Group L] (hc : Nat.card L = 6048)
    {F : Type*} [Field F] [Finite F] (e : L ≃* Atlas.G2.Model F) : False := by
  rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model] at hc
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hb : 2 ^ 6 * (2 ^ 6 - 1) * (2 ^ 2 - 1) ≤
      Nat.card F ^ 6 * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1) := by gcongr
  omega

private theorem not_alternating {L : Type*} [Group L] (hc : Nat.card L = 6048)
    {n : ℕ} (hlo : 5 ≤ n) (hhi : n ≤ 8) (e : L ≃* alternatingGroup (Fin n)) : False := by
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hc
  interval_cases n <;> norm_num at hc

private theorem not_binary_linear {L : Type*} [Group L] (hc : Nat.card L = 6048)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : L ≃* SL(n,ZMod 2)) : False := by
  rcases hn with rfl | rfl
  · have hh := sl_card_mul (ZMod 2) 4
    rw [← Nat.card_congr e.toEquiv, hc] at hh
    norm_num [Fin.prod_univ_succ] at hh
  · have hh := sl_card_mul (ZMod 2) 5
    rw [← Nat.card_congr e.toEquiv, hc] at hh
    norm_num [Fin.prod_univ_succ] at hh

private theorem irreducible_g2_marked {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    {L I : Subgroup D} (hc : Nat.card L = 6048) (h : IrreducibleActionCase ρ L I) :
    Nonempty (MarkedActionEquiv ρ I L (g2Natural (ZMod 2))
      (commutator (Atlas.G2.Model (ZMod 2)))) ∧
      (∀ A, IsBestOffender ρ A → rank A = 3) ∧ quadraticRatio ρ = 1 := by
  cases h with
  | linearTwo _ _ e _ _ => exact (not_sl_two hc e.groupEquiv).elim
  | linearThree _ _ e _ => exact (not_sl_three hc e.groupEquiv).elim
  | symplectic _ _ _ e _ => exact (not_sp_four hc e.groupEquiv).elim
  | symplecticTwo e _ =>
    exact (not_alternating hc (by decide) (by decide)
      (e.subgroupEquiv.trans binarySymplecticDerivedEquiv)).elim
  | g2 _ _ _ e _ _ => exact (not_g2 hc e.groupEquiv).elim
  | g2Two e offenders ratio => exact ⟨⟨e⟩, offenders, ratio⟩
  | symmetric n hn e _ _ =>
    exact (not_alternating hc (by omega) (by omega) e.subgroupEquiv).elim
  | alternatingSix _ e _ _ =>
    exact (not_alternating hc (by decide) (by decide) e.groupEquiv).elim
  | alternatingSeven _ _ e _ _ _ =>
    exact (not_alternating hc (by decide) (by decide) e).elim
  | tripleSix _ action _ =>
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
    rw [Nat.card_congr action.centerEquiv.toEquiv, Nat.card_congr action.quotientEquiv.toEquiv,
      nat_card_alternatingGroup, hc] at hh
    norm_num at hh
  | binaryLinear n hn _ e _ => exact (not_binary_linear hc hn e.groupEquiv).elim
  | orthogonalSix _ _ e _ _ =>
    exact (not_alternating hc (by decide) (by decide) e.groupEquiv).elim
  | symmetricEight _ e _ =>
    exact (not_alternating hc (by decide) (by decide) e.subgroupEquiv).elim
  | exteriorFive _ _ e _ _ _ =>
    exact (not_binary_linear hc (Or.inr rfl) e).elim

/-- Select the literal marked action on the original central section and
retain its rank-three best-offender clause. -/
theorem source_g2_marked {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    {L : Subgroup D} (c : QuasisimpleSourceConclusion ρ L) (hc : Nat.card L = 6048) :
    Function.Injective c.sectionData.action ∧
      Nonempty (MarkedActionEquiv c.sectionData.action
      (offenderSubgroup c.sectionData.action) L (g2Natural (ZMod 2))
      (commutator (Atlas.G2.Model (ZMod 2)))) ∧
      (∀ A, IsBestOffender c.sectionData.action A → rank A = 3) ∧
      quadraticRatio c.sectionData.action = 1 := by
  cases c.clause_one with
  | irreducible _ faithful _ h _ =>
    exact ⟨faithful, irreducible_g2_marked c.sectionData.action hc h⟩
  | doubleThree _ _ e _ _ => exact (not_sl_three hc e.groupEquiv).elim
  | naturalDual _ hn _ h =>
    obtain ⟨e⟩ := h
    exact (not_binary_linear hc hn e.groupEquiv).elim
  | repeatedNatural _ _ hn _ _ _ h =>
    obtain ⟨e⟩ := h
    exact (not_binary_linear hc hn e.groupEquiv).elim

/-- The marked B.4.2 action forces a full G₂(2) subgroup of the original
actor. Its embedding comes from the source action equivalence. -/
theorem source_contains_full_g2 {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    {L : Subgroup D} (c : QuasisimpleSourceConclusion ρ L) (hc : Nat.card L = 6048) :
    ∃ f : Atlas.G2.Model (ZMod 2) →* D, Function.Injective f := by
  obtain ⟨_, ⟨e⟩, _⟩ := source_g2_marked ρ c hc
  exact ⟨(offenderSubgroup c.sectionData.action).subtype.comp e.action.groupEquiv.symm.toMonoidHom,
    Subtype.val_injective.comp e.action.groupEquiv.symm.injective⟩

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection.ComponentRows.HighRows
