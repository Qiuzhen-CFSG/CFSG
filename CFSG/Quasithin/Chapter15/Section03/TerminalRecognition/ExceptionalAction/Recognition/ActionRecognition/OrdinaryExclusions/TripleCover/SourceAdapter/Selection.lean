module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.TripleCover.SourceAdapter.Recovery
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.Source
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.Actor
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance.Models
import Mathlib.FieldTheory.Finite.GaloisField
public import Theory.SpecificGroups.FFG2DerivedCenter
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs

/-!
# Selecting the corrected triple-six section

The selection uses the source projective-line alternatives; its result
forgets all offender assertions and retains the exact original moved section.

The even hexacode automorphism group has order `1080` and a cubic centre.
Comparing these intrinsic invariants with every B.4.2 action alternative
leaves only the literal triple-six constructor.  The extension clause in
B.5.1 is eliminated separately by the subgroup-order divisibility forced by
the same order.  Consequently the selected section retains the exact moved
section supplied by the source conclusion.

Source: Aschbacher--Smith, B.4.2, printed p.86, B.5.1, printed p.99, and
the final proof of 15.3.1, printed p.1155 (combined manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open scoped MatrixGroups IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.SourceAdapter

private theorem not_hex_center_bot {L : Type*} [Group L]
    (e : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hZ : Subgroup.center L = ⊥) : False := by
  have hc := Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rw [hZ, Subgroup.card_bot, Representation.Hexacode.even_center_card] at hc
  norm_num at hc

private theorem not_hex_sl3 {L : Type*} [Group L]
    (eL : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F) : False := by
  let f : F ≃+* GaloisField 2 n :=
    (GaloisField.algEquivGaloisField 2 n hcard).toRingEquiv
  exact
    CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance.hex_not_equiv_sl3
      n (eL.symm.trans (e.trans (Atlas.fieldEquivSL 3 f)))

private theorem not_proper_extension {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] {L : Subgroup D}
    (ρ : Representation (ZMod 2) D W) (s : MovedSection ρ L)
    (eL : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (houter : OuterNaturalAction s.action) : False := by
  have hL : Nat.card L = 1080 := by
    rw [Nat.card_congr eL.toEquiv, Atlas.Codes.hexEven_card]
  rcases houter with ⟨⟨n, hnlo, hnhi, ⟨e⟩⟩⟩ | ⟨⟨e⟩⟩
  · have hdvd := L.card_subgroup_dvd_card
    rw [hL, Nat.card_congr e.groupEquiv.toEquiv, Nat.card_perm, Nat.card_fin] at hdvd
    interval_cases n <;> norm_num at hdvd
  · have hdvd := L.card_subgroup_dvd_card
    rw [hL, Nat.card_congr e.groupEquiv.toEquiv, Atlas.G2.card_Model,
      Nat.card_zmod] at hdvd
    norm_num at hdvd

private theorem center_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hZ : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  exact e.map_eq_one_iff.mp
    (hZ.le ((Subgroup.centerCongr e ⟨x, hx⟩).property))

private theorem not_hex_g2 {L : Type*} [Group L]
    (eL : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (BF : BinaryField) (e : L ≃* Atlas.G2.Model BF.Carrier) : False := by
  have hL : Nat.card L = 1080 := by
    rw [Nat.card_congr eL.toEquiv, Atlas.Codes.hexEven_card]
  have hc : Nat.card (Atlas.G2.Model BF.Carrier) = 1080 :=
    (Nat.card_congr e.toEquiv).symm.trans hL
  rw [Atlas.G2.card_Model, BF.card_eq] at hc
  have hd1 : 1 ≤ BF.degree := BF.degree_pos
  have hq : 2 ≤ 2 ^ BF.degree := by
    have hpow : 2 ^ 1 ≤ 2 ^ BF.degree :=
      Nat.pow_le_pow_right (by decide) hd1
    simpa using hpow
  have hq6 : 64 ≤ (2 ^ BF.degree) ^ 6 := by
    have hpow : (2 ^ 1) ^ 6 ≤ (2 ^ BF.degree) ^ 6 :=
      Nat.pow_le_pow_left hq 6
    norm_num at hpow ⊢
    exact hpow
  have hq2 : 4 ≤ (2 ^ BF.degree) ^ 2 := by
    have hpow : (2 ^ 1) ^ 2 ≤ (2 ^ BF.degree) ^ 2 :=
      Nat.pow_le_pow_left hq 2
    norm_num at hpow ⊢
    exact hpow
  have hq6m : 63 ≤ (2 ^ BF.degree) ^ 6 - 1 := by omega
  have hq2m : 3 ≤ (2 ^ BF.degree) ^ 2 - 1 := by omega
  have hbound : 12096 ≤ (2 ^ BF.degree) ^ 6 *
      ((2 ^ BF.degree) ^ 6 - 1) * ((2 ^ BF.degree) ^ 2 - 1) := by
    calc
      12096 = 64 * 63 * 3 := by norm_num
      _ ≤ (2 ^ BF.degree) ^ 6 * ((2 ^ BF.degree) ^ 6 - 1) *
          ((2 ^ BF.degree) ^ 2 - 1) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul hq6 hq6m) hq2m
  omega

private theorem tripleSix_of_irreducible {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {L H : Subgroup D}
    (eL : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (h : ProjectiveLine.IrreducibleActionCase ρ L H) : Nonempty (ProjectiveLine.TripleSixAction ρ L) := by
  cases h with
  | linearTwo F _ e _ _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.groupEquiv
        Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot)).elim
  | linearThree F _ e _ =>
      exact (not_hex_sl3 eL F.card_eq e.groupEquiv).elim
  | symplectic F _ _ e _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.groupEquiv
        Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot)).elim
  | symplecticTwo e _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv
        (e.subgroupEquiv.trans binarySymplecticDerivedEquiv)
        (alternatingGroup.center_eq_bot (by simp)))).elim
  | g2 F _ _ e _ _ => exact (not_hex_g2 eL F e.groupEquiv).elim
  | g2Two e _ _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.subgroupEquiv
        Theory.SpecificGroups.g2_derived_two_center_eq_bot)).elim
  | symmetric n hn e _ _ =>
      have hn4 : 4 ≤ n := by omega
      have hn4' : 4 ≤ Nat.card (Fin n) := by simpa using hn4
      exact (not_hex_center_bot eL (center_bot_of_equiv e.subgroupEquiv
        (alternatingGroup.center_eq_bot hn4'))).elim
  | alternatingSix _ e _ _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.groupEquiv
        (alternatingGroup.center_eq_bot (by simp)))).elim
  | alternatingSeven _ _ e _ _ _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e
        (alternatingGroup.center_eq_bot (by simp)))).elim
  | tripleSix _ action _ => exact ⟨action⟩
  | binaryLinear d _ _ e _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.groupEquiv
        (sl_binary_center_eq_bot d (by omega)))).elim
  | orthogonalSix _ _ e _ _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.groupEquiv
        (alternatingGroup.center_eq_bot (by simp)))).elim
  | symmetricEight _ e _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e.subgroupEquiv
        (alternatingGroup.center_eq_bot (by simp)))).elim
  | exteriorFive _ _ e _ _ _ =>
      exact (not_hex_center_bot eL (center_bot_of_equiv e
        (sl_binary_center_eq_bot 5 (by decide)))).elim

private theorem not_hex_sl_binary {L : Type*} [Group L]
    (eL : L ≃* Atlas.Codes.HexEvenAutomorphisms) {d : ℕ}
    (e : L ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2))
    (hd : 0 < d) : False :=
  not_hex_center_bot eL (center_bot_of_equiv e (sl_binary_center_eq_bot d hd))

/-- The selected section is the literal section from the source conclusion.
The equality in the result records that no replacement or quotient action is
being selected by this theorem. -/
theorem selectedSection_of_source {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {L : Subgroup D}
    (eL : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L) :
    ∃ s : SelectedSection ρ L, s.sectionData = c.sectionData := by
  cases c.clause_one with
  | irreducible _ hf hi hs hext =>
      have hwhole : L = ⊤ := by
        rcases hext with htop | ⟨_, houter⟩
        · exact htop
        · exact (not_proper_extension ρ c.sectionData eL houter).elim
      obtain ⟨triple⟩ := tripleSix_of_irreducible c.sectionData.action eL hs
      exact ⟨{ sectionData := c.sectionData
               whole := hwhole
               faithful := hf
               irreducible := hi
               centerEquiv := triple.centerEquiv
               dimension := triple.dimension }, rfl⟩
  | doubleThree F _ e _ _ => exact (not_hex_sl3 eL F.card_eq e.groupEquiv).elim
  | naturalDual d hd _ e =>
      obtain ⟨e⟩ := e
      exact (not_hex_sl_binary eL e.groupEquiv (by omega)).elim
  | repeatedNatural d r hd hr hb _ e =>
      obtain ⟨e⟩ := e
      exact (not_hex_sl_binary eL e.groupEquiv (by omega)).elim

/-- Nonempty form for consumers that only need the selected structure. -/
theorem exists_selectedSection_of_source {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {L : Subgroup D}
    (eL : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L) :
    Nonempty (SelectedSection ρ L) := by
  rcases selectedSection_of_source ρ eL c with ⟨s, _⟩
  exact ⟨s⟩

/-- Specialization to the literal generalized-Fitting offender action used by
the exceptional terminal branch.  The actor equivalence and source
conclusion remain explicit inputs for the final assembly. -/
theorem selectedSection_of_offender {H : Type*} [Group H] [Finite H]
    {V : Subgroup H} [IsElementaryAbelian 2 (moduleClosure V)]
    (d : SourceInput V)
    (eL : generalizedFitting d.offenderGroup ≃*
      Atlas.Codes.HexEvenAutomorphisms)
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup)) :
    ∃ s : SelectedSection d.offenderAction
      (generalizedFitting d.offenderGroup), s.sectionData = c.sectionData :=
  selectedSection_of_source d.offenderAction eL c

theorem exists_selectedSection_of_offender {H : Type*} [Group H] [Finite H]
    {V : Subgroup H} [IsElementaryAbelian 2 (moduleClosure V)]
    (d : SourceInput V)
    (eL : generalizedFitting d.offenderGroup ≃*
      Atlas.Codes.HexEvenAutomorphisms)
    (c : ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup)) :
    Nonempty (SelectedSection d.offenderAction
      (generalizedFitting d.offenderGroup)) := by
  rcases selectedSection_of_offender d eL c with ⟨s, _⟩
  exact ⟨s⟩

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.TripleCover.SourceAdapter
