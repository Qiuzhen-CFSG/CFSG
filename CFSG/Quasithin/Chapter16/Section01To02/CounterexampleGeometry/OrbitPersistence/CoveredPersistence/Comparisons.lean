module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredPersistence.ModelAlternatives
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Excluding the proper enlargement endpoints

A two-core extension of Sz(8) has order prime to three. This excludes the
field-derived and unitary endpoints as soon as their concrete divisibility
comparisons are supplied. Every other endpoint in 16.1.7(3) is proved simple
using its actual isomorphism, which contradicts the nontrivial two-core.
Both the symplectic/Suzuki and Rudvalis/Suzuki branches are retained.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, pp.1172–1174.
The two intrinsic comparison inputs below are additional obligations of the
covered-persistence assembly; they are not asserted as source theorems.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
universe v
variable {L J : Type v} [Group L] [Group J] [Finite L]

/-- The whole covered group, as well as its quotient, has order prime to three. -/
theorem three_not_dvd_card_of_coveredSuzuki
    (iso : Nonempty ((L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup 1)) :
    ¬ 3 ∣ Nat.card L := by
  obtain ⟨e⟩ := iso
  have hq : ¬ 3 ∣ (pCore 2 L).index := by
    change ¬ 3 ∣ Nat.card (L ⧸ pCore 2 L)
    rw [Nat.card_congr e.toEquiv]
    exact (BenderSuzuki.External.huppert_blackburn_XI_3_6 1 (by decide)).2
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  rw [← (pCore 2 L).card_mul_index, hn]
  exact fun h => (Nat.prime_three.dvd_mul.mp h).elim
    (fun h => (by norm_num : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)) hq

omit [Finite L] in
/-- A nontrivial two-core with nontrivial Suzuki quotient excludes simplicity. -/
theorem not_simple_of_coveredSuzuki (hne : pCore 2 L ≠ ⊥)
    (iso : Nonempty ((L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup 1)) :
    ¬ IsSimpleGroup L := by
  intro hs
  let := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 2 L) inferInstance with hb | ht
  · exact hne hb
  · obtain ⟨e⟩ := iso
    have hcard : Nat.card (SuzukiMatrixGroup 1) = 1 := by
      rw [← Nat.card_congr e.toEquiv]
      change (pCore 2 L).index = 1
      rw [ht, Subgroup.index_top]
    let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 1 (by decide)).1
    have := Finite.one_lt_card (α := SuzukiMatrixGroup 1)
    omega

omit [Finite L] in
private theorem simple_of_alternating {n : ℕ} (hn : 5 ≤ n)
    (iso : Nonempty (L ≃* alternatingGroup (Fin n))) : IsSimpleGroup L := by
  obtain ⟨e⟩ := iso
  let := alternatingGroup.isSimpleGroup (by simpa using hn : 5 ≤ Nat.card (Fin n))
  exact e.isSimpleGroup

/-- Eliminate all nine model pairs. The only remaining numerical inputs are
explicit intrinsic comparisons for the field-derived and unitary endpoints. -/
theorem not_properModels_of_comparisons
    (fieldThree : ∀ X, FieldDerivedThreeInput X) (unitaryThree : UnitaryThreeInput)
    (hne : pCore 2 L ≠ ⊥)
    (iso : Nonempty ((L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup 1)) :
    ¬ ProperModels L J := by
  have hsimple := not_simple_of_coveredSuzuki hne iso
  have hthree := three_not_dvd_card_of_coveredSuzuki iso
  intro h
  cases h with
  | field X n hn _ small =>
    obtain ⟨M, hM, hfin, hmodel, ⟨e⟩⟩ := small
    obtain ⟨eS⟩ := iso
    have hd := fieldThree X M hM hfin n hn hmodel
    have he : Nat.card (SuzukiMatrixGroup 1) = Nat.card (commutator M) :=
      Nat.card_congr (eS.symm.trans e).toEquiv
    exact (BenderSuzuki.External.huppert_blackburn_XI_3_6 1 (by decide)).2
      (he ▸ hd)
  | graph_field_linear n hn _ small =>
    obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := small
    apply hthree
    rw [Nat.card_congr e.toEquiv]
    exact unitaryThree F hF hfin J n hn hcard hconj
  | graph_linear_unitary n hn _ small =>
    obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := small
    have hfour : 4 ≤ Nat.card F := by
      rw [hcard]
      exact Nat.pow_le_pow_right (show 0 < 2 by decide) (show 2 ≤ n by omega)
    let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
    exact hsimple e.isSimpleGroup
  | graph_field_symplectic m hm _ small =>
    obtain ⟨e⟩ := small
    let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    exact hsimple e.isSimpleGroup
  | graph_binary _ _ _ small => exact hsimple (simple_of_alternating (by decide) small)
  | mathieu_janko _ small => exact hsimple (simple_of_alternating (by decide) small)
  | janko_linear _ small =>
    obtain ⟨F, _, _, _, ⟨e⟩⟩ := small
    let := Atlas.psl_simple_high_rank (F := F) 3 (by decide)
    exact hsimple e.isSimpleGroup
  | higman_sims _ small =>
    rcases small with small | small
    · exact hsimple (simple_of_alternating (by decide) small)
    · exact hsimple (simple_of_alternating (by decide) small)
  | rudvalis _ small =>
    obtain ⟨e⟩ := small
    let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 1 (by decide)).1
    exact hsimple e.isSimpleGroup

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence
end
