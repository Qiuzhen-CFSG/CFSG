module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.Actions
public import Theory.SpecificGroups.PSL3Even.ResidualComparison

/-!
# Centrality and residual invariants for binary PSL₃

The highest-root involution centralizes the actual unitriangular Sylow
subgroup. Conjugacy of involutions and the faithful inner action therefore
mark every inner involutory automorphism as two-central.

Taking O³ preserves solvability, since its quotient is a three-group.
For a component with central quotient PSL₃(2), the order formula rules out
any even-exponent full PSL₃ model, so the modification in 16.5.5 is absent.
This endpoint argument retains the central kernel: centerlessness is deduced
only under the contrary full-model identification.

Source: Aschbacher–Smith, 16.1.2–4, printed pp.1170–1172, and
16.5.5–6(4), printed p.1197 of the combined manuscript of 1 March 2004.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.LinearThree
open Matrix.PSL3.EvenInnerCentralizers Matrix.PSL3Even.ResidualComparison
open Matrix.PSL3Even.UnipotentGeometry

variable (F : Type*) [Field F] [Finite F] {n : ℕ}

private theorem binary_char (hn : 0 < n) (hF : Nat.card F = 2 ^ n) : ringChar F = 2 := by
  let := Fintype.ofFinite F
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, hF]
  exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt hn))

/-- The concrete highest-root involution lies in the center of a Sylow two-group. -/
theorem root_twoCentral (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    IsTwoCentralIn (⊤ : Subgroup PSL(3,F)) (root F) := by
  let : CharP F 2 := ringChar.of_eq (binary_char F hn hF)
  let S := Matrix.PSL3.LinearThree.unipotentSylow F hn hF
  let e : PSL(3,F) ≃* (⊤ : Subgroup PSL(3,F)) := topEquiv.symm
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨orderOf_eq_prime (root_sq F) (root_ne_one F),
    (P : Subgroup (⊤ : Subgroup PSL(3,F))).map (⊤ : Subgroup PSL(3,F)).subtype,
    ⟨P, rfl⟩, ?_, ?_⟩
  · refine ⟨e (root F), ?_, rfl⟩
    refine ⟨root F, ?_, rfl⟩
    change root F ∈ Matrix.PSL3.LinearThree.unipotent F
    rw [← Matrix.PSL3.LinearThree.projective_range]
    exact ⟨⟨0,0,1⟩, rfl⟩
  · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    change z ∈ Subgroup.centralizer {root F}
    change z ∈ Matrix.PSL3.LinearThree.unipotent F at hz
    rw [← Matrix.PSL3.LinearThree.projective_range] at hz
    obtain ⟨w, rfl⟩ := hz
    exact projective_mem_centralizer F w

/-- Every inner involutory automorphism has its individual Sylow-centrality marking. -/
theorem inner_twoCentral (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (a : MulAut PSL(3,F)) (ha : orderOf a = 2)
    (hi : ∃ x, a = MulAut.conj x) :
    IsTwoCentralIn (MulAut.innerSubgroup PSL(3,F)) a := by
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect PSL(3,F) := Atlas.psl_perfect 3 (by decide)
  have hc : center PSL(3,F) = ⊥ := center_eq_bot_of_simple_perfect
  obtain ⟨t, ht, rfl, _⟩ := MulAut.inner_involution_representative hc a ha hi
  have ht1 : t ≠ 1 := by intro h; simp [h] at ht
  obtain ⟨g, hg⟩ := isConj_iff.mp (involution_isConj_root_of_pos F hn hF t ht1
    (ht ▸ pow_orderOf_eq_one t))
  have hr := twoCentral_map (root_twoCentral F hn hF) (MulAut.conj g).symm
  have he : (MulAut.conj g).symm (root F) = t := (MulAut.conj g).symm_apply_eq.mpr hg.symm
  rw [he, map_top_of_surjective _ (MulAut.conj g).symm.surjective] at hr
  have h := (twoCentral_map_injective_iff (MulAut.conj : PSL(3,F) →* MulAut PSL(3,F))
    (MulAut.conj_injective_of_center_eq_bot hc)).mpr hr
  simpa only [← MonoidHom.range_eq_map, MulAut.innerSubgroup] using h

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- The actual O³ modification neither creates nor removes solvability. -/
theorem modified_solvable_iff (u : G) :
    Group.IsSolvable (modifiedCentralizerResidual L u) ↔
      Group.IsSolvable (involutionTwoResidual L u) := by
  classical
  by_cases hL : HasEvenLinearThreeType L
  · rw [modifiedCentralizerResidual, if_pos hL]
    let e := (pResidual 3 (involutionTwoResidual L u)).equivMapOfInjective
      (involutionTwoResidual L u).subtype (subtype_injective _)
    have hq : Group.IsSolvable (involutionTwoResidual L u ⧸
        pResidual 3 (involutionTwoResidual L u)) := by
      let : Group.IsNilpotent (involutionTwoResidual L u ⧸
        pResidual 3 (involutionTwoResidual L u)) :=
        (isPGroup_quotient_pResidual 3).isNilpotent
      infer_instance
    constructor
    · intro h
      let := h
      have hp : Group.IsSolvable (pResidual 3 (involutionTwoResidual L u)) :=
        Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      exact (Group.isSolvable_iff_subgroup_quotient _).mpr ⟨hp, hq⟩
    · intro h
      let := h
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · rw [modifiedCentralizerResidual, if_neg hL]

omit [Finite G] in
/-- The order-168 full model cannot have a positive even field exponent. -/
theorem not_even_type_of_binary_model (hF : Nat.card F = 2)
    (e : L ≃* PSL(3,F)) : ¬ HasEvenLinearThreeType L := by
  have hL : Nat.card L = 168 := by
    rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective, hF]
    norm_num
  rintro ⟨m, hm, ⟨k, hk⟩, E, hfield, hfinite, hE, ⟨d⟩⟩
  have hm2 : 2 ≤ m := by omega
  have hq : 4 ≤ Nat.card E := by
    rw [hE]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hm2
  have hcard := Matrix.PSL3.LinearThree.card_projective_mul_scalar E
  rw [← Nat.card_congr d.toEquiv, hL] at hcard
  have hd : Nat.gcd 3 (Nat.card E - 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
  have hlow : 4 ^ 3 * (4 ^ 3 - 1) * (4 ^ 2 - 1) ≤
      Nat.card E ^ 3 * (Nat.card E ^ 3 - 1) * (Nat.card E ^ 2 - 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
  omega

omit [Finite G] in
/-- Even full models are also excluded when only the central quotient is PSL₃(2). -/
theorem not_even_type_of_binary_quotient_model (hF : Nat.card F = 2)
    (e : (L ⧸ center L) ≃* PSL(3,F)) : ¬ HasEvenLinearThreeType L := by
  intro heven
  have hevenCopy := heven
  obtain ⟨m, _, _, E, hfield, hfinite, _, ⟨d⟩⟩ := heven
  let : IsSimpleGroup PSL(3,E) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect PSL(3,E) := Atlas.psl_perfect 3 (by decide)
  have hZ : center L = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr d).toEquiv,
      (center_eq_bot_of_simple_perfect : center PSL(3,E) = ⊥)]
    simp
  let c : L ≃* PSL(3,F) :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  exact not_even_type_of_binary_model F hF c hevenCopy

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows.LinearThree
