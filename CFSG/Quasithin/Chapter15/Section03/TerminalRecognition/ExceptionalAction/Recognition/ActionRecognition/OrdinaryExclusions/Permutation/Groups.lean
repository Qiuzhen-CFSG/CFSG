module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Reduction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Quotient
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition

/-!
# The actual permutation actor and its marked residual pair

Normality and nontriviality put the offender image between Aₙ and Sₙ, for
n ≥ 5; both possibilities are retained. The source Goldschmidt triple and
its literal two-residuals transport through any full-quotient equivalence.
For S₆ the checked residual-pair theorem identifies both marked residuals
as A₄ and their two-cores as intersecting four-groups generating D₈.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
proof of 15.3.1, printed p.1155; the S₆ parabolics are described in I.5.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- Every nontrivial normal permutation actor contains the alternating group. -/
theorem alternating_le_offender {n : ℕ} (hn : 5 ≤ n) (e : coreQuotient H ≃* Equiv.Perm (Fin n)) :
    alternatingGroup (Fin n) ≤ d.offenderGroup.map e.toMonoidHom := by
  let _ : (d.offenderGroup.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ e.surjective
  have hne : d.offenderGroup.map e.toMonoidHom ≠ ⊥ :=
    fun h => d.offenderGroup_ne_bot
      ((d.offenderGroup.map_eq_bot_iff_of_injective e.injective).mp h)
  exact Equiv.Perm.alternatingGroup_le_of_normal (by simpa using hn)
    ((nontrivial_iff_ne_bot _).mpr hne)

/-- Retain both possible offender images, without identifying it with the full quotient. -/
theorem offender_image_cases {n : ℕ} (hn : 5 ≤ n)
    (e : coreQuotient H ≃* Equiv.Perm (Fin n)) :
    d.offenderGroup.map e.toMonoidHom = alternatingGroup (Fin n) ∨
      d.offenderGroup.map e.toMonoidHom = ⊤ := by
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hi := index_dvd_of_le (alternating_le_offender d hn e)
  rw [alternatingGroup.index_eq_two] at hi
  rcases (Nat.dvd_prime Nat.prime_two).mp hi with h | h
  · exact Or.inr (index_eq_one.mp h)
  · exact Or.inl (Equiv.Perm.eq_alternatingGroup_of_index_eq_two h)
omit [IsElementaryAbelian 2 (moduleClosure V)] in
theorem model_goldschmidt {n : ℕ} (e : coreQuotient H ≃* Equiv.Perm (Fin n)) :
    ChapterF.IsGoldschmidtTriple
      (d.G1.map (e.toMonoidHom.comp coreProjection))
      (d.G2.map (e.toMonoidHom.comp coreProjection)) := by
  let f := e.toMonoidHom.comp coreProjection
  have hk : f.ker = pCore 2 H := by
    ext x
    change e (coreProjection x) = 1 ↔ x ∈ pCore 2 H
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  apply d.goldschmidt.map_of_two_kernel f
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  · rw [hk]; exact pCore_isPGroup
  · rw [hk]; exact d.goldschmidt.twoCore_isGreatest.1.1

omit [IsElementaryAbelian 2 (moduleClosure V)] in
theorem first_model_residual {n : ℕ}
    (e : coreQuotient H ≃* Equiv.Perm (Fin n)) :
    (pResidual 2 (d.G1.map (e.toMonoidHom.comp coreProjection))).map
        (d.G1.map (e.toMonoidHom.comp coreProjection)).subtype =
      d.YF.map (e.toMonoidHom.comp coreProjection) := by
  rw [← map_embedded_pResidual, d.first_residual]

omit [IsElementaryAbelian 2 (moduleClosure V)] in
theorem second_model_residual {n : ℕ}
    (e : coreQuotient H ≃* Equiv.Perm (Fin n)) :
    (pResidual 2 (d.G2.map (e.toMonoidHom.comp coreProjection))).map
        (d.G2.map (e.toMonoidHom.comp coreProjection)).subtype =
      d.XE.map (e.toMonoidHom.comp coreProjection) := by
  rw [← map_embedded_pResidual, d.second_residual]

private theorem sylow_index_three {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) :
    (S : Subgroup G).index = 3 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ x ∈ pCore 2 G
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let R := S.mapSurjective hf
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hR : Nat.card R = 2 := by
    rw [R.card_eq_multiplicity, hc]
    change 2 ^ (Nat.factorization (2 * 3) 2) = 2
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hi := (R : Subgroup (Equiv.Perm (Fin 3))).index_mul_card
  rw [hc, hR] at hi
  have hi3 : (R : Subgroup (Equiv.Perm (Fin 3))).index = 3 := by omega
  change ((S : Subgroup G).map f).index = 3 at hi3
  rwa [Subgroup.index_map_eq _ hf (by rw [hk]; exact pCore_isPGroup.le_sylow_of_normal S)] at hi3

omit [IsElementaryAbelian 2 (moduleClosure V)] in
theorem model_sylow_indices {n : ℕ} (e : coreQuotient H ≃* Equiv.Perm (Fin n)) :
    ∃ S : Sylow 2 (Equiv.Perm (Fin n)),
      (S : Subgroup _) ≤ d.G1.map (e.toMonoidHom.comp coreProjection) ∧
      (S : Subgroup _) ≤ d.G2.map (e.toMonoidHom.comp coreProjection) ∧
      (S : Subgroup _).relIndex (d.G1.map (e.toMonoidHom.comp coreProjection)) = 3 ∧
      (S : Subgroup _).relIndex (d.G2.map (e.toMonoidHom.comp coreProjection)) = 3 := by
  have h := model_goldschmidt d e
  obtain ⟨S, hS⟩ := h.intersection_sylow
  have h1 := hS.symm.le.trans inf_le_left
  have h2 := hS.symm.le.trans inf_le_right
  exact ⟨S, h1, h2, sylow_index_three (S.subtype h1) h.quotient_left.some,
    sylow_index_three (S.subtype h2) h.quotient_right.some⟩

omit [IsElementaryAbelian 2 (moduleClosure V)] in
theorem six_residual_pair (e : coreQuotient H ≃* Equiv.Perm (Fin 6)) :
    let L₁ := d.YF.map (e.toMonoidHom.comp coreProjection)
    let L₂ := d.XE.map (e.toMonoidHom.comp coreProjection)
    Nonempty (L₁ ≃* alternatingGroup (Fin 4)) ∧
      Nonempty (L₂ ≃* alternatingGroup (Fin 4)) ∧
      Nat.card (L₁.pCoreIn 2) = 4 ∧ Nat.card (L₂.pCoreIn 2) = 4 ∧
      Nonempty (↥(L₁.pCoreIn 2 ⊔ L₂.pCoreIn 2) ≃* DihedralGroup 4) ∧
      L₁.pCoreIn 2 ⊓ L₂.pCoreIn 2 ≠ ⊥ := by
  obtain ⟨S, h1, h2, hi1, hi2⟩ := model_sylow_indices d e
  have h := Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.residual_pair_recognition
    S _ _ h1 h2 hi1 hi2 (model_goldschmidt d e).generated
  dsimp only at h ⊢
  rwa [first_model_residual d e, second_model_residual d e] at h
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
