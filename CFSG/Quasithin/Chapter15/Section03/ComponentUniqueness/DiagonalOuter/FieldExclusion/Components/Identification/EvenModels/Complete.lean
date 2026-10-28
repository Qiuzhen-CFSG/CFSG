module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.G2
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Triality
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Ree
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.FiniteModels.Basic
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Outer
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.SpecificGroups.Triality.InvolutionFixedComponents
public import Theory.SpecificGroups.PSL3Even.FixedComponents

/-!
# Complete even-model sieve for the selected field component

The literal ordinary PSL₃(2) fixed component is transported through each
model marking. Existing full automorphism and fixed-component rows exclude
G₂ and triality; the linear-three component theorem forces field order four.
The existing symplectic, rank-one and Ree exclusions complete the even list.

Source: Aschbacher–Smith, proof of 15.3.38, printed p.1137. These are
exact source-component exclusions, consumed by `Identification.Complete`.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
variable {S : Type*} [Group S] (s : SimpleInput S)
include s

/-- The proved outer fixed-group descent discharges the G₂ source row. -/
theorem SimpleInput.not_even_g2 {n : ℕ} (hn : 2 ≤ n) :
    ¬ ClassificationModels.IsG2At S (2 ^ n) := by
  rintro ⟨F, _, _, hc, ⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (show Fintype.card F = 2 ^ n by simpa only [Nat.card_eq_fintype_card] using hc)
  have hq : 2 < Nat.card F := by
    rw [hc]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  let a := MulAut.congr e s.involution
  have ha : orderOf a = 2 := ((MulAut.congr e).orderOf_eq _).trans s.involution_order
  obtain ⟨σ, m, hm, hmn, hnm, hcard, he⟩ :=
    Atlas.G2.EvenFieldFixedResidual.outer_involution_smaller_fixed_model hn hc a ha
      (s.g2_involution_not_inner hq e)
  exact s.not_g2_fixed_model e he

/-- The genuine full binary automorphism group discharges the derived endpoint. -/
theorem SimpleInput.not_binary_g2 :
    ¬ Nonempty (S ≃* commutator (Atlas.G2.Model (ZMod 2))) :=
  s.not_binary_g2_of_automorphism_coverage
    Atlas.G2.LieAutomorphismExtensions.binaryConjugation_bijective

/-- The completed inner parabolic and outer fixed-component rows exclude triality. -/
theorem SimpleInput.not_even_triality {n : ℕ} (hn : 0 < n) :
    ¬ Triality.Standard.IsTrialityGroupAt (2 ^ n) S := by
  intro h
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff S n hn).mp h
  obtain ⟨a, ha, D, hD, ⟨eD⟩⟩ := s.fixed_component_of_equiv e
  by_cases hi : a ∈ MulAut.innerSubgroup (Triality.Standard.BinaryCarrier n hn)
  · exact EvenModels.TrialityCase.not_fixed_component_of_inner n hn a ha hi D ⟨eD⟩
  · have hr := Triality.Standard.EvenField.outer_fixed_component_rank_gt_two n hn a ha hi D hD
    rw [primeRank_equiv 2 eD, Matrix.PSL3Even.two_rank (ZMod 2) (n := 1)
      (by decide) (by simp)] at hr
    omega

/-- The marked PSL₃(2) component forces the binary linear-three parameter to four. -/
theorem SimpleInput.even_linear_three_equiv_four {n : ℕ} (hn : 0 < n)
    (h : ClassicalGroup.IsPSL S 3 (2 ^ n)) :
    Nonempty (S ≃* Matrix.PSL3Four.PSL) := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  obtain ⟨a, ha, D, hD, ⟨eD⟩⟩ := s.fixed_component_of_equiv e
  have hr : primeRank 2 D ≤ 2 := by
    rw [primeRank_equiv 2 eD, Matrix.PSL3Even.two_rank (ZMod 2) (n := 1)
      (by decide) (by simp)]
  let P : Sylow 2 D := default
  have hnc : ¬ ∀ x y : P, x ^ 2 = 1 → y ^ 2 = 1 → Commute x y := by
    intro hc
    exact Matrix.PSL3Two.not_injective_of_sylow_involutions_commute P hc
      eD.symm.toMonoidHom eD.symm.injective
  have hn2 := (Matrix.PSL3Even.FixedComponents.component_field_degree_two
    hn hc a ha D hD hr P hnc).1
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let f : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hc, hn2, Matrix.PSL3Four.card_F]
    norm_num)
  exact ⟨e.trans (Atlas.fieldEquivPSL 3 f)⟩

/-- The full rank-two characteristic-two list has precisely the PSL₃(4) survivor. -/
theorem SimpleInput.even_rank_two_equiv_four [Finite S] {n : ℕ}
    (h : ChapterA.Section02.IsTheoremCRankTwoModel S n) :
    Nonempty (S ≃* Matrix.PSL3Four.PSL) := by
  rcases s.even_rank_two_remaining h with h | h | h | h | h
  · exact s.even_linear_three_equiv_four (by omega) h.2
  · exact (s.not_even_g2 h.1 h.2).elim
  · exact (s.not_even_triality (by omega) h.2).elim
  · obtain ⟨m, hm, _, he⟩ := h
    exact (s.not_reeF4 hm he).elim
  · exact (s.not_binary_g2 h.2).elim
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
