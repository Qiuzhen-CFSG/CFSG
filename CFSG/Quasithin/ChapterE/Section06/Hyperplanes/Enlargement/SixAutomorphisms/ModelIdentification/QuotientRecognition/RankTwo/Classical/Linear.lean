module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Inputs
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SU3.SixSubgroupExclusion
public import BenderSuzuki.External.Huppert.II.theorem_8_27
public import Theory.GroupTheory.SolvableResidual

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
/-!
# Screening the linear-three involution residuals

Every perfect component of a fixed group lies in its two-residual. The solvable
residual cases have no such component. A simple linear-three residual has
only itself as a component, and the exact projective order, including its scalar
divisor, differs from 360. Binary linear-two and unitary-three residuals cannot
even contain A₆: their Sylow two-subgroups have commuting involutions.

The residual-model alternatives here are genuine matrix isomorphisms, with
solvable endpoints retained. They are an outstanding table input, not an
assertion that all linear-three automorphisms have been classified.

Source: Aschbacher–Smith, 16.1.4(1),(4)–(6), printed p.1171;
E.6.23, printed p.254.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
private abbrev A6 := alternatingGroup (Fin 6)
private instance : Group.IsPerfect A6 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩

private theorem card_psl_three_ne_six {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) : Nat.card PSL(3,F) ≠ 360 := by
  intro hc
  have he := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
  rw [hc] at he
  by_cases hn1 : n = 1
  · subst n
    norm_num [hF] at he
  · have hq : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 2 ≤ n by omega)
    have hg : Nat.gcd 3 (Nat.card F - 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
    have hbig : 60480 ≤ Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
      calc
        60480 = 4 ^ 3 * (4 ^ 3 - 1) * (4 ^ 2 - 1) := by norm_num
        _ ≤ _ := by gcongr
    omega

private theorem perfect_le_twoResidual {H : Type*} [Group H] [Finite H]
    (P : Subgroup H) [Group.IsPerfect P] : P ≤ pResidual 2 H := by
  let : Group.IsNilpotent (H ⧸ pResidual 2 H) :=
    (Subgroup.isPGroup_quotient_pResidual (G := H) 2).isNilpotent
  exact (le_solvableResidual_of_isPerfect P).trans
    (solvableResidual_le_of_solvable_quotient (pResidual 2 H))

private theorem component_equiv_simple_residual {H : Type*} [Group H] [Finite H]
    [IsSimpleGroup (pResidual 2 H)] (P : Subgroup H) (hP : IsComponent H P) :
    Nonempty (P ≃* pResidual 2 H) := by
  let := hP.2
  have hle := perfect_le_twoResidual P
  have he := subgroupOfEquivOfLe hle
  let : IsSimpleGroup (P ⧸ center P) := IsQuasisimple.simple
  let : Nontrivial P := (QuotientGroup.mk'_surjective (center P)).nontrivial
  let : Nontrivial (P.subgroupOf (pResidual 2 H)) := he.nontrivial
  have ht : P.subgroupOf (pResidual 2 H) = ⊤ := by
    rcases hP.1.subgroupOf.eq_bot_or_top_of_isSimpleGroup
      (inferInstance : IsSimpleGroup (pResidual 2 H)) with hb | ht
    · exact ((nontrivial_iff_ne_bot _).mp inferInstance hb).elim
    · exact ht
  exact ⟨he.symm.trans ((MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv)⟩

private theorem not_six_residual_solvable {H : Type*} [Group H] [Finite H]
    (hs : Group.IsSolvable (pResidual 2 H)) (P : Subgroup H) [Group.IsPerfect P]
    (hSix : Nonempty (P ≃* A6)) : False := by
  obtain ⟨e⟩ := hSix
  let := hs
  let j := (inclusion (perfect_le_twoResidual P)).comp e.symm.toMonoidHom
  exact Group.IsPerfect.not_isSolvable A6
    (Group.isSolvable_of_isSolvable_injective (f := j)
      ((inclusion_injective (perfect_le_twoResidual P)).comp e.symm.injective))

private theorem not_six_residual_linear_three {H : Type*} [Group H] [Finite H]
    {n : ℕ} (hn : 1 ≤ n) (hmodel : ClassicalGroup.IsPSL (pResidual 2 H) 3 (2 ^ n))
    (P : Subgroup H) (hP : IsComponent H P) (hSix : Nonempty (P ≃* A6)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup (pResidual 2 H) := e.isSimpleGroup
  obtain ⟨d⟩ := component_equiv_simple_residual P hP
  obtain ⟨s⟩ := hSix
  exact card_psl_three_ne_six hn hF
    ((Nat.card_congr ((d.trans e).symm.trans s).toEquiv).trans
      alternatingGroup.SixSubgroupObstructions.card_six)

private theorem not_six_residual_linear_two {H : Type*} [Group H] [Finite H]
    {n : ℕ} (hmodel : ClassicalGroup.IsPSL (pResidual 2 H) 2 (2 ^ n))
    (P : Subgroup H) [Group.IsPerfect P] (hSix : Nonempty (P ≃* A6)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  obtain ⟨s⟩ := hSix
  let Q : Sylow 2 PSL(2,F) := default
  obtain ⟨d⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF Q
  let j := e.toMonoidHom.comp ((inclusion (perfect_le_twoResidual P)).comp s.symm.toMonoidHom)
  apply alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute Q
    (fun a b _ _ => ?_) j
    (e.injective.comp ((inclusion_injective (perfect_le_twoResidual P)).comp s.symm.injective))
  exact d.symm.injective (by simp only [map_mul]; exact mul_comm _ _)

private theorem not_six_residual_unitary_three {H : Type*} [Group H] [Finite H]
    {n : ℕ} (hn : 1 ≤ n) (hmodel : ClassicalGroup.IsPSU (pResidual 2 H) 3 (2 ^ n))
    (P : Subgroup H) [Group.IsPerfect P] (hSix : Nonempty (P ≃* A6)) : False := by
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hmodel
  obtain ⟨s⟩ := hSix
  let j := e.toMonoidHom.comp ((inclusion (perfect_le_twoResidual P)).comp s.symm.toMonoidHom)
  exact BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.not_injective_alternating_six
    J (by omega) hF hconj j
    (e.injective.comp ((inclusion_injective (perfect_le_twoResidual P)).comp s.symm.injective))

/-- The genuine possible two-residual models, including every solvable endpoint. -/
@[expose] def LinearResidualModels (H : Type*) [Group H] : Prop :=
  Group.IsSolvable (pResidual 2 H) ∨
    (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL (pResidual 2 H) 3 (2 ^ n)) ∨
    (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSU (pResidual 2 H) 3 (2 ^ n)) ∨
    (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL (pResidual 2 H) 2 (2 ^ n))

/-- Each actual residual model in the linear-three table excludes an A₆ component. -/
theorem not_six_component_of_residual_models {D : Type*} [Group D] [Finite D]
    (a : MulAut D) (hmodels : LinearResidualModels a.fixedSubgroup)
    (S : Subgroup D) (hS : IsComponentIn S a.fixedSubgroup) :
    ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  let P := S.subgroupOf a.fixedSubgroup
  have hP : IsComponent a.fixedSubgroup P := hS.2
  let := hP.2
  have hSix : Nonempty (P ≃* A6) := ⟨(subgroupOfEquivOfLe hS.1).trans e⟩
  rcases hmodels with hs | ⟨n, hn, hm⟩ | ⟨n, hn, hm⟩ | ⟨n, _, hm⟩
  · exact not_six_residual_solvable hs P hSix
  · exact not_six_residual_linear_three hn hm P hP hSix
  · exact not_six_residual_unitary_three hn hm P hSix
  · exact not_six_residual_linear_two hm P hSix

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
