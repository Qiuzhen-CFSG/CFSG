module

public import CFSG.Quasithin.Chapter12.Section08.RankTwo
public import CFSG.Quasithin.Chapter12.Section08.Setup.NaturalActions

/-!
# Placement and normalizers of the actual rank-two seed

The seed is the normal conjugate span of Ω₁(Z(T)) in M. Its already proved
elementarity puts it in O₂(M), and hence in the fixed Sylow subgroup T.
Uniqueness over LT then controls its full normalizer and centralizer.
The literal LT action kernel is the given O₂(LT), with no Chapter 12.2 input.

This is the base for the separate S₃/C₃ action construction in dimension two.
No full natural action of L, flag or escape conclusion is assumed here.
Source: Aschbacher–Smith, Hypothesis 12.8.1(2) and Notation 12.8.2, p.849.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.RankTwoHypothesis
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L M : Subgroup G}
variable (h : RankTwoHypothesis K T L M)
include h

theorem seed_le_M : rankTwoSeed T M ≤ M :=
  conjugateSpanBy_le_self ((sylowOmega_le T).trans h.sylow_le)

omit h [Finite G] in
theorem M_normalizes_seed : M ≤ normalizer (rankTwoSeed T M : Set G) :=
  le_normalizer_conjugateSpanBy _ _

theorem seed_le_sylow : rankTwoSeed T M ≤ (T : Subgroup G) := by
  let := rankTwoSeed_elementary h
  have hcore : rankTwoSeed T M ≤ M.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _) h.seed_le_M M_normalizes_seed
  apply hcore.trans
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le h.sylow_le] using
    pCoreIn_le_sylow M (T.subtype h.sylow_le)

theorem L_normalizes_seed : L ≤ normalizer (rankTwoSeed T M : Set G) :=
  h.L_le.trans M_normalizes_seed

theorem sylow_normalizes_L : (T : Subgroup G) ≤ normalizer (L : Set G) :=
  h.sylow_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)

theorem seed_normalizer_le : normalizer (rankTwoSeed T M : Set G) ≤ M := by
  let := rankTwoSeed_elementary h
  apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
  · intro N hN hJN
    exact Set.mem_singleton_iff.mp (h.unique ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN, hJN⟩)
  · exact IsElementaryAbelian.isPGroup 2 _
  · intro he
    have hc := rankTwoSeed_card h
    rw [he, Subgroup.card_bot] at hc
    norm_num at hc
  · exact (sup_le h.L_le h.sylow_le).trans M_normalizes_seed

theorem seed_centralizer_le : Subgroup.centralizer (rankTwoSeed T M : Set G) ≤ M :=
  (Subgroup.centralizer_le_normalizer _).trans h.seed_normalizer_le

omit h [Finite G] in
theorem seedNormalizer_eq : seedNormalizer M (rankTwoSeed T M) = M :=
  inf_eq_left.mpr M_normalizes_seed

/-- The intrinsic kernel agrees with the original quotient denominator. -/
theorem literal_action_kernel :
    (setupSeedAction (L ⊔ (T : Subgroup G)) (rankTwoSeed T M)
      ((sup_le h.L_le h.sylow_le).trans M_normalizes_seed)).ker =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  apply map_injective (L ⊔ (T : Subgroup G)).subtype_injective
  rw [setupSeedAction_ker, subgroupOf_map_subtype, inf_comm]
  exact h.centralizer

/-- The existing flag action has exactly the source S₃ quotient denominator. -/
theorem binarySeedAction_kernel (F : InvariantFlag T (rankTwoSeed T M) 2) :
    (F.binarySeedAction L h.L_normalizes_seed).ker =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  apply map_injective (L ⊔ (T : Subgroup G)).subtype_injective
  rw [F.binarySeedAction_ker, subgroupOf_map_subtype, inf_comm]
  exact h.centralizer

end CFSG.Quasithin.Chapter12.Section08.RankTwoHypothesis
