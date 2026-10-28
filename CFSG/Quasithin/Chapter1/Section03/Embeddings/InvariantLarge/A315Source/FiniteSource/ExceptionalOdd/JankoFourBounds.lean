module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.ProductCore
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Source.ElementaryClosure
public import Theory.GroupTheory.ElementaryEightSolvableMinimal.SevenFree
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.CentralizerSylow

/-!
# The original eleven-pair closure in Janko four

The actual product is solvable with nontrivial two-core, and its order is
prime to seven. The canonical minimal normal elementary closure cannot have
order eight. The checked max1 and max2 orders, and the actual max4 two-core
quotient, exclude a factor of 121 in all three possible local overgroups.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511; GLS3 Table 5.3i.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
open Janko4 Janko4.OuterReduction.OddIndex
open Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open InvariantThree.SporadicActions.J4Reduction.Source
attribute [local irreducible] Janko4.modelGroup matrixA matrixB

theorem j4_max1_not_eleven_square :
    ¬ 121 ∣ Nat.card (Janko4.Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four) := by
  rw [Janko4.Cardinality.max1Subgroup_card]
  norm_num

theorem j4_max2_not_eleven_square : ¬ 121 ∣ Nat.card sourceSubgroup := by
  rw [card_sourceSubgroup_eq_localSubgroup, localSubgroup_eq_top, card_top, centralizer_card]
  norm_num

theorem j4_max4_not_eleven_square : ¬ 121 ∣ Nat.card max4Subgroup := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := max4Subgroup)).exists_card_eq
  have hcop : Nat.Coprime 121 (Nat.card (pCore 2 max4Subgroup)) := by
    rw [hn]
    exact (by decide : Nat.Coprime 121 2).pow_right n
  intro hd
  have hc := (pCore 2 max4Subgroup).card_mul_index
  rw [← hc] at hd
  have hh : 121 ∣ Nat.card (max4Subgroup ⧸ pCore 2 max4Subgroup) := hcop.dvd_of_dvd_mul_left hd
  rw [Nat.card_congr max4QuotientEquiv.toEquiv, quotientModel_card] at hh
  norm_num at hh

theorem j4_eleven_product_twoCore (B : Subgroup Model) (S : Sylow 2 Model)
    (hB : XiOddQuotient 11 B)
    (hperm : (B : Set Model) * (S : Set Model) = (S : Set Model) * (B : Set Model)) :
    pCore 2 (B ⊔ (S : Subgroup Model) : Subgroup Model) ≠ ⊥ := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply product_twoCore_ne_bot_of_exceptional_prime (Or.inr (Or.inr rfl)) B S hB S.isPGroup' hperm
  rw [ambient_sylow_card]
  norm_num

theorem j4_eleven_product_seven_free (B : Subgroup Model) (S : Sylow 2 Model)
    (hB : XiOddQuotient 11 B)
    (hperm : (B : Set Model) * (S : Set Model) = (S : Set Model) * (B : Set Model)) :
    ¬ 7 ∣ Nat.card (B ⊔ (S : Subgroup Model) : Subgroup Model) := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hd := IsPGroup.disjoint_of_ne 11 2 (by decide) B (S : Subgroup Model) hB.isPGroup S.isPGroup'
  have hc := card_set_mul_mul_card_inf B (S : Subgroup Model)
  rw [hd.eq_bot, card_bot, mul_one, ← coe_sup_of_set_mul_comm B (S : Subgroup Model) hperm] at hc
  change Nat.card (B ⊔ (S : Subgroup Model) : Subgroup Model) = Nat.card B * Nat.card S at hc
  rw [hc, ambient_sylow_card]
  rcases hB with ⟨_,hcB⟩ | ⟨_,hcB,_⟩ <;> rw [hcB] <;> norm_num

theorem j4_eleven_closure_card_ne_eight (B : Subgroup Model) (S : Sylow 2 Model)
    (hB : XiOddQuotient 11 B)
    (hperm : (B : Set Model) * (S : Set Model) = (S : Set Model) * (B : Set Model)) :
    Nat.card (elementaryClosure S (B ⊔ S.toSubgroup) le_sup_right) ≠ 8 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  intro he
  let H := B ⊔ S.toSubgroup
  let E := centralClosure S H le_sup_right
  let _ := centralClosure_elementary_of_twoCore_ne_bot S H le_sup_right
    (j4_eleven_product_twoCore B S hB hperm)
  have hc : Nat.card E = 8 := (card_map_of_injective H.subtype_injective).symm.trans he
  exact not_minimal_normal_elementary_eight_of_solvable_seven_free E hc
    (solvable_product B S hB.isPGroup S.isPGroup' (by decide) hperm)
    (j4_eleven_product_seven_free B S hB hperm) (by
      intro C hCE hCn
      let _ := hCn
      exact centralClosure_minimal S H le_sup_right C hCE)
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
