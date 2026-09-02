import Stellmacher.SectionOne.LemmaOneFour
import Stellmacher.SectionOne.LemmaOneFive

open scoped BigOperators Pointwise
open Stellmacher
namespace Stellmacher.SectionOne

universe u

example
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (F : Finset (Subgroup G))
    (hF : ∀ D : Subgroup G, D ∈ F ↔ oneOmega (G := G) (V := V) D)
    (W0 : Subgroup G)
    (hW0 : W0 = ⨆ D : {D : Subgroup G // D ∈ F}, (D : Subgroup G))
    (hW0_le : W0 ≤ pCore 3 G) :
    LemmaOneFourConclusion (G := G) (V := V) W0 F := by
  aesop

example
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (U : Subgroup G) (hU : U ≤ (S : Subgroup G)) :
    LemmaOneFiveConclusion (G := G) (V := V) (S : Subgroup G) U := by
  aesop

example
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S U : Subgroup G) (hU : U ≤ S) :
    subgroupQuotientCard
        (FixedPoints.subgroup U V)
        (FixedPoints.subgroup S V) =
      m (G := G) (V := V) S * (m (G := G) (V := V) U)⁻¹ *
    (indexWithin S U : ℚ) := by
  simp only [subgroupQuotientCard, m, indexWithin]
  have hV : (Nat.card V : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos.ne' : Nat.card V ≠ 0)
  have hFU : (Nat.card (FixedPoints.subgroup U V) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos.ne' : Nat.card (FixedPoints.subgroup U V) ≠ 0)
  have hFS : (Nat.card (FixedPoints.subgroup S V) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos.ne' : Nat.card (FixedPoints.subgroup S V) ≠ 0)
  have hS : (Nat.card S : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos.ne' : Nat.card S ≠ 0)
  have hU' : (Nat.card U : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos.ne' : Nat.card U ≠ 0)
  have hidx_nat : Nat.card (U.subgroupOf S) * (U.subgroupOf S).index = Nat.card S :=
    Subgroup.card_mul_index (U.subgroupOf S)
  rw [natCard_subgroupOf_eq U S hU] at hidx_nat
  have hidx : (Nat.card U : ℚ) * (U.subgroupOf S).index = Nat.card S := by
    exact_mod_cast hidx_nat
  field_simp [hV, hFU, hFS, hS, hU']
  nlinarith [hidx]

end Stellmacher.SectionOne
