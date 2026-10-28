module
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.QuasithinBasic
public import Mathlib.Data.Nat.Log
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Elementary images in the prime-to-three quotient

For a Goldschmidt triple, F.6.11 identifies the intersection of either
local group with O₃′(G) as O₂(G). Thus the actual image of an elementary
subgroup has precisely the relative order needed for its rank bound.
An image of rank at least four also excludes the collapsed S₃ quotient.

Source: Aschbacher--Smith, F.6.11, printed pp.306--307; the application
is the normal elementary subgroup in original 14.6.10(4), p.1028.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G]

/-- F.6.11 identifies the two quotient kernels on every subgroup of either
source parabolic. -/
theorem goldschmidt_elementary_quotient_card {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (U : Subgroup G) (hUB : U ≤ B) :
    Nat.card (U.map (QuotientGroup.mk' (pPrimeCore 3 G))) = (pCore 2 G).relIndex U := by
  let q := QuotientGroup.mk' (pPrimeCore 3 G)
  have he : (pPrimeCore 3 G).subgroupOf U = (pCore 2 G).subgroupOf U := by
    ext x
    change (x:G) ∈ pPrimeCore 3 G ↔ (x:G) ∈ pCore 2 G
    rw [←h.right_inf_primeToThreeCore]
    exact (and_iff_right (hUB x.property)).symm
  rw [←relIndex_ker U q,QuotientGroup.ker_mk']
  exact congrArg Subgroup.index he

omit [Finite G] in
/-- Normality is transported inside the literal image of the same parabolic. -/
theorem goldschmidt_elementary_quotient_normal {B : Subgroup G}
    (U : Subgroup G) (hUB : U ≤ B) (hn : (U.subgroupOf B).Normal) :
    let q := QuotientGroup.mk' (pPrimeCore 3 G)
    ((U.map q).subgroupOf (B.map q)).Normal := by
  let q := QuotientGroup.mk' (pPrimeCore 3 G)
  apply normal_subgroupOf_of_le_normalizer
  exact (map_mono ((normal_subgroupOf_iff_le_normalizer hUB).mp hn)).trans
    (le_normalizer_map q)

/-- The lower bound records the actual elementary image, not merely the rank
of its ambient quotient. -/
theorem goldschmidt_elementary_quotient_rank {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (U : Subgroup G) (hUB : U ≤ B)
    [IsElementaryAbelian 2 U] :
    Nat.log 2 ((pCore 2 G).relIndex U) ≤
      primeRank 2 (U.map (QuotientGroup.mk' (pPrimeCore 3 G))) := by
  let E := U.map (QuotientGroup.mk' (pPrimeCore 3 G))
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  rw [←goldschmidt_elementary_quotient_card h U hUB]
  change Nat.log 2 (Nat.card E) ≤ primeRank 2 E
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  rw [hn,Nat.log_pow (by decide)]
  let : IsElementaryAbelian 2 (⊤ : Subgroup E) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup E).subtype (subtype_injective _)
  exact IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup E) (by simpa using hn)

/-- A rank-four elementary image excludes the collapsed symmetric-three
case of F.6.11, so the literal quotient images form a Goldschmidt triple. -/
theorem goldschmidt_quotient_triple_of_elementary_rank {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B)
    (E : Subgroup (G ⧸ pPrimeCore 3 G)) (hr : 4 ≤ primeRank 2 E) :
    IsGoldschmidtTriple
      (A.map (QuotientGroup.mk' (pPrimeCore 3 G)))
      (B.map (QuotientGroup.mk' (pPrimeCore 3 G))) := by
  rcases h.primeToThreeCore_dichotomy with good | bad
  · exact good.2.1
  obtain ⟨e⟩ := bad.2.2.1
  have hcard : Nat.card (G ⧸ pPrimeCore 3 G) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hbound : primeRank 2 (G ⧸ pPrimeCore 3 G) ≤ 3 := by
    apply (primeRank_le_iff_elementary_card_le _).mpr
    intro F hF
    have hc := Nat.card_le_card_of_injective F.subtype F.subtype_injective
    rw [hcard] at hc
    omega
  have he := Theory.GroupTheory.primeRank_le_of_injective 2 E.subtype E.subtype_injective
  exact (by omega : False).elim

end CFSG.Quasithin.ChapterF
