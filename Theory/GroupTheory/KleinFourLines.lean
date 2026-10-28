module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The three lines of a four-group

If two order-two subgroups generate a group and a third order-two subgroup
is disjoint from both, the product of their nonidentity elements generates
the third subgroup. Normalization identifies the join with the subgroup
product; uniqueness of each nonidentity element determines its factors.

This supplies the original identity Z=⟨e₁e₂⟩ from the factor fixed lines
in Aschbacher–Smith 13.2.11(3), printed p.881. The source consumer keeps
the literal offender factors and Sylow flag.
-/

public section

open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

theorem exists_generator_of_card_two (A : Subgroup G) (hA : Nat.card A = 2) :
    ∃ a : G, a ∈ A ∧ a ≠ 1 ∧ zpowers a = A := by
  obtain ⟨a,ha,hu⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  refine ⟨a,a.property,(fun he => ha (Subtype.ext he)),le_antisymm
    (zpowers_le.mpr a.property) ?_⟩
  intro x hx
  by_cases he : x = 1
  · simpa only [he] using (zpowers (a : G)).one_mem
  · have hxa : (⟨x,hx⟩ : A) = a := hu _ (fun h => he (congrArg Subtype.val h))
    rw [show x = a from congrArg Subtype.val hxa]
    exact mem_zpowers _

theorem zpowers_mul_eq_third_line (A B Z : Subgroup G)
    (hA : Nat.card A = 2) (hB : Nat.card B = 2) (hZ : Nat.card Z = 2)
    (hZA : Disjoint A Z) (hZB : Disjoint B Z) (hZle : Z ≤ A ⊔ B)
    (hn : B ≤ normalizer (A : Set G)) (a b : G)
    (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ B) (hb1 : b ≠ 1) :
    zpowers (a * b) = Z := by
  obtain ⟨z,hz,hz1,hzg⟩ := exists_generator_of_card_two Z hZ
  have hm : z ∈ (A : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hn]
    exact hZle hz
  obtain ⟨x,hx,y,hy,hxy⟩ := hm
  have hx1 : x ≠ 1 := by
    intro he
    have hyz : y = z := by simpa only [he,one_mul] using hxy
    exact hz1 (Subgroup.disjoint_def.mp hZB (hyz ▸ hy) hz)
  have hy1 : y ≠ 1 := by
    intro he
    have hxz : x = z := by simpa only [he,mul_one] using hxy
    exact hz1 (Subgroup.disjoint_def.mp hZA (hxz ▸ hx) hz)
  have hxa : x = a := congrArg Subtype.val (((Nat.card_eq_two_iff' (1 : A)).mp hA).unique
    (show (⟨x,hx⟩ : A) ≠ 1 from fun he => hx1 (congrArg Subtype.val he))
    (show (⟨a,ha⟩ : A) ≠ 1 from fun he => ha1 (congrArg Subtype.val he)))
  have hyb : y = b := congrArg Subtype.val (((Nat.card_eq_two_iff' (1 : B)).mp hB).unique
    (show (⟨y,hy⟩ : B) ≠ 1 from fun he => hy1 (congrArg Subtype.val he))
    (show (⟨b,hb⟩ : B) ≠ 1 from fun he => hb1 (congrArg Subtype.val he)))
  rwa [← hxy,hxa,hyb] at hzg
end Subgroup
