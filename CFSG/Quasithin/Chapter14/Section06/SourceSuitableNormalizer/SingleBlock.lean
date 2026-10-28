module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# The symmetric-three quotient from one normal A₃ block

A normal A₃ block is the concrete A₄ group. It meets a Sylow two-subgroup
in a four-group, so their generating join gives Sylow index three. When
the Sylow subgroup properly contains the two-core, the existing faithful
three-coset action identifies the quotient with S₃.

This is the single-block endpoint of Aschbacher--Smith 14.6.3(4), printed
pp.1021--1022. The actual normalizer assembly obtains the normal block
from C.1.29 and excludes a normal Sylow subgroup using characteristic
normalizer control. No quotient classification is taken as a premise.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.SourceSuitableNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- One normal A₃ block and the original Sylow generate an S₃ quotient. -/
theorem quotient_equiv_perm_three_of_normal_alternatingThree
    (S : Sylow 2 G) (K : Subgroup G) [K.Normal]
    (hK : ChapterC.IsAlternatingBlock K 3) (hgen : K ⊔ (S : Subgroup G) = ⊤)
    (hSnoncore : ¬ (S : Subgroup G) ≤ pCore 2 G) :
    Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := hK.equiv_alternatingFour
  have hKcard : Nat.card K = 12 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal K
  have hPcard : Nat.card P = 4 := by
    rw [P.card_eq_multiplicity, hKcard]
    decide +kernel
  have hinter : Nat.card (K ⊓ (S : Subgroup G) : Subgroup G) = 4 := by
    have hm := card_map_of_injective (K := (S : Subgroup G).subgroupOf K)
      K.subtype_injective
    rw [subgroupOf_map_subtype, inf_comm, ← hP] at hm
    exact hm.trans hPcard
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes K (S : Subgroup G)
    (by rw [K.normalizer_eq_top]; exact le_top)
  rw [hKcard, hinter, hgen, card_top] at hprod
  have hScard : 0 < Nat.card S := Nat.card_pos
  have hi : (S : Subgroup G).index = 3 := by
    have hm := (S : Subgroup G).card_mul_index
    nlinarith
  exact sylow_index_three_core_quotient S hi
    (lt_of_le_not_ge (pCore_isPGroup.le_sylow_of_normal S) hSnoncore)
end CFSG.Quasithin.Chapter14.Section06.SourceSuitableNormalizer
