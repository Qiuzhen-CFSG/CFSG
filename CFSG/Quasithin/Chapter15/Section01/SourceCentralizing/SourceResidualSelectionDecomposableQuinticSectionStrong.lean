module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionOffender
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex

/-!
# Strong offenders from the actual section-kernel index

The original centralizer index bounds the fixed quotient order of the
literal section. A strict comparison with the actual actor image order
therefore gives a strong offender on that same faithful action image.
No replacement of the original actor or section kernel is used.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
variable {G : Type*} [Group G] [Finite G]

/-- Strict kernel-index comparison constructs a strong offender on the
faithful image of the original binary section. -/
theorem exists_faithful_section_strong_offender_of_kernel_index
    (H F U A : Subgroup G) [IsElementaryAbelian 2 F] [IsElementaryAbelian 2 A]
    (hFH : F ≤ H) (hUF : U ≤ F)
    (hnF : H ≤ normalizer (F : Set G)) (hnU : H ≤ normalizer (U : Set G))
    (hAH : A ≤ H)
    (hi : (centralizer (A : Set G)).relIndex F <
      (commutatorPreimage H F U).relIndex A) :
    ∃ ρ : Representation (ZMod 2) H (Additive (F ⧸ U.subgroupOf F)),
      Nonempty (BinaryConjugationSection H F U ρ) ∧
      Function.Injective (imageRepresentation ρ) ∧
      (actionHom ρ).ker.map H.subtype = commutatorPreimage H F U ∧
      Nat.card (actionSubgroup ρ (A.subgroupOf H)) =
        (commutatorPreimage H F U).relIndex A ∧
      IsStrongOffender (imageRepresentation ρ) (actionSubgroup ρ (A.subgroupOf H)) := by
  have hpos : 0 < (centralizer (A : Set G)).relIndex F :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  obtain ⟨ρ, ⟨d⟩, hfaith, hker, hcard, hoff⟩ :=
    exists_faithful_section_offender_of_kernel_index H F U A hFH hUF hnF hnU hAH
      (lt_of_le_of_lt hpos hi) hi.le
  refine ⟨ρ, ⟨d⟩, hfaith, hker, hcard, hoff.1, ?_⟩
  have hb := d.fixed_quotient_card_le_centralizer_index
    (imageRepresentation ρ) (actionHom ρ) A
  have hs : Nat.card ((Additive (F ⧸ U.subgroupOf F)) ⧸
      fixedSpace (imageRepresentation ρ) (actionSubgroup ρ (A.subgroupOf H))) <
      Nat.card (actionSubgroup ρ (A.subgroupOf H)) := by
    rw [hcard]
    exact hb.trans_lt hi
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    hoff.1.card_eq_two_pow_rank] at hs
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hs

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
