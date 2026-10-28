module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddParity
public import Theory.Representation.BinaryPermutation.FivePairWreath
public import Theory.Representation.BinaryOffender.ProductSplitting
public import Theory.Representation.BinaryOffender.GeneratedCore
-- Internal coordinate transport: unfold only the existing literal base equivalence.
import all Theory.SpecificGroups.SymmetricFive.WreathComponents
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.FivePairOverlap

/-!
# A pure-coordinate transposition in the paired natural offender

Restrict the actual offender to the literal wreath base and transport it
through the original base equivalence. The product splitting theorem
makes it the product of its coordinate projections. A nontrivial coordinate
is an offender on the five-letter core, hence contains an odd involution,
which is a transposition. All maps retain the original wreath coordinates.
Source: Aschbacher--Smith B.3.2(4), B.6.9 and 3.1.9(6), pp.83,115--116,578.
The literal source application is M22CodeSolvable.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Theory.SpecificGroups.SymmetricFive.WreathComponents
open MathieuCode.NormalizedShadowRows.FivePairOverlap
open BinaryPermutation

private theorem core_offender_swap (A : Subgroup Sym)
    (hA : IsOffender (coreRepresentation (Fin 5)) A) :
    ∃ a ∈ A, a.IsSwap := by
  have hout := ChapterB.Offenders.core_offender_not_le_alternating (Or.inl rfl) hA
  obtain ⟨a,ha,hao⟩ := Set.not_subset.mp hout
  let := hA.1.2
  have hne : a ≠ 1 := fun he => hao (he ▸ one_mem _)
  exact ⟨a,ha,Equiv.Perm.five_isSwap_of_outer_involution a
    (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) hne) hao⟩

/-- An offender in the literal wreath base contains a pure-coordinate transposition. -/
theorem paired_base_offender_swap (A : Subgroup W)
    (hA : IsOffender FivePair.wreathRepresentation A) (hbase : A ≤ base) :
    ∃ (i : C2) (a : Sym), axis i a ∈ A ∧ a.IsSwap := by
  let e := baseEquiv.symm
  let C := (A.subgroupOf base).map e.toMonoidHom
  have heb (g : base) : baseHom (e g) = (g : W) :=
    congrArg Subtype.val (baseEquiv.apply_symm_apply g)
  have hC : IsOffender FivePair.action C := by
    apply (hA.subgroupOf _ hbase).map_equivariant _ _ e.toMonoidHom e.injective
      (LinearEquiv.refl _ _)
    intro g v
    change FivePair.wreathRepresentation (g : W) v = FivePair.action (e g) v
    rw [←heb g]
    exact FivePair.wreathToLinear_base _ _
  have hCA : C.map baseHom = A := by
    change ((A.subgroupOf base).map e.toMonoidHom).map baseHom = A
    rw [map_map]
    have he : baseHom.comp e.toMonoidHom = base.subtype := MonoidHom.ext heb
    rw [he,map_subgroupOf_eq_of_le hbase]
  have hn : ¬ IsStrongFFModule (coreRepresentation (Fin 5)) :=
    fun ⟨E,hE⟩ => ChapterB.Offenders.Odd.not_isStrongOffender_core (Or.inl rfl) E hE
  obtain ⟨hsplit,h₁,h₂⟩ := offender_product_of_not_strong _ _ hn hn hC
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · exact (hC.1.1 (by rw [hsplit,h₁,h₂,bot_prod_bot])).elim
    · obtain ⟨a,ha,hs⟩ := core_offender_swap _ h₂
      refine ⟨swap,a,?_,hs⟩
      have hc : (1,a) ∈ C := hsplit.ge ⟨one_mem _,ha⟩
      have hm := mem_map_of_mem baseHom hc
      rw [hCA] at hm
      have he : axis swap a = baseHom (1,a) := by
        apply RegularWreathProduct.ext
        · funext i
          rcases index_cases i with rfl | rfl <;> simp [axis_apply,baseHom_apply,swap_ne_one]
        · rfl
      simpa only [he] using hm
  · obtain ⟨a,ha,hs⟩ := core_offender_swap _ h₁
    refine ⟨1,a,?_,hs⟩
    have hc : (a,1) ∈ C := hsplit.ge ⟨ha,one_mem _⟩
    have hm := mem_map_of_mem baseHom hc
    rw [hCA] at hm
    have he : axis 1 a = baseHom (a,1) := by
      apply RegularWreathProduct.ext
      · funext i
        rcases index_cases i with rfl | rfl <;> simp [axis_apply,baseHom_apply,swap_ne_one]
      · rfl
    simpa only [he] using hm
end CFSG.Quasithin.Chapter8.MathieuShadowRows
