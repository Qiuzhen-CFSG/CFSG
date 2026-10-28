module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.SylowGeneration
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Centralizer


/-!
# Orders of faithful small factor actions

The actual offender product fixes each of its own factors by conjugation.
When its centralizer is trivial, it is exactly the kernel of the ambient
factor-permutation map. A full permutation image therefore gives the
literal ambient order 6^r r!, using the supplied internal factor product.

Source: the one- and two-factor action calculation in Aschbacher–Smith
14.1.7, printed p.977.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

theorem offenderSubgroup_le_factorConjugation_ker : offenderSubgroup ρ ≤ d.factorConjugation.ker := by
  intro k hk
  apply Equiv.ext
  intro i
  apply d.factor_injective
  have hkn : k ∈ normalizer (d.factor i : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer (d.factor_le_offenderSubgroup i)).mp
      (d.factor_normal_in_offenderSubgroup i)) hk
  exact (d.factor_map_conj k i).symm.trans
    (mem_normalizer_iff_map_conj_eq.mp hkn)

theorem factorConjugation_ker_eq_of_centralizer_eq_bot
    (hc : centralizer (offenderSubgroup ρ : Set G) = ⊥) :
    d.factorConjugation.ker = offenderSubgroup ρ := by
  apply le_antisymm ?_ d.offenderSubgroup_le_factorConjugation_ker
  simpa only [hc, sup_bot_eq] using d.factorConjugation_kernel_le

include d in
theorem offenderSubgroup_card : Nat.card (offenderSubgroup ρ) = 6 ^ d.count := by
  classical
  obtain ⟨eS⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  have hi (i : Fin d.count) : Nat.card (d.factor i) = 6 := by
    rw [Nat.card_congr ((d.factorModel i).trans eS).toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  rw [← Nat.card_congr d.groupProduct.toEquiv, Nat.card_pi]
  simp only [hi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_of_full_factorConjugation [Finite G]
    (hc : centralizer (offenderSubgroup ρ : Set G) = ⊥)
    (hs : Function.Surjective d.factorConjugation) :
    Nat.card G = 6 ^ d.count * d.count.factorial := by
  have hk := d.factorConjugation_ker_eq_of_centralizer_eq_bot hc
  have hi : (offenderSubgroup ρ).index = d.count.factorial := by
    rw [← hk, Subgroup.index_eq_card]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective d.factorConjugation hs).toEquiv,
      Nat.card_perm, Nat.card_fin]
  rw [← (offenderSubgroup ρ).card_mul_index, d.offenderSubgroup_card, hi]

end CFSG.Quasithin.ChapterB.SolvableFFFactors
