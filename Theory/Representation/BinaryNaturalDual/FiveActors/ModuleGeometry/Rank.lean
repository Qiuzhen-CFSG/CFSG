module

public import Theory.Representation.BinaryNaturalDual.FiveActors.OuterConjugacy
public import Theory.SpecificGroups.SymmetricFourSylow
public import Theory.GroupTheory.PrimeRankAutomorphismOrder
/-!
# Sharp two-rank exclusion for degree-five outer actors

A nonabelian Sylow subgroup of S₄ embeds in a Sylow subgroup of S₆. The
latter has order sixteen, so its elementary subgroups have rank at most
three. The inner kernel of an elementary outer actor embeds in its actual
S₆ centralizer, and the cyclic outer quotient adds at most one.

Source: Aschbacher–Smith, H.9.2(2), printed p.390 (PDF p.401).
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.FiveActors.ModuleGeometry

theorem symmetric_six_rank_le_three : primeRank 2 (Equiv.Perm (Fin 6)) ≤ 3 := by
  let P : Sylow 2 (Equiv.Perm (Fin 4)) := Classical.choice inferInstance
  let f : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 6) :=
    Equiv.Perm.viaEmbeddingHom ⟨Fin.castAdd 2, Fin.castAdd_injective 4 2⟩
  have hf : Function.Injective f := Equiv.Perm.viaEmbeddingHom_injective _
  obtain ⟨Q, hQ⟩ := (P.isPGroup'.map f).exists_le_sylow
  let j : P →* Q := (f.comp (P : Subgroup _).subtype).codRestrict Q
    (fun x => hQ ⟨x, x.property, rfl⟩)
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  have hc : Nat.card Q = 2 ^ (3 + 1) := by
    rw [Q.card_eq_multiplicity, Nat.card_perm, Nat.card_fin]
    decide +kernel
  rw [Q.primeRank_eq]
  apply primeRank_le_of_noncommutative_card_prime_pow hc
  intro hcomm
  let := hcomm
  obtain ⟨e⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four P
  apply DihedralGroup.not_commutative (n := 4) (by decide) (by decide)
  exact IsMulCommutative.of_comm fun x y => by
    apply e.symm.injective
    apply hj
    simp only [map_mul]
    exact mul_comm _ _

theorem outer_elementary_kernel_rank_le_three
    (A : Subgroup M) [IsElementaryAbelian 2 A]
    (t : M) (htA : t ∈ A) (hout : t ∉ L) :
    primeRank 2 ((QuotientGroup.mk' L).comp A.subtype).ker ≤ 3 := by
  let f := (QuotientGroup.mk' L).comp A.subtype
  let j : f.ker →* innerCentralizer t :=
    { toFun := fun x => ⟨x.1.1, (QuotientGroup.eq_one_iff _).mp x.property,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mul_comm x.1 (⟨t, htA⟩ : A)))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    have he : x.1.1 = y.1.1 := congrArg (fun z : innerCentralizer t => (z : M)) h
    exact Subtype.ext (Subtype.ext he)
  obtain ⟨e⟩ := innerCentralizer_equiv_six t
    (elemPow_eq_one_of_isElementaryAbelian t htA) hout
  have hc : primeRank 2 (innerCentralizer t) ≤ 3 := by
    rw [primeRank_equiv 2 e]
    exact symmetric_six_rank_le_three
  exact (primeRank_le_of_injective 2 j hj).trans hc

theorem outer_elementary_rank_le_four (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hA : ¬ A ≤ L) : primeRank 2 A ≤ 4 := by
  obtain ⟨t, htA, hout⟩ := SetLike.not_le_iff_exists.mp hA
  have hk := outer_elementary_kernel_rank_le_three A t htA hout
  let : IsCyclic (MulAut.Outer G) := linear_outer_isCyclic (Or.inr rfl)
  have ho : primeRank 2 (MulAut.Outer G) ≤ 1 := by
    let P : Sylow 2 (MulAut.Outer G) := Classical.choice inferInstance
    exact P.primeRank_le_one_of_isCyclic inferInstance
  exact (primeRank_le_ker_add (p := 2) ((QuotientGroup.mk' L).comp A.subtype)).trans
    (Nat.add_le_add hk ho)

theorem high_rank_inner (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hr : 5 ≤ primeRank 2 A) : A ≤ L := by
  by_contra h
  have := outer_elementary_rank_le_four A h
  omega
end BinaryNaturalDual.FiveActors.ModuleGeometry
