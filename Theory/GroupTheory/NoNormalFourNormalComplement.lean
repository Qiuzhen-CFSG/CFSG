module

public import Theory.GroupTheory.PGroup.NoNormalFourIndex
public import BenderSuzuki.External.Huppert.XI.NormalComplement

/-!
# A normal two-complement from the absence of normal four-groups

A noncyclic Sylow two-subgroup without a normal elementary four-group has
a cyclic normal self-centralizing subgroup of index two. Thus it is
metacyclic, as is each of its subgroups. Conjugating any ambient two-subgroup
into this Sylow subgroup proves that it needs at most two generators.

The rank-two normal-complement theorem then applies when three does not
divide the ambient order. Its proof uses the Frattini quotient, of order at
most four, to rule out coprime automorphisms in a minimal counterexample.
The resulting complement is an actual normal subgroup of odd order with
two-group quotient.

Source: GLS, Volume 4, Chapter 1, Lemma 3.10,
`refs/KGroup/GLS4/Chapter1.tex`, lines 450–456. The source invokes Frobenius's
criterion; here the proved rank-two form of Huppert IV.5.11 gives the same
normal-complement consequence without a separate classification of all
subgroup automizers.
-/

open Subgroup BenderSuzuki.External
open scoped Pointwise

namespace Sylow

/-- The normal-complement branch of GLS4, Lemma 3.10. Normality of the
excluded four-group is relative to the given Sylow subgroup. -/
public theorem hasNormalTwoComplement_of_no_normal_four
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hnoncyclic : ¬ IsCyclic S) (hthree : ¬ 3 ∣ Nat.card G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4) :
    HasNormalPComplement 2 G := by
  obtain ⟨A, hAn, hAc, hC⟩ :=
    S.isPGroup'.exists_cyclic_normal_selfCentralizing_of_no_normal_four hno
  let : A.Normal := hAn
  let : IsCyclic A := hAc
  have hproper : A ≠ ⊤ := by
    intro htop
    have htopcyclic : IsCyclic (⊤ : Subgroup S) := htop ▸ hAc
    exact hnoncyclic (Subgroup.topEquiv.isCyclic.mp htopcyclic)
  have hindex : A.index = 2 := by
    have hlo := A.one_lt_index_of_ne_top hproper
    have hhi := S.isPGroup'.index_le_two_of_cyclic_normal_selfCentralizing_of_no_normal_four
      hno A hC.le
    omega
  have hmeta : IsMetacyclic S :=
    ⟨A, hAn, hAc, isCyclic_of_prime_card (A.index_eq_card ▸ hindex)⟩
  apply huppert_IV_5_11_hasNormalPComplement_of_rankTwo_twoSubgroups hthree
  intro U hU
  obtain ⟨Q, hUQ⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  let c : G ≃* G := MulAut.conj g
  let Uc : Subgroup G := U.map c.toMonoidHom
  have hQmap : (Q : Subgroup G).map c.toMonoidHom = (S : Subgroup G) := by
    calc
      (Q : Subgroup G).map c.toMonoidHom =
          (MulAut.conj g • (Q : Subgroup G) : Subgroup G) := rfl
      _ = ((g • Q : Sylow 2 G) : Subgroup G) := by
        rw [← Sylow.coe_subgroup_smul]
      _ = (S : Subgroup G) := by rw [hg]
  have hUcS : Uc ≤ (S : Subgroup G) := by
    rw [← hQmap]
    exact Subgroup.map_mono hUQ
  let US : Subgroup S := Uc.subgroupOf S
  have hrank : generatorRank US ≤ 2 :=
    huppert_IV_5_10_generatorRank_le_two_of_isMetacyclic
      (huppert_IV_5_10_isMetacyclic_subgroup US hmeta)
  let e : U ≃* US :=
    (Subgroup.equivMapOfInjective (f := c.toMonoidHom) U c.injective).trans
      (Subgroup.subgroupOfEquivOfLe hUcS).symm
  rw [generatorRank_eq_group_rank] at hrank ⊢
  exact (Group.rank_congr e).trans_le hrank

end Sylow
