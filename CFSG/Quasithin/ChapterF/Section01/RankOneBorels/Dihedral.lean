module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.QuotientGeometry
public import Theory.GroupTheory.SpecificGroups.OddDihedralTwoNormalizer

/-!
# The order-ten alternative in F.1.3(1)

Source: Aschbacher–Smith, printed pp.259–260, where the dihedral group of
order ten is regarded as a truncated Suzuki group. Its Sylow two-subgroup
has order two and index five. The odd-dihedral normalizer theorem makes
it self-normalizing; prime index gives the unique proper-overgroup assertion.
The Cartan complement is trivial. All conclusions transport along an actual
multiplicative equivalence, not merely a group-family label.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.Source

/-- Every Sylow two-subgroup in a concrete order-ten dihedral model satisfies
all the intrinsic rank-one Borel conclusions, including the odd complement. -/
theorem rankOneSylowFacts_of_dihedral_equiv {H : Type*} [Group H]
    (e : H ≃* DihedralGroup 5) (T : Sylow 2 H) : RankOneSylowFacts T := by
  let : Finite H := Finite.of_injective e e.injective
  have hcard : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    rw [Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization, Nat.prime_five.factorization]
    norm_num
  have hindex : (T : Subgroup H).index = 5 := by
    have h := (T : Subgroup H).card_mul_index
    rw [show Nat.card (T : Subgroup H) = 2 from hcard,
      Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h
    omega
  have hne : (T : Subgroup H) ≠ ⊥ :=
    fun hh => by simp [hh] at hcard
  have hnorm : Subgroup.normalizer (T : Set H) =
      (T : Subgroup H) :=
    odd_dihedral_two_subgroup_normalizer 5 (by decide) e
      (T : Subgroup H) T.isPGroup' hne
  refine ⟨?_, ?_, twoCore_sylow_normalizer T, ?_, ?_⟩
  · rw [hnorm]
    apply lt_top_iff_ne_top.mpr
    intro heq
    simp [heq] at hindex
  · intro M hTM hM
    rw [hnorm]
    have hm := Subgroup.relIndex_mul_index hTM
    rw [hindex] at hm
    have hp : ((T : Subgroup H).relIndex M * M.index).Prime :=
      hm.symm ▸ (by decide : Nat.Prime 5)
    rcases Nat.prime_mul_iff.mp hp with ⟨_, hMi⟩ | ⟨_, hrel⟩
    · exact (hM.ne (Subgroup.index_eq_one.mp hMi)).elim
    · exact Subgroup.relIndex_eq_one.mp hrel
  · rw [hnorm]
    let := T.isPGroup'.isNilpotent
    infer_instance
  · refine ⟨⊥, bot_le, ?_, ?_, disjoint_bot_right, ?_⟩
    · simp
    · infer_instance
    · simpa using hnorm.symm
end CFSG.Quasithin.ChapterF.Source
