module

public import Theory.GroupTheory.CComponent.QuotientLifting
public import CFSG.Quasithin.ChapterA.Section01
public import FeitThompson.FinalTheorem

/-!
# The small Sylow obstruction in Lemma 1.2.5

A nonabelian simple group has even order by the proved odd-order theorem.
A.1.38 then excludes cyclic Sylow two-subgroups: its normal complement
would be trivial or the whole simple group, contradicting perfectness or
evenness. Thus its Sylow two-subgroups have order greater than two.

Consequently, in a C-component, a subgroup of relative index at most two
in a Sylow two-subgroup cannot lie in the solvable radical; its commutator
with the whole component is nonsolvable. This supplies the parity step
omitted by citing A.1.38 alone in the printed proof.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 1.2.5, printed p.505, and A.1.38, printed p.31 (1 March 2004).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.Section02.IndexTwo
variable {G : Type*} [Group G] [Finite G]

/-- The odd-order theorem supplies the parity premise needed for A.1.38. -/
theorem two_dvd_card_of_not_isSolvable (hn : ¬ Group.IsSolvable G) :
    2 ∣ Nat.card G := by
  by_contra he
  exact hn (odd_order_theorem G (Nat.not_even_iff_odd.mp
    (fun h => he (even_iff_two_dvd.mp h))))

/-- A.1.38 rules out a cyclic Sylow two-subgroup in a nonabelian simple group. -/
theorem not_isCyclic_sylow_of_simple_perfect [IsSimpleGroup G] [Group.IsPerfect G]
    (S : Sylow 2 G) : ¬ IsCyclic S := by
  intro hc
  have heven := two_dvd_card_of_not_isSolvable (Group.IsPerfect.not_isSolvable G)
  obtain ⟨N, hn, hcop, hp⟩ := ChapterA.lemma_A_1_38 S
    ((Nat.minFac_eq_two_iff _).mpr heven) hc
  let := hn
  rcases hn.eq_bot_or_eq_top with hb | ht
  · subst N
    let := hp.isNilpotent
    exact Group.IsPerfect.not_isSolvable G
      (Group.isSolvable_of_surjective (f := QuotientGroup.quotientBot.toMonoidHom)
        QuotientGroup.quotientBot.surjective)
  · have hcopG : Nat.Coprime 2 (Nat.card G) := by
      simpa only [ht, Nat.card_congr (topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv] using hcop
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hcopG) heven

/-- The Sylow two-subgroup of a nonabelian simple group has order greater than two. -/
theorem two_lt_card_sylow_of_simple_perfect [IsSimpleGroup G] [Group.IsPerfect G]
    (S : Sylow 2 G) : 2 < Nat.card S := by
  by_contra hn
  have hp : 0 < Nat.card S := Nat.card_pos
  have hc : Nat.card S = 1 ∨ Nat.card S = 2 := by omega
  have hd : Nat.card S ∣ 2 := by rcases hc with hc | hc <;> simp [hc]
  exact not_isCyclic_sylow_of_simple_perfect S (isCyclic_of_card_dvd_prime hd)

/-- The source's index-at-most-two subgroup survives the intrinsic radical quotient. -/
theorem not_le_radical_of_sylow_index_le_two {B : Subgroup G} (hB : B.IsCComponent)
    (S : Sylow 2 B) (V : Subgroup B) (hi : V.relIndex S ≤ 2) :
    ¬ V ≤ solvableRadical B := by
  intro hV
  let := hB.perfect
  let := hB.isSimpleGroup_quotient_solvableRadical
  let q := QuotientGroup.mk' (solvableRadical B)
  let T := S.mapSurjective (QuotientGroup.mk'_surjective (solvableRadical B))
  have hc : Nat.card T ≤ 2 := by
    change Nat.card ((S : Subgroup B).map q) ≤ 2
    rw [← relIndex_ker]
    have hk : q.ker = solvableRadical B := QuotientGroup.ker_mk' _
    rw [hk]
    exact (relIndex_le_of_le_left hV
      (V.subgroupOf S).index_ne_zero_of_finite).trans hi
  exact (not_le_of_gt (two_lt_card_sylow_of_simple_perfect T)) hc

/-- Its commutator with the C-component is nonsolvable. -/
theorem nonsolvable_commutator_of_sylow_index_le_two {B : Subgroup G}
    (hB : B.IsCComponent) (S : Sylow 2 B) (V : Subgroup B)
    (hi : V.relIndex S ≤ 2) :
    ¬ Group.IsSolvable (⁅(⊤ : Subgroup B), V⁆ : Subgroup B) := by
  intro hs
  have hnormal : (⁅(⊤ : Subgroup B), V⁆ : Subgroup B).Normal := by
    rw [← normalizer_eq_top_iff]
    exact top_unique (normalizer_commutator_ge_left ⊤ V)
  have hle := le_solvableRadical _ hnormal hs
  let q := QuotientGroup.mk' (solvableRadical B)
  have hm : (⁅(⊤ : Subgroup B), V⁆ : Subgroup B).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    simpa only [q, QuotientGroup.ker_mk'] using hle
  rw [map_commutator, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hm
  have hV := commutator_top_left_eq_bot_iff_le_center.mp hm
  have hcenter : center (B ⧸ solvableRadical B) = ⊥ := by
    apply le_bot_iff.mp
    rw [← solvableRadical_quotient_solvableRadical (G := B)]
    exact le_solvableRadical _ inferInstance (Group.isSolvable_of_comm
      (fun a b => Subtype.ext (mem_center_iff.mp a.2 b).symm))
  have hVker : V ≤ q.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    exact bot_unique (hcenter ▸ hV)
  exact not_le_radical_of_sylow_index_le_two hB S V hi
    (by simpa only [q, QuotientGroup.ker_mk'] using hVker)

end CFSG.Quasithin.Chapter1.Section02.IndexTwo
