module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Contracts
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Natural.LowRank
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Natural.EightConjugacy
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Natural.EightSeed

/-!
# Natural elementary actors generate over Inn(A₆) within budget six

The injective permutation action identifies a natural actor with its literal
preimage in S₆. In ranks one and two, the even-involution generation theorem
and two elementary odd-involution identities give the required bounds.
Every elementary eight-group of Aut(A₆) is conjugate to the image of the
three disjoint transpositions. Two A₆ conjugates generate over A₆ for this
representative; automorphism transport preserves the inner conjugators.
Thus the numbers of conjugates are at most six, three and two in ranks
one, two and three, respectively. No generation premise remains.

Source: the group-generation route to Aschbacher–Smith K.1.1, printed p.452
(PDF p.463), citing GM02 Theorem 6.2 and Table 6.3. The ambient lift and
representation-theoretic degree conclusion remain with ActorGeneration.
-/

public section

open Subgroup Representation.BinaryOffender AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof
open NaturalProof

private theorem eight_generation (A : Subgroup AutA6) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 8) : ∃ c : Fin 2 → A6,
    AlternatingSix.ShadowLocal.inner ≤
      ⨆ i, A.map (MulAut.conj (MulAut.conj (c i))).toMonoidHom := by
  let F := seedPerm.map permutationAction
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  have hF : Nat.card F = 8 := by
    rw [Subgroup.card_map_of_injective permutationAction_injective, card_seedPerm]
  obtain ⟨g,hg⟩ := eight_conjugacy F A hF hA
  obtain ⟨c,hc⟩ := seed_two_conjugates
  have hspan := permutation_span_to_natural seedPerm c hc
  have hm := inner_conjugate_span_map g F c hspan
  have he : MulAut.congr g = MulAut.conj g := by rfl
  rw [he,hg] at hm
  exact ⟨fun i => g (c i), hm⟩

/-- Every nontrivial elementary natural actor has inner-conjugate budget six. -/
theorem naturalGeneration : NaturalGeneration := by
  intro A hA hAn
  let : IsElementaryAbelian 2 A := hA.2
  have hr : rank A ≤ 3 :=
    (Nat.log_mono_right (b := 2) (elementary_card_le_eight A)).trans
      (by decide : Nat.log 2 8 ≤ 3)
  by_cases hr2 : rank A ≤ 2
  · obtain ⟨hE,he,hrE⟩ := preimage_elementary A hA hAn
    obtain ⟨n,c,hn,hc⟩ := permutation_low_rank (A.comap permutationAction) hE (by omega)
    refine ⟨n,c,by simpa only [hrE] using hn,?_⟩
    have hm := permutation_span_to_natural (A.comap permutationAction) c hc
    rwa [he] at hm
  · have hr3 : rank A = 3 := by omega
    have hcard : Nat.card A = 8 := by
      rw [hA.card_eq_two_pow_rank, hr3]
      decide
    obtain ⟨c,hc⟩ := eight_generation A hcard
    exact ⟨2,c,by omega,hc⟩
end CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof
