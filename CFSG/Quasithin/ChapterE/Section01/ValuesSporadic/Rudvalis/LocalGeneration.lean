module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.QuotientFamily
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup

/-!
# E-generation from a faithful simple subgroup in the local core quotient

Suppose H/O₂(H) has two-rank at most two and has a nonabelian simple normal
subgroup with trivial centralizer and two-group quotient. Every Sylow
subgroup supplements that simple subgroup. The whole quotient is then an
E2-member for each nontrivial elementary actor; the actual radical-quotient
rank is at most two. The proved normal-two-kernel lifting theorem yields
rank-two E-generation of H.

This is the local criterion for the two Rudvalis Sylow overgroups in
Aschbacher--Smith E.1.14(5), printed p.214, citing Asc82a, Lemma 4.9.
It uses the corrected local-tau definition in E.1.2 and the quotient lifting
of E.1.10. No general E-generation existence premise is needed. The concrete
Rudvalis quotient calculations and ambient generating cover remain separate
obligations; this module does not assert the Rudvalis clause of E.1.14.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Rudvalis
variable {G : Type*} [Group G] [Finite G]

/-- A faithful nonabelian simple normal subgroup with two-group quotient
makes the whole group an E-member; its two-rank bounds the required rank. -/
theorem isEGenerated_of_faithful_simple_normal {i : ℕ} (L : Subgroup G) [L.Normal]
    [IsSimpleGroup L] (ha : ¬ IsMulCommutative L)
    (hC : centralizer (L : Set G) = ⊥) (hq : IsPGroup 2 (G ⧸ L))
    (hrank : primeRank 2 G ≤ i) : IsEGenerated i G := by
  let : Group.IsPerfect L := ⟨
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator L)
      inferInstance).resolve_left (fun h => ha ((commutator_eq_bot_iff L).mp h))⟩
  have hR := SimpleSocle.radical_eq_bot L hC
  have hF := (simple_two_quotient_structure L ha hq (SimpleSocle.pCore_eq_bot hR 2)).1
  let : IsSimpleGroup (generalizedFitting G) := hF.symm ▸ inferInstance
  have haF : ¬ IsMulCommutative (generalizedFitting G) := hF.symm ▸ ha
  intro T
  have hsupp : L ⊔ (T : Subgroup G) = ⊤ := by
    simpa only [sup_comm] using T.sup_eq_top_of_quotient_isPGroup L hq
  have hsuppF : generalizedFitting G ⊔ (T : Subgroup G) = ⊤ := by
    rw [hF]
    exact hsupp
  apply ValuesEvenClassical.RankOneUpper.isEGeneratedAt_of_top_members T
  intro A hA hAT hne
  let := hA
  exact ValuesEvenClassical.RankOneUpper.isEMemberAt_top_of_simple_generalizedFitting
    haF T hsuppF T A hA hAT hne
    ((A.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 A)).trans hrank)

/-- The structural local input, expressed in the literal intrinsic core
quotient. This predicate contains no E-member or generation assumption. -/
@[expose] def HasRankTwoLocalQuotient (H : Type*) [Group H] : Prop :=
  let Q := H ⧸ pCore 2 H
  primeRank 2 Q ≤ 2 ∧ ∃ L : Subgroup Q,
    IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
      centralizer (L : Set Q) = ⊥ ∧ HasTwoGroupQuotient L

/-- The intrinsic two-core quotient criterion supplies the actual local
rank-two bound used in the Rudvalis generating-family assembly. -/
theorem isEGenerated_two_of_local_quotient (h : HasRankTwoLocalQuotient G) : IsEGenerated 2 G := by
  obtain ⟨hrank, L, hs, ha, hC, hN, hq⟩ := h
  let := hs
  let := hN
  exact IsEGenerated.of_normal_two_subgroup (pCore 2 G) pCore_isPGroup
    (isEGenerated_of_faithful_simple_normal L ha hC hq hrank)

end CFSG.Quasithin.ChapterE.Rudvalis
