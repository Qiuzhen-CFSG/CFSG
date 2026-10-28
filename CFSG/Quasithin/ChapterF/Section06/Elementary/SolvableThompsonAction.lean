module
public import CFSG.Quasithin.ChapterB.Section02.SolvableActionFactors.TwoPerfect
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Subnormal
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.Representation.NormalElementaryQuotient.Thompson
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Quasithin.Rank

/-!
# A reduced Goldschmidt action with Thompson movement is nonsolvable

Suppose the first local residual is its commutator with ordinary J(S),
J(S) is not normal, and the opposite residual does not normalize it.
A reduced elementary module with full kernel O₂(G) gives a faithful FF
action if G is solvable. Solvable FF factorization then makes the two
residual images commute. The kernel lies in the first vertex, so residual
recovery lifts commutation to normalization, a contradiction.

The quotient is the literal G/O₂(G). Its three-rank bound is transported
only across the two-group kernel. The local S₃ quotient supplies the
{2,3} order bound on the opposite residual; it is not an extra assumption.
Source: Aschbacher--Smith F.6 and B.1.8; the solvable exclusions in
13.4.7(3), printed p.903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF
universe u
variable {G : Type u} [Group G] [Finite G]

theorem nonsolvable_of_reduced_thompson_pair
    (S : Sylow 2 G) {P Q : Subgroup G}
    (hg : ChapterF.IsGoldschmidtTriple P Q) (hSQ : (S : Subgroup G) ≤ Q)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hk : centralizer (U : Set G) = pCore 2 G)
    (hJ : ¬ (elementaryAbelianMaxJ (S : Subgroup G)).Normal)
    (hm : ⁅(pResidual 2 P).map P.subtype,elementaryAbelianMaxJ (S : Subgroup G)⁆ =
      (pResidual 2 P).map P.subtype)
    (hrank : primeRank 3 G ≤ 2)
    (hnot : ¬ (pResidual 2 Q).map Q.subtype ≤
      normalizer ((pResidual 2 P).map P.subtype : Set G)) :
    ¬ Group.IsSolvable G := by
  intro hs
  let : U.Normal := hU.normal
  let : IsElementaryAbelian 2 U := hU.elementary
  let : Group.IsSolvable G := hs
  let q := QuotientGroup.mk' (pCore 2 G)
  have hq := QuotientGroup.mk'_surjective (pCore 2 G)
  have hker : q.ker = centralizer (U : Set G) := by rw [QuotientGroup.ker_mk',hk]
  let ρ := NormalElementaryQuotient.representation U q hq hker
  let L := (pResidual 2 P).map P.subtype
  let R := (pResidual 2 Q).map Q.subtype
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  have hUS : U ≤ (S : Subgroup G) :=
    (IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal S
  have hff : IsFFModule ρ := by
    by_contra hn
    apply hJ
    exact NormalElementaryQuotient.thompson_normal_of_nonFF S U q hq hker
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hUS hn
  have hj : J.map q ≤ offenderSubgroup ρ := by
    rw [map_le_iff_le_comap]
    apply sSup_le
    intro E hE
    apply map_le_iff_le_comap.mp
    by_cases hn : E.map q = ⊥
    · rw [hn]; exact bot_le
    · exact (NormalElementaryQuotient.maxElementary_isBestOffender U q hq hker
        (S : Subgroup G) E hUS hE hn).le_offenderSubgroup ρ
  have hL : IsPPerfect 2 (L.map q) := (isPPerfect_embedded_pResidual 2 P).of_surjective
    (q.subgroupMap L) (q.subgroupMap_surjective L)
  have hR : IsPPerfect 2 (R.map q) := (isPPerfect_embedded_pResidual 2 Q).of_surjective
    (q.subgroupMap R) (q.subgroupMap_surjective R)
  have hmove : ⁅L.map q,J.map q⁆ = L.map q := by
    rw [←map_commutator]; exact congrArg (Subgroup.map q) hm
  have hr : primeRank 3 (G ⧸ pCore 2 G) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hrank
  have horder : ∃ m n : ℕ, Nat.card (R.map q) ∣ 2 ^ m * 3 ^ n := by
    obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
    have hc := ((S : Subgroup G).subgroupOf Q).index_mul_card
    rw [show ((S : Subgroup G).subgroupOf Q).index = 3 from
      SymmetricThreeTwoCore.sylow_index_three hg.quotient_right.some (S.subtype hSQ),
      Nat.card_congr (subgroupOfEquivOfLe hSQ).toEquiv,hn] at hc
    refine ⟨n,1,?_⟩
    have hd : Nat.card (R.map q) ∣ Nat.card Q := (card_map_dvd R q).trans
      ((card_map_dvd (pResidual 2 Q) Q.subtype).trans (card_subgroup_dvd_card _))
    simpa only [←hc,pow_one,Nat.mul_comm] using hd
  have hc := ChapterB.solvable_ff_thompson_actor_centralizes ρ inferInstance
    (pCore_quotient_pCore_eq_bot 2)
    (NormalElementaryQuotient.representation_injective U q hq hker) hff
    (L.map q) (R.map q) (J.map q) hL hR hj hmove hr horder
  have hcom : ⁅R,L⁆ ≤ pCore 2 G := by
    have hh : ⁅R,L⁆.map q = ⊥ := by
      rw [map_commutator]
      exact commutator_eq_bot_iff_le_centralizer.mpr hc
    have hh' := (Subgroup.map_eq_bot_iff _).mp hh
    simpa only [q,QuotientGroup.ker_mk'] using hh'
  apply hnot
  exact normalizes_residual_of_commutator_le_two R P P (pCore 2 G)
    P.le_normalizer (hg.twoCore_isGreatest.1.1.trans inf_le_left)
    pCore_isPGroup le_normalizer_of_normal hcom


end CFSG.Quasithin.ChapterF
