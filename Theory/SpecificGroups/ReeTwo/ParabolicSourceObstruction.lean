module

public import Theory.SpecificGroups.ReeTwo.Relations
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A quotient-center obstruction from the Ree root relations

The three root relations [v5,v7] = v11, [v3,v11] = v12 and
[v3,v12] = 1 rule out centrality of v5 modulo the normal cyclic group
of a nonidentity v12. Indeed centrality would place v11 in that cyclic
group, which v3 centralizes, contradicting the second relation.

This is an implication from explicitly stated relations in any group.
It requires no identification of an ambient group by its order, nor any
package containing the disputed quotient-center conclusion.

Source: Aschbacher, *The Tits group as a standard subgroup*, Math. Z. 181
(1982), (3.1), printed p.233. For the second relation the printed source
uses the reversed commutator; its value is the central involution v12,
so both orientations agree. This calculation is relevant to the quotient
by Z used in Aschbacher--Smith, Lemma 14.2.21, printed p.989.
-/

namespace ReeTwo

private theorem rightComm_eq_one_iff {G : Type*} [Group G] (a b : G) :
    rightComm a b = 1 ↔ a * b = b * a := by
  simp only [rightComm, mul_assoc, inv_mul_eq_iff_eq_mul, mul_one]

/-- Three source relations already exclude the asserted central coset. -/
public theorem rootFive_quotient_not_central_of_relations
    {G : Type*} [Group G] (v3 v5 v7 v11 v12 : G)
    (h57 : rightComm v5 v7 = v11) (h311 : rightComm v3 v11 = v12)
    (h312 : rightComm v3 v12 = 1) (hne : v12 ≠ 1)
    [(Subgroup.zpowers v12).Normal] :
    QuotientGroup.mk' (Subgroup.zpowers v12) v5 ∉
      Subgroup.center (G ⧸ Subgroup.zpowers v12) := by
  let q := QuotientGroup.mk' (Subgroup.zpowers v12)
  have h09 : v3 * v12 = v12 * v3 := (rightComm_eq_one_iff _ _).mp h312
  intro hc
  have hq : rightComm (q v5) (q v7) = 1 :=
    (rightComm_eq_one_iff _ _).mpr ((Subgroup.mem_center_iff.mp hc (q v7)).symm)
  have hx8 : v11 ∈ Subgroup.zpowers v12 := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q v11 = 1
    rw [← h57]
    simpa only [rightComm, map_mul, map_inv] using hq
  have hz : Subgroup.zpowers v12 ≤ Subgroup.centralizer ({v3} : Set G) := by
    apply Subgroup.zpowers_le_of_mem
    exact Subgroup.mem_centralizer_iff.mpr (by simpa using h09)
  have hc08 : v3 * v11 = v11 * v3 :=
    Subgroup.mem_centralizer_iff.mp (hz hx8) v3 (Set.mem_singleton _)
  exact hne (h311.symm.trans ((rightComm_eq_one_iff _ _).mpr hc08))

/-- In any nondegenerate realization of the ten-root presentation, the source
root v5 has a noncentral coset modulo the normal last-root subgroup. -/
public theorem rootFive_quotient_not_central_of_coreRelations
    {G : Type*} [Group G] (x : CoreRoot → G) (h : CoreRelations x)
    (hne : x 9 ≠ 1) [(Subgroup.zpowers (x 9)).Normal] :
    QuotientGroup.mk' (Subgroup.zpowers (x 9)) (x 2) ∉
      Subgroup.center (G ⧸ Subgroup.zpowers (x 9)) := by
  apply rootFive_quotient_not_central_of_relations (x 0) (x 2) (x 4) (x 8) (x 9)
  · simpa [coreCommutator, rootWord] using h.commutator 2 4 (by decide)
  · simpa [coreCommutator, rootWord] using h.commutator 0 8 (by decide)
  · simpa [coreCommutator, rootWord] using h.commutator 0 9 (by decide)
  · exact hne

end ReeTwo
