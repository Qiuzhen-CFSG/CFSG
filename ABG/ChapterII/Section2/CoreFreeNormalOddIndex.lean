module
public import ABG.ChapterII.Section2.Defs
public import ABG.ChapterII.Section1.InvolutionsCyclicImage
public import FeitThompson.PCore.PPrimeCore
public import Theory.GroupTheory.CyclicSylowTwoOddOrder

/-!
# Normal subgroups of odd-core-free QD groups

Every nontrivial normal subgroup of a finite QD group with trivial odd core
has odd index. Both quasi-dihedral and wreathed Sylow alternatives are included.
This is the quotient step in ABG Chapter II Section 2 Proposition 2,
`refs/latex/alperin-brauer-gorenstein-pages/page-016.tex`, article p.15.

A nontrivial normal subgroup N has even order, since an odd normal subgroup
would lie in the trivial odd core. Cauchy's theorem gives an involution in N.
The unique ambient involution conjugacy class and normality then put every
involution in N. The defining generators of either Sylow type show that
killing these involutions gives a cyclic image. Consequently G/N has cyclic
Sylow two-subgroups. The absence of normal subgroups of index two descends
to G/N, where Burnside transfer forces odd order.

The result supplies the odd index of a minimal normal subgroup in the source
proof before the separate simplicity argument. No simplicity or solvability
assumption is used here.
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]

private theorem square_one_mem_normal
    (hclass : HasElementConjugacyClassCount G 2 1)
    (hcore : pPrimeCore 2 G = ⊥) (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥)
    {x : G} (hx : x ^ 2 = 1) : x ∈ N := by
  by_cases hx1 : x = 1
  · exact hx1 ▸ N.one_mem
  have hdiv : 2 ∣ Nat.card N := by
    by_contra h
    exact hN (pPrimeCore_eq_bot_iff.mp hcore N inferInstance
      (Nat.prime_two.coprime_iff_not_dvd.mpr h))
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 hdiv
  have hyG : orderOf (y : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hy
  have hx2 : orderOf x = 2 := orderOf_eq_prime hx hx1
  obtain ⟨r, _, _, hcoverage⟩ := hclass
  obtain ⟨i, hi⟩ := hcoverage x hx2
  obtain ⟨j, hj⟩ := hcoverage y hyG
  have hij : i = j := Subsingleton.elim _ _
  have hconj : IsConj (y : G) x := hj.trans (hij ▸ hi.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  rw [← hg]
  exact (inferInstance : N.Normal).conj_mem y y.property g

omit [Finite G] in
private theorem no_index_two_quotient (hno : HasNoNormalIndexTwoSubgroup G)
    (N : Subgroup G) [N.Normal] : HasNoNormalIndexTwoSubgroup (G ⧸ N) := by
  intro U hU hi
  let := hU
  exact hno (U.comap (QuotientGroup.mk' N)) inferInstance
    ((U.index_comap_of_surjective (QuotientGroup.mk'_surjective N)).trans hi)

private theorem normal_odd_index_from_sylow
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥)
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (hno : HasNoNormalIndexTwoSubgroup G)
    (hclass : HasElementConjugacyClassCount G 2 1)
    (hcore : pPrimeCore 2 G = ⊥) : Odd N.index := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let f := q.comp (S : Subgroup G).subtype
  have hkill : ∀ x : S, x ^ 2 = 1 → f x = 1 := by
    intro x hx
    exact (QuotientGroup.eq_one_iff _).mpr
      (square_one_mem_normal hclass hcore N hN (congrArg Subtype.val hx))
  let R : Sylow 2 (G ⧸ N) := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have hrange : f.range = (R : Subgroup (G ⧸ N)) := by
    rw [Sylow.coe_mapSurjective]
    exact (MonoidHom.range_comp q (S : Subgroup G).subtype).trans
      (congrArg (Subgroup.map q) (S : Subgroup G).range_subtype)
  have hR : IsCyclic R := by
    have h := cyclic_range_of_involutions_killed hS f hkill
    rwa [hrange] at h
  rw [N.index_eq_card]
  exact odd_card_of_cyclic_sylow_two_of_no_normal_index_two R hR
    (no_index_two_quotient hno N)

/-- Every nontrivial normal subgroup of an odd-core-free QD group has odd index. -/
public theorem IsQDGroup.odd_index_of_normal_ne_bot
    (hG : IsQDGroup G) (hcore : pPrimeCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : Odd N.index := by
  rcases hG with ⟨S, T, Q, hframe, hpattern⟩ | ⟨S, n, U, V, hframe, hpattern⟩
  · exact normal_odd_index_from_sylow N hN S (Or.inl hframe.1)
      hpattern.1 hpattern.2.1 hcore
  · exact normal_odd_index_from_sylow N hN S (Or.inr ⟨n, hframe.1⟩)
      hpattern.1 hpattern.2.1 hcore

end ABG
