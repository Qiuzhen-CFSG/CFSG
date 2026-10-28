module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalSubgroups
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.Residual
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Tests
public import Theory.GroupTheory.PCoreFromTwoNormalizers

/-!
# Reducing Held pair placement to finite group calculations

A two-subgroup fixes a coset of any odd-index subgroup. After conjugating
our marked two-subgroup into the pair product, a double-coset factorization
and a prime-order obstruction test put every element of that product in
one of the two aligned local subgroups. A subgroup contained in the union
of two subgroups lies in one of them. Composing the actual conjugations
then gives placement in the literal ATLAS max3 or max4 subgroup.

The two-group, alignment, exhaustive factorization and finite-test premises
are explicit. This module does not claim that the supplied candidate data
pass those tests. The source adapter uses the already proved fact that the
permuting pair product has no prime divisors other than two and three.

Sources: Aschbacher–Smith, printed pp.509–511; Aschbacher, *Overgroups of
Sylow subgroups in sporadic groups* (1986); GLS3 Table 5.3p. This direct
route needs neither a maximal-subgroup catalogue nor global simplicity.
-/

public section
namespace Held.LocalPairs.PairCoverage.SylowOvergroups
open Subgroup Theory.GroupTheory.SubgroupEnumeration

/-- The finite tests exclude every representative outside the two local subgroups. -/
theorem representative_mem_aligned_of_checks (hcheck : RepresentativeChecks)
    (K : Subgroup He) (hPK : markedSubgroup ≤ K)
    (hprimes : ∀ p : ℕ, Nat.Prime p → p ∣ Nat.card K → p = 2 ∨ p = 3)
    (j : Fin 4831) (hj : representative j ∈ K) :
    representative j ∈ alignedOvergroup false ∨
      representative j ∈ alignedOvergroup true := by
  rcases hcheck j with h | h | ⟨p, hp, hp2, hp3, x, hx, hxp⟩
  · exact Or.inl h
  · exact Or.inr h
  · have hxK : x ∈ K := (sup_le hPK (zpowers_le.mpr hj)) hx
    have hd : p ∣ Nat.card K := hxp ▸ K.orderOf_dvd_natCard hxK
    exact ((hprimes p hp hd).elim hp2 hp3).elim

/-- Factoring through a double coset recovers its representative inside K.
The union-of-two-subgroups lemma then puts all of K in one candidate. -/
theorem le_aligned_of_tests
    (halign : ∀ i, markedSubgroup ≤ alignedOvergroup i)
    (hcover : Covers) (hcheck : RepresentativeChecks)
    (K : Subgroup He) (hPK : markedSubgroup ≤ K)
    (hprimes : ∀ p : ℕ, Nat.Prime p → p ∣ Nat.card K → p = 2 ∨ p = 3) :
    ∃ i : Bool, K ≤ alignedOvergroup i := by
  have hU : (K : Set He) ⊆
      (alignedOvergroup false : Set He) ∪ (alignedOvergroup true : Set He) := by
    intro x hx
    obtain ⟨j, s, t, hs, ht, he⟩ := hcover x
    have hr : representative j ∈ K := by
      have hm := K.mul_mem (K.mul_mem (K.inv_mem (hPK hs)) hx) (K.inv_mem (hPK ht))
      rw [he] at hm
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hm
    rcases representative_mem_aligned_of_checks hcheck K hPK hprimes j hr with h | h
    · exact Or.inl (he ▸ (alignedOvergroup false).mul_mem
        ((alignedOvergroup false).mul_mem (halign false hs) h)
        (halign false ht))
    · exact Or.inr (he ▸ (alignedOvergroup true).mul_mem
        ((alignedOvergroup true).mul_mem (halign true hs) h)
        (halign true ht))
  rcases SubgroupClass.subset_union.mp hU with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

/-- A two-subgroup fixes an odd-index coset. Apply the finite tests after
conjugating it into K, then compose the two actual inner conjugations. -/
theorem placement_of_tests (hP : IsPGroup 2 markedSubgroup)
    (halign : ∀ i, markedSubgroup ≤ alignedOvergroup i)
    (hcover : Covers) (hcheck : RepresentativeChecks)
    (K : Subgroup He) (hindex : ¬ 2 ∣ K.index)
    (hprimes : ∀ p : ℕ, Nat.Prime p → p ∣ Nat.card K → p = 2 ∨ p = 3) :
    ∃ (i : Bool) (g : He), K.map (MulAut.conj g).toMonoidHom ≤ localOvergroup i := by
  obtain ⟨g, hg⟩ := exists_conj_overgroup_of_index_primeTo markedSubgroup K hP hindex
  let e := MulAut.conj g
  let L := K.comap e.toMonoidHom
  have hcard : Nat.card L = Nat.card K := by
    let f : L ≃* K := (e.subgroupMap L).trans
      (MulEquiv.subgroupCongr (map_comap_eq_self_of_surjective
        (f := e.toMonoidHom) e.surjective K))
    exact Nat.card_congr f.toEquiv
  obtain ⟨i, hi⟩ := le_aligned_of_tests halign hcover hcheck L hg
    (fun p hp hd => hprimes p hp (hcard ▸ hd))
  let c := if i then alignment else 1
  have hm : (K.map e.symm.toMonoidHom).map (MulAut.conj c).toMonoidHom ≤
      localOvergroup i := by
    rw [← comap_equiv_eq_map_symm' e]
    exact (map_mono hi).trans_eq (alignedOvergroup_map i)
  refine ⟨i, c * g⁻¹, ?_⟩
  rw [map_map] at hm
  exact hm

end Held.LocalPairs.PairCoverage.SylowOvergroups
