module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PrimeRankProduct
/-!
# Component normalization from the rank of an overlap

If a subgroup M moves a centerless component C, the two conjugate copies
of M intersect C lie in M, commute, and intersect trivially. Their prime
ranks therefore add. A bound strictly below twice the rank of the overlap
forces M to normalize C.

This retains the overlap instead of requiring the whole component inside M.
Source: the commuting-component theorem, GLS vol.2, Theorem 3.5; the
exchanged-component step of Aschbacher--Smith 5.2.2, pp.648--649.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
/-- A subgroup with insufficient rank for two conjugate overlaps fixes the component. -/
theorem IsComponent.normalizes_of_overlap_primeRank
    {C M : Subgroup G} (hC : IsComponent G C) (hz : center C = ⊥)
    (p : ℕ) [Fact p.Prime]
    (hr : primeRank p M < 2 * primeRank p (M ⊓ C : Subgroup G)) :
    M ≤ normalizer (C : Set G) := by
  intro m hm
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  let B := M ⊓ C
  let B' := B.map (MulAut.conj m).toMonoidHom
  have hc : C ≤ centralizer (C.map (MulAut.conj m).toMonoidHom : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (hC.commutator_eq_bot_of_ne (hC.map_conj m) (Ne.symm hne))
  have hdis : Disjoint B B' := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hx,hx'⟩
    have hxC : x ∈ C := hx.2
    have hxC' : x ∈ C.map (MulAut.conj m).toMonoidHom := map_mono inf_le_right hx'
    have hxc : (⟨x,hxC⟩ : C) ∈ center C := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext ((le_centralizer_iff.mp hc) hxC' y y.property)
    have hx1 : (⟨x,hxC⟩ : C) = 1 := by simpa only [hz, mem_bot] using hxc
    exact congrArg (fun c : C => (c : G)) hx1
  have hcomm : B ≤ centralizer (B' : Set G) :=
    inf_le_right.trans (hc.trans (centralizer_le (map_mono inf_le_right)))
  have hB'M : B' ≤ M := by
    exact (map_mono (show B ≤ M from inf_le_left)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hm))
  have hle : B ⊔ B' ≤ M := sup_le inf_le_left hB'M
  have hbound := primeRank_le_of_injective p (inclusion hle) (inclusion_injective hle)
  rw [B.primeRank_sup_eq_add_of_disjoint_commuting B' hdis hcomm p] at hbound
  have hsame : primeRank p B = primeRank p B' :=
    primeRank_equiv p ((MulAut.conj m).subgroupMap B)
  rw [← hsame] at hbound
  change primeRank p (M ⊓ C : Subgroup G) + primeRank p (M ⊓ C : Subgroup G) ≤
    primeRank p M at hbound
  omega
end Theory.GroupTheory
