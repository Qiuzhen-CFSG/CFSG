module
public import Theory.GroupTheory.CComponent.RadicalFreeProduct
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PrimeRankProduct

/-!
# A rank-one overlap stabilizes a component

Distinct components in a radical-free finite group commute and meet trivially.
If a subgroup I moves a component K, a positive-prime-rank subgroup of I ∩ K
and its conjugate contribute two independent ranks inside I. Thus prime rank
at most one forces I to normalize every component it meets in positive rank.

The terminal component sieve applies this after quotienting by O₂(H), with
I the literal image of M ∩ H. Source: Aschbacher--Smith, 14.6.20, printed
p.1037, using the intersection rank bound in 14.2.2(4).
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A subgroup of prime rank at most one normalizes every component with
which it has positive prime-rank overlap, if the ambient radical is trivial. -/
theorem IsCComponent.le_normalizer_of_overlap_primeRank
    {p : ℕ} [Fact p.Prime] {K I J : Subgroup G}
    (hR : solvableRadical G = ⊥) (hK : K.IsCComponent)
    (hI : primeRank p I ≤ 1) (hJK : J ≤ K) (hJI : J ≤ I)
    (hJ : 0 < primeRank p J) : I ≤ normalizer (K : Set G) := by
  intro g hg
  by_contra hn
  let a := MulAut.conj g
  have hne : K ≠ K.map a.toMonoidHom := by
    intro he
    exact hn (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hc := hK.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR (hK.map_equiv a) hne
  have hd := hK.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hR hc
  have hJJ : Disjoint J (J.map a.toMonoidHom) := hd.mono hJK (map_mono hJK)
  have hcc : J ≤ centralizer (J.map a.toMonoidHom : Set G) :=
    hJK.trans ((commutator_eq_bot_iff_le_centralizer.mp hc).trans (centralizer_le (map_mono hJK)))
  have hmap : J.map a.toMonoidHom ≤ I := by
    apply (map_mono hJI).trans
    exact (mem_normalizer_iff_map_conj_eq.mp (I.le_normalizer hg)).le
  have hr := (primeRank_mono p (sup_le hJI hmap)).trans hI
  rw [primeRank_sup_eq_add_of_disjoint_commuting J (J.map a.toMonoidHom) hJJ hcc p,
    ← primeRank_equiv p (J.equivMapOfInjective a.toMonoidHom a.injective)] at hr
  omega
end Subgroup
