module

public import Theory.PrimeRank
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Prime rank in groups with cyclic Sylow subgroups

A cyclic Sylow `p`-subgroup forces every abelian `p`-subgroup to have at most
one generator. The same bound holds in every surjective image: the image of
a Sylow subgroup is Sylow, and an image of a cyclic group is cyclic.

These are the cyclic-Sylow steps in Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), Lemma A.2.7, p. 34.
The proof works also for `p = 2`; the converse used there requires odd `p`.
-/

public section

private theorem rank_le_one_of_cyclic {G : Type*} [Group G] [Group.FG G]
    (hG : IsCyclic G) : Group.rank G ≤ 1 := by
  classical
  obtain ⟨g, hg⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := G)).mp hG
  have h : Subgroup.closure (({g} : Finset G) : Set G) = ⊤ := by
    simpa only [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure] using hg
  simpa only [Finset.card_singleton] using Group.rank_le h

namespace Sylow

/-- A cyclic Sylow subgroup bounds the corresponding prime rank by one. -/
theorem primeRank_le_one_of_isCyclic {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hP : IsCyclic P) :
    primeRank p G ≤ 1 := by
  apply csSup_le'
  rintro n ⟨A, hAp, _, hfg, hn⟩
  obtain ⟨Q, hAQ⟩ := hAp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hQ : IsCyclic Q := by
    let e : (P : Subgroup G) ≃* ((g • P : Sylow p G) : Subgroup G) :=
      Subgroup.equivMapOfInjective (P : Subgroup G)
        (MulAut.conj g).toMonoidHom (EquivLike.injective (MulAut.conj g))
    have hconj := e.isCyclic.mp hP
    rwa [hg] at hconj
  let := hQ
  exact hn.trans (rank_le_one_of_cyclic (Subgroup.isCyclic_of_le hAQ))

/-- Every surjective image of a finite group with cyclic Sylow `p`-subgroups
has `p`-rank at most one. -/
theorem primeRank_le_one_of_surjective {G H : Type*} [Group G] [Finite G]
    [Group H] {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hP : IsCyclic P)
    (f : G →* H) (hf : Function.Surjective f) : primeRank p H ≤ 1 := by
  let : Finite H := Finite.of_surjective f hf
  let : IsCyclic P := hP
  apply (P.mapSurjective hf).primeRank_le_one_of_isCyclic
  change IsCyclic ((P : Subgroup G).map f)
  exact isCyclic_of_surjective (f.subgroupMap (P : Subgroup G))
    (f.subgroupMap_surjective (P : Subgroup G))

/-- In particular, quotienting a finite group with cyclic Sylow `p`-subgroups
cannot produce `p`-rank greater than one. -/
theorem primeRank_quotient_le_one {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hP : IsCyclic P)
    (K : Subgroup G) [K.Normal] : primeRank p (G ⧸ K) ≤ 1 :=
  P.primeRank_le_one_of_surjective hP (QuotientGroup.mk' K)
    (QuotientGroup.mk'_surjective K)

end Sylow
