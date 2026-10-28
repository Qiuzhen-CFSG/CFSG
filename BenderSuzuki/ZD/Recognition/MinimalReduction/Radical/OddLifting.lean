module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.OddQuotient
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.OddLifting.Transport

/-!
# Lifting the complete ZD conclusion through the odd core

Elementary four-subgroups inject through an odd kernel, so the rank-one
alternative lifts. In the structural alternative the transport theorem lifts
the square-one element in M, removes the odd factor from the generation
assertion, and identifies every quotient clause through an actual isomorphism.

The lifting only needs involution generation and containment of the kernel in
M. The conjugacy, two-centrality and fusion preliminaries used in the source
are needed for quotient product disconnection and odd-core containment, rather
than for this step. Those inputs remain the responsibility of the caller.

Source: GLS, Volume 4, Chapter 2, Lemma 4.5, first paragraph, printed p. 34
(PDF p. 51); `refs/KGroup/GLS4/Chapter2.tex`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1

/-- Both alternatives of the ZD conclusion lift through an odd normal
subgroup contained in M, for a generating set of square-one elements. -/
public theorem conclusion_of_odd_quotient
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (hgen : Subgroup.closure Z = ⊤) (hsq : ∀ z ∈ Z, z ^ 2 = 1)
    (N : Subgroup G) [N.Normal] (hNM : N ≤ M) (hodd : Odd (Nat.card N))
    (h : Conclusion ((QuotientGroup.mk' N) '' Z) (M.map (QuotientGroup.mk' N))) :
    Conclusion Z M := by
  let q := QuotientGroup.mk' N
  have hker : Nat.Coprime 2 (Nat.card q.ker) := by
    simpa only [q, QuotientGroup.ker_mk'] using hodd.coprime_two_left
  rcases h with hrank | hstructure
  · left
    intro hr
    let e : Subgroup.closure Z ≃* G :=
      (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
    have hgenQ : Subgroup.closure (q '' Z) = ⊤ := by
      rw [← MonoidHom.map_closure, hgen,
        Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N)]
    let eQ : Subgroup.closure (q '' Z) ≃* (G ⧸ N) :=
      (MulEquiv.subgroupCongr hgenQ).trans Subgroup.topEquiv
    exact hrank (((hr.map_of_injective e.toMonoidHom e.injective).map_of_coprime_ker
      q hker).map_of_injective eQ.symm.toMonoidHom eQ.symm.injective)
  · right
    exact hstructure.of_odd_surjection q hker
      (by simpa only [q, QuotientGroup.ker_mk'] using hNM) hsq

/-- The full odd-core lifting step in GLS Chapter 2, Lemma 4.5. In
particular, all structural clauses and the rank-one branch are retained. -/
public theorem conclusion_of_oddCore_quotient
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (hgen : Subgroup.closure Z = ⊤)
    (hOM : pPrimeCore 2 G ≤ M)
    (hquot : Conclusion ((QuotientGroup.mk' (pPrimeCore 2 G)) '' Z)
      (M.map (QuotientGroup.mk' (pPrimeCore 2 G)))) : Conclusion Z M := by
  exact conclusion_of_odd_quotient hgen (fun z hz => (h.involutions z hz).sq_eq_one)
    (pPrimeCore 2 G) hOM (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hquot

end BenderSuzuki.ZD
