module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PrimeRankResidualCentralizer
/-! # Normality of components with prime-to-p center
Distinct conjugate components commute and intersect inside their centers.
When the center has order prime to p, their p-ranks add. A strict bound
against twice the component rank therefore forces normality; no trivial
center or ambient component-normality assumption is used.
Source: Aschbacher--Smith A.3.8(3), p.46, and its use in 2.5.7, p.554. -/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
theorem IsComponent.normal_of_coprime_center_primeRank
    {L : Subgroup G} (hL : IsComponent G L) (p : ℕ) [Fact p.Prime]
    (hc : Nat.Coprime p (Nat.card (center L)))
    (hr : primeRank p G < 2 * primeRank p L) : L.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hne
  have hcomm : L.map (MulAut.conj g).toMonoidHom ≤ centralizer (L:Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      ((hL.map_conj g).commutator_eq_bot_of_ne hL hne)
  have hh := ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    (L.map (MulAut.conj g).toMonoidHom) L hcomm hc
  have he : primeRank p L = primeRank p (L.map (MulAut.conj g).toMonoidHom) :=
    primeRank_equiv p ((MulAut.conj g).subgroupMap L)
  rw [← he] at hh
  omega
end Theory.GroupTheory
