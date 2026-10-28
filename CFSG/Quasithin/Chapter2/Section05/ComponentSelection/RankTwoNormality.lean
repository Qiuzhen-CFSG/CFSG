module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.OrbitSource
/-! # Source normality with a two-primary component center
The original Gamma group has nontrivial two-core, so ambient quasithinness
bounds every odd prime rank by two. A component of odd-prime rank at least
two and two-primary center is therefore normal. The actual rank witness
remains explicit for the rank-two model calculation; no centerlessness is
assumed and the original component and ambient group are retained.
Source: Aschbacher--Smith 2.5.7, printed p.554, applying 1.2.1(3). -/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}
theorem source_component_normal_of_odd_rank
    (hqt : IsQuasithin G) (hH : H∈gammaZero (Chapter1.He G) M)
    (L : Subgroup H) (hL : IsComponent H L)
    (hZ : IsPGroup 2 (center L)) (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hr : 2≤primeRank p L) : L.Normal := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n,hn⟩ := hZ.exists_card_eq
  have hc : Nat.Coprime p (Nat.card (center L)) := by
    rw [hn]
    exact (Nat.coprime_two_right.mpr ho).pow_right n
  have hcore : pCore 2 H≠⊥ := by
    intro he
    have hh := (hH.elim (fun h=>h.1.1) (fun h=>h.1)).1
    exact hh (by simp only [twoCore,he,Subgroup.map_bot])
  have hb := Theory.Quasithin.primeRank_subgroup_le_two_of_normal_two_subgroup
    hqt H (pCore 2 H) hcore pCore_isPGroup p hp ho
  exact hL.normal_of_coprime_center_primeRank p hc (by omega)
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
