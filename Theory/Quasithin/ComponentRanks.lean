module

public import Theory.Quasithin.Rank
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import FeitThompson.FinalTheorem

/-!
# Odd-prime ranks of distinct components in a quasithin group

A nontrivial Sylow two-subgroup of one component is centralized by every
other component. Thus each other component lies in an actual two-local,
bounding all its odd-prime ranks by two. The Sylow subgroup is nontrivial
because a quasisimple group is nonsolvable and hence has even order.

Source: Aschbacher–Smith A.2.12, printed p.36, after the semisimple reduction.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {C D : Subgroup G}

theorem IsComponent.primeRank_le_two_of_ne
    (hC : IsComponent G C) (hD : IsComponent G D) (hne : C ≠ D)
    (hG : IsQuasithin G) (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p C ≤ 2 := by
  let := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  have heven : 2 ∣ Nat.card D := by
    by_contra hn
    exact Group.IsPerfect.not_isSolvable D
      (odd_order_theorem D (Nat.not_even_iff_odd.mp (by
        simpa only [even_iff_two_dvd] using hn)))
  obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := D)
  let N : Subgroup G := (Q : Subgroup D).map D.subtype
  have hN : N ≠ ⊥ := by
    intro hh
    exact Q.ne_bot_of_dvd_card heven
      ((map_eq_bot_iff_of_injective _ D.subtype_injective).mp hh)
  have hloc : IsTwoLocal (normalizer (N : Set G)) :=
    ⟨N, hN, Q.isPGroup'.map D.subtype, rfl⟩
  have hND : N ≤ D := map_subtype_le _
  have hCD := commutator_eq_bot_iff_le_centralizer.mp
    (hC.commutator_eq_bot_of_ne hD hne)
  have hCN : C ≤ normalizer (N : Set G) :=
    (hCD.trans (centralizer_le hND)).trans (Subgroup.centralizer_le_normalizer _)
  exact (primeRank_mono p hCN).trans
    (isQuasithin_iff_twoLocal.mp hG _ hloc p hp ho)

end Theory.GroupTheory
