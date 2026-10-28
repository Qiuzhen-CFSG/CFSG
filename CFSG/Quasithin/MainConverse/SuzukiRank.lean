module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.SpecificGroups.Suzuki.OddSubgroups

/-!
# The QT clause for the Suzuki family

All odd Sylow subgroups of the concrete Suzuki group are cyclic. Thus all
odd prime ranks are at most one, in particular at most two. Monotonicity
gives the same bound in every 2-local subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1), printed p.4, and Remark A.2.4. The field has order
2^(2m+1), with m ≥ 1. This proves QT only; the proper-K and E clauses
are separate converse obligations.
-/

namespace CFSG.Quasithin.MainConverse

open BenderSuzuki.MatrixGroups

public theorem suzuki_stronglyQuasithin {m : ℕ} (hm : 1 ≤ m) :
    IsStronglyQuasithin (SuzukiMatrixGroup m) := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  let P : Sylow p (SuzukiMatrixGroup m) := Classical.choice inferInstance
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact ho.not_two_dvd_nat (dvd_refl 2)
  exact (P.primeRank_le_one_of_isCyclic
    (suzukiSylow_isCyclic_of_ne_two (by omega) hp2 P)).trans (by decide)

public theorem suzuki_quasithin_of_iso {G : Type*} [Group G] [Finite G]
    {m : ℕ} (hm : 1 ≤ m) (e : G ≃* SuzukiMatrixGroup m) : IsQuasithin G :=
  Theory.GroupTheory.isQuasithin_of_equiv e.symm (suzuki_stronglyQuasithin hm).quasithin

end CFSG.Quasithin.MainConverse
