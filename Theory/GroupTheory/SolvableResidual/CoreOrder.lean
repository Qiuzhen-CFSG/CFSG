module
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# Recovering a normal subgroup from the residual and prime core

If N is normal with solvable quotient, it contains the solvable residual R.
When the prime core of G lies in R, its intersection formula identifies it
with the embedded prime core of N. Equality of |R| with |N/O_p(N)| |O_p(G)|
then gives N=R. If N/O_p(N) is perfect, core containment alone suffices:
the embedded O_p(N) lies in the residual of N, whose image is the whole
perfect quotient. This identifies an original marked local subgroup after
the parabolic has been recognized; it does not recognize that parabolic.

Source application: Aschbacher--Smith F.1.12, printed p.264, identification
of the original nonbinary local factors with their solvable residuals.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem normal_eq_solvableResidual_of_core_order (p : ℕ) (N : Subgroup G)
    [N.Normal] [Group.IsSolvable (G ⧸ N)]
    (hcore : pCore p G ≤ solvableResidual G)
    (hcard : Nat.card (solvableResidual G) =
      Nat.card (N ⧸ pCore p N) * Nat.card (pCore p G)) : N = solvableResidual G := by
  have hRN : solvableResidual G ≤ N := solvableResidual_le_of_solvable_quotient N
  have hc := pCore_eq_map_of_normal_of_le p N (hcore.trans hRN)
  have hccard : Nat.card (pCore p N) = Nat.card (pCore p G) := by
    rw [hc]
    exact (card_map_of_injective N.subtype_injective).symm
  have hNcard := card_eq_card_quotient_mul_card_subgroup (pCore p N)
  rw [hccard, ← hcard] at hNcard
  exact (eq_of_le_of_card_ge hRN hNcard.le).symm

/-- Perfectness of the core quotient removes the residual-order premise. -/
theorem normal_eq_solvableResidual_of_perfect_core_quotient (p : ℕ) (N : Subgroup G)
    [N.Normal] [Group.IsSolvable (G ⧸ N)]
    [Group.IsPerfect (N ⧸ pCore p N)]
    (hcore : pCore p G ≤ solvableResidual G) : N = solvableResidual G := by
  have hRN : solvableResidual G ≤ N := solvableResidual_le_of_solvable_quotient N
  let R := (solvableResidual G).subgroupOf N
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hRN).symm.surjective
  have hcN : pCore p N ≤ solvableResidual N := by
    apply le_trans (show pCore p N ≤ R from ?_) (le_solvableResidual_of_isPerfect R)
    intro x hx
    apply hcore
    rw [pCore_eq_map_of_normal_of_le p N (hcore.trans hRN)]
    exact mem_map_of_mem N.subtype hx
  let q := QuotientGroup.mk' (pCore p N)
  have hm := map_solvableResidual_eq q (QuotientGroup.mk'_surjective _)
  rw [solvableResidual_eq_top (G := N ⧸ pCore p N)] at hm
  have ht := congrArg (comap q) hm
  rw [comap_map_eq, comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hcN] at ht
  have hN := map_solvableResidual_le N.subtype
  rw [ht, ← MonoidHom.range_eq_map, N.range_subtype] at hN
  exact le_antisymm hN hRN
end Subgroup
