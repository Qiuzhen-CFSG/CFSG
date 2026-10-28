module

public import Theory.GroupTheory.NormalProductCoordinate
public import Theory.Alternating.Aut
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Proper normal quotients of the direct-factor models

A group with a simple normal subgroup, trivial centralizer of that subgroup,
and a 2-group quotient has only 2-groups as nontrivial normal quotients.
This applies to symmetric groups of degree at least five. The S3 case follows
from its order six and the fact that a normal subgroup of order two would be
central. Simple groups supply the remaining case directly.

These literal model statements discharge the normal-homomorphism condition in
the coordinate-rigidity argument for the two-factor B.5.6 source branch.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace Theory.GroupTheory
variable {H : Type*} [Group H]

theorem simple_normal_quotient_two [IsSimpleGroup H]
    (N : Subgroup H) [N.Normal] (hn : N ≠ ⊥) : IsPGroup 2 (H ⧸ N) := by
  have he : N = ⊤ := (inferInstance : N.Normal).eq_bot_or_eq_top.resolve_left hn
  subst N
  have hall (x : H ⧸ (⊤ : Subgroup H)) : x = 1 := by
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (⊤ : Subgroup H) x
    exact (QuotientGroup.eq_one_iff g).mpr (mem_top g)
  let : Subsingleton (H ⧸ (⊤ : Subgroup H)) := ⟨fun x y => (hall x).trans (hall y).symm⟩
  exact IsPGroup.of_subsingleton 2 _

theorem normal_quotient_two_of_simple_monolith (L : Subgroup H) [L.Normal]
    [IsSimpleGroup L] (hc : centralizer (L : Set H) = ⊥)
    (hq : IsPGroup 2 (H ⧸ L))
    (N : Subgroup H) [N.Normal] (hn : N ≠ ⊥) : IsPGroup 2 (H ⧸ N) := by
  have hle : L ≤ N := by
    rcases (inferInstance : (N.subgroupOf L).Normal).eq_bot_or_eq_top with hz | ht
    · have hd := subgroupOf_eq_bot.mp hz
      have hcomm : ⁅N,L⁆ = ⊥ := bot_unique ((commutator_le_inf N L).trans (hd inf_le_left inf_le_right))
      have hNC : N ≤ centralizer (L : Set H) := commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact (hn (le_bot_iff.mp (hc ▸ hNC))).elim
    · exact subgroupOf_eq_top.mp ht
  exact hq.of_surjective (QuotientGroup.map L N (MonoidHom.id H) hle)
    (QuotientGroup.map_surjective_of_surjective L N (MonoidHom.id H) (QuotientGroup.mk_surjective) hle)

theorem symmetric_normal_quotient_two {n : ℕ} (hn : 5 ≤ n)
    (N : Subgroup (Equiv.Perm (Fin n))) [N.Normal] (hne : N ≠ ⊥) :
    IsPGroup 2 ((Equiv.Perm (Fin n)) ⧸ N) := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
  apply normal_quotient_two_of_simple_monolith (alternatingGroup (Fin n))
    (GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot n (by omega)) ?_ N hne
  apply IsPGroup.of_card (n := 1)
  change (alternatingGroup (Fin n)).index = 2 ^ 1
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  simp [alternatingGroup.index_eq_two]

theorem symmetric_three_normal_quotient_two
    (N : Subgroup (Equiv.Perm (Fin 3))) [N.Normal] (hne : N ≠ ⊥) :
    IsPGroup 2 ((Equiv.Perm (Fin 3)) ⧸ N) := by
  have hNcard : Nat.card N ∣ 6 := by simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using N.card_subgroup_dvd_card
  have hNnot : Nat.card N ≠ 1 := fun h => hne (card_eq_one.mp h)
  have hNnot2 : Nat.card N ≠ 2 := by
    intro h
    have hc := central_of_normal_card_two N h
    have hz : center (Equiv.Perm (Fin 3)) = ⊥ := by
      apply (eq_bot_iff_forall _).mpr
      exact by decide
    exact hne (le_bot_iff.mp (hz ▸ hc))
  apply IsPGroup.of_card_dvd_pow (n := 1)
  have hc := N.index_mul_card
  have hpos := Nat.card_pos (α := N)
  have hle : Nat.card N ≤ 6 := Nat.le_of_dvd (by decide) hNcard
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hcard] at hc
  change N.index ∣ 2 ^ 1
  have hcases : Nat.card N = 3 ∨ Nat.card N = 6 := by
    interval_cases hk : Nat.card N <;> omega
  rcases hcases with h3 | h6
  · rw [h3] at hc
    have he : N.index = 2 := by omega
    simp [he]
  · rw [h6] at hc
    have he : N.index = 1 := by omega
    simp [he]
end Theory.GroupTheory
