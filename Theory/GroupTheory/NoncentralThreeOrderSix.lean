module

public import Theory.GroupTheory.DihedralPresentation
public import Theory.GroupTheory.OddInvolutionEndpointModels
public import Theory.GroupTheory.PrimeSubgroupInvolution
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

/-!
# A noncentral cubic element in a group of order six

A Cauchy involution and the given cubic generate the whole group by order.
The cubic subgroup has index two, so the involution centralizes or inverts
it. Noncentrality excludes the first case and the dihedral presentation
identifies the actual group with S₃.

This supplies the order-six factor in the literal J₃ overlap normalizer.
-/

public noncomputable section

open Subgroup
namespace Theory.GroupTheory

/-- A group of order six with a specified noncentral cubic element is S₃. -/
theorem nonempty_perm_three_of_card_six_noncentral_three
    {H : Type*} [Group H] [Finite H] (hcard : Nat.card H = 6)
    (c : H) (hc : orderOf c = 3) (hn : c ∉ center H) :
    Nonempty (H ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := H) 2
    (hcard ▸ (by decide : 2 ∣ 6))
  have hgen : closure ({c, t} : Set H) = ⊤ := by
    apply eq_top_of_card_eq
    apply Nat.dvd_antisymm
    · exact card_subgroup_dvd_card _
    · rw [hcard]
      apply (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd
      · simpa only [orderOf_mk, ht] using
          orderOf_dvd_natCard (⟨t, subset_closure (by simp)⟩ : closure ({c, t} : Set H))
      · simpa only [orderOf_mk, hc] using
          orderOf_dvd_natCard (⟨c, subset_closure (by simp)⟩ : closure ({c, t} : Set H))
  have hi : (zpowers c).index = 2 := by
    have hh := (zpowers c).card_mul_index
    rw [Nat.card_zpowers, hc, hcard] at hh
    omega
  let : (zpowers c).Normal := normal_of_index_eq_two hi
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hinv : t * c * t⁻¹ = c⁻¹ := by
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one (zpowers c)
      (by rw [Nat.card_zpowers, hc]; decide) t ht2
      (le_normalizer_of_normal (mem_top t)) with hh | hh
    · apply False.elim
      apply hn
      have htop : centralizer ({c} : Set H) = ⊤ := by
        apply top_unique
        rw [← hgen]
        apply (closure_le _).mpr
        intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hx
        · exact mem_centralizer_singleton_iff.mpr rfl
        · rw [Set.mem_singleton_iff.mp hx]
          exact mem_centralizer_singleton_iff.mpr (hh c (mem_zpowers c)).eq
      apply mem_center_iff.mpr
      intro x
      exact mem_centralizer_singleton_iff.mp (htop ▸ mem_top x)
    · exact hh c (mem_zpowers c)
  obtain ⟨e⟩ := dihedralGroup_equiv_of_presentation (by decide) c t hc ht2 hinv hgen hcard
  obtain ⟨d⟩ := nonempty_dihedralThreeEquivPerm
  exact ⟨e.trans d⟩

end Theory.GroupTheory
