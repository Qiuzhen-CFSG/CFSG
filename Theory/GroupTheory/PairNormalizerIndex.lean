module
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Order.Atoms

/-!
# The normalizer index of a moved subgroup in an invariant pair

If every element of M carries Q into a fixed pair {Q,W}, and one element
moves Q, its relative normalizer has index two. The proof identifies the
two cosets directly. A maximal subgroup of M contained in this normalizer
must therefore be the full stabilizer and also have index two.

Source application: Aschbacher–Smith, C.5.6(5),(6) and C.5.7, pp.157–160.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- An invariant pair moved by M gives a normalizer of index two in M. -/
theorem normalizer_relIndex_eq_two_of_pair (M Q W : Subgroup G)
    (hpair : ∀ m ∈ M, Q.map (MulAut.conj m).toMonoidHom = Q ∨
      Q.map (MulAut.conj m).toMonoidHom = W)
    (x : G) (hx : x ∈ M) (hmove : Q.map (MulAut.conj x).toMonoidHom ≠ Q) :
    (normalizer (Q : Set G)).relIndex M = 2 := by
  have hxW := (hpair x hx).resolve_left hmove
  have hd : (normalizer (Q : Set G)).relIndex M ∣ 2 := by
    apply relIindex_dvd_two_iff'.mpr
    refine ⟨x⁻¹, M.inv_mem hx, ?_⟩
    intro b hb
    rcases hpair b hb with hfix | hswap
    · exact Or.inr (mem_normalizer_iff_map_conj_eq.mpr hfix)
    · left
      apply mem_normalizer_iff_map_conj_eq.mpr
      change Q.map (MulAut.conj (x⁻¹ * b)).toMonoidHom = Q
      have he : (MulAut.conj (x⁻¹ * b)).toMonoidHom =
          (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
        ext a
        simp [MulAut.conj_apply, mul_assoc]
      rw [he, ← map_map, hswap, ← hxW, map_map]
      have hc : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id G := by
        ext a
        simp [MulAut.conj_apply, mul_assoc]
      rw [hc, map_id]
  exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (fun he =>
    hmove (mem_normalizer_iff_map_conj_eq.mp (relIndex_eq_one.mp he hx)))

/-- A coatom contained in the stabilizer of a moved pair is that stabilizer. -/
theorem coatom_eq_pair_normalizer (M H Q W : Subgroup G) (hHM : H ≤ M)
    (hmax : IsCoatom (H.subgroupOf M)) (hHQ : H ≤ normalizer (Q : Set G))
    (hpair : ∀ m ∈ M, Q.map (MulAut.conj m).toMonoidHom = Q ∨
      Q.map (MulAut.conj m).toMonoidHom = W)
    (x : G) (hx : x ∈ M) (hmove : Q.map (MulAut.conj x).toMonoidHom ≠ Q) :
    H = M ⊓ normalizer (Q : Set G) ∧ H.relIndex M = 2 := by
  have hle : H.subgroupOf M ≤ (normalizer (Q : Set G)).subgroupOf M :=
    subgroupOf_mono M hHQ
  have hne : (normalizer (Q : Set G)).subgroupOf M ≠ ⊤ := by
    intro he
    have hh : (⟨x, hx⟩ : M) ∈ (normalizer (Q : Set G)).subgroupOf M := he ▸ mem_top _
    exact hmove (mem_normalizer_iff_map_conj_eq.mp hh)
  have heq : H.subgroupOf M = (normalizer (Q : Set G)).subgroupOf M := by
    by_contra hn
    exact hne (hmax.2 _ (lt_of_le_of_ne hle hn))
  have he : H = M ⊓ normalizer (Q : Set G) := by
    apply le_antisymm (le_inf hHM hHQ)
    intro y hy
    have hh : (⟨y, hy.1⟩ : M) ∈ H.subgroupOf M := heq.symm ▸ hy.2
    exact hh
  refine ⟨he, ?_⟩
  change (H.subgroupOf M).index = 2
  rw [heq]
  exact normalizer_relIndex_eq_two_of_pair M Q W hpair x hx hmove
end Subgroup
end
