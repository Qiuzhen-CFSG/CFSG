module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Sylow

/-!
# Transpositions are not two-central in S5 and S8

A transposition centralizer has order 2(n-2)!. Its two-part is smaller than
that of n! at n=5 and n=8, so no full Sylow two-subgroup centralizes it. The
transport theorem preserves the given group isomorphism and original Sylow.

Source application: Aschbacher–Smith G.6.4(4), printed p.346.
-/

public section
open Subgroup
namespace Equiv.Perm

theorem isSwap_not_twoCentral {n : ℕ} (hn : n = 5 ∨ n = 8)
    (a : Perm (Fin n)) (ha : a.IsSwap) (S : Sylow 2 (Perm (Fin n)))
    (hz : a ∈ (center S).map (S : Subgroup (Perm (Fin n))).subtype) : False := by
  obtain ⟨z,hz,rfl⟩ := hz
  have hSC : (S : Subgroup (Perm (Fin n))) ≤ centralizer ({(z : Perm (Fin n))} : Set _) := by
    intro s hs
    apply mem_centralizer_iff.mpr
    rintro x (rfl : x = (z : Perm (Fin n)))
    exact (congrArg Subtype.val (mem_center_iff.mp hz (⟨s,hs⟩ : S))).symm
  have hc := nat_card_centralizer (z : Perm (Fin n))
  have hcycle : (z : Perm (Fin n)).cycleType = {2} := isSwap_iff_cycleType.mp ha
  rw [hcycle] at hc
  have hg : Nat.card (Perm (Fin n)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rcases hn with rfl | rfl
  · have hp := S.pow_dvd_card_of_pow_dvd_card (n := 3) (by rw [hg]; norm_num [Nat.factorial])
    have hd := hp.trans (card_dvd_of_le hSC)
    rw [hc] at hd
    norm_num [Nat.factorial] at hd
  · have hp := S.pow_dvd_card_of_pow_dvd_card (n := 7) (by rw [hg]; norm_num [Nat.factorial])
    have hd := hp.trans (card_dvd_of_le hSC)
    rw [hc] at hd
    norm_num [Nat.factorial] at hd

/-- The original Sylow condition transported through a specified symmetric model. -/
theorem not_twoCentral_of_isSwap_model
    {G : Type*} [Group G] {n : ℕ} (hn : n = 5 ∨ n = 8)
    (e : G ≃* Perm (Fin n)) (a : G) (ha : (e a).IsSwap)
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) : False := by
  let : Finite G := Finite.of_injective e e.injective
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  apply isSwap_not_twoCentral hn (e a) ha P
  obtain ⟨z,hz,rfl⟩ := hz
  let z' : P := ⟨e z,by
    change e z ∈ (S : Subgroup G).map e.toMonoidHom
    exact mem_map_of_mem e.toMonoidHom z.property⟩
  refine ⟨z',?_,rfl⟩
  apply mem_center_iff.mpr
  intro s
  have hs := s.property
  change (s : Perm (Fin n)) ∈ (S : Subgroup G).map e.toMonoidHom at hs
  obtain ⟨x,hx,hxs⟩ := hs
  change e x = (s : Perm (Fin n)) at hxs
  apply Subtype.ext
  change (s : Perm (Fin n)) * e z = e z * s
  rw [← hxs, ← map_mul, ← map_mul]
  exact congrArg e (congrArg Subtype.val (mem_center_iff.mp hz (⟨x,hx⟩ : S)))
end Equiv.Perm
