module

public import Theory.GroupTheory.Commutator.CoprimeQuadratic
public import Theory.GroupTheory.Commutator.NilpotentSaturation
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The nilpotent A × B lemma

A coprime actor Q normalizes B and centralizes P. If B and P lie in a
nilpotent subgroup T, then fixing C_B(P) forces Q to fix B. Induction on
|B| descends to [B,P], which is proper by nilpotent commutator saturation.
The three-subgroups lemma and coprime commutator idempotence finish the
induction. No faithfulness of the original action is required.

For Y ≤ X nilpotent, this identifies the kernels of an action on X and on
C_X(Y) whenever the actor centralizes Y. This is the reusable content of
Aschbacher–Smith, *The Classification of Quasithin Groups*, G.8.4,
printed p.349 (combined manuscript, 1 March 2004).
-/

namespace Subgroup

/-- The coprime A × B centralizer lemma with both the target and the
internal actor contained in a nilpotent subgroup. -/
public theorem nilpotent_a_times_b_centralizer
    {G : Type*} [Group G] [Finite G]
    (T B P Q : Subgroup G) (hT : Group.IsNilpotent T)
    (hBT : B ≤ T) (hPT : P ≤ T)
    (hPB : P ≤ normalizer (B : Set G))
    (hQB : Q ≤ normalizer (B : Set G))
    (hPQ : ⁅P, Q⁆ = ⊥)
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card B))
    (hfixed : B ⊓ centralizer (P : Set G) ≤ centralizer (Q : Set G)) :
    ⁅B, Q⁆ = ⊥ := by
  classical
  induction hcard : Nat.card B using Nat.strong_induction_on generalizing B with
  | h n ih =>
    by_cases hBbot : B = ⊥
    · simp [hBbot]
    let U := ⁅B, P⁆
    have hUB : U ≤ B := le_normalizer_iff_commutator_le_left.mp hPB
    have hUlt : U < B := by
      refine lt_of_le_of_ne hUB ?_
      intro heq
      apply hBbot
      apply bot_unique
      apply le_of_le_sup_commutator_of_isNilpotent T B ⊥ P hT hBT bot_le hPT
        (le_normalizer_of_normal)
      simpa only [bot_sup_eq] using heq.ge
    have hUcard : Nat.card U < n := by
      rw [← hcard]
      exact lt_of_le_of_ne (card_le_of_le hUB)
        (fun heq => hUlt.ne (eq_of_le_of_card_ge hUB heq.ge))
    have hPU : P ≤ normalizer (U : Set G) := normalizer_commutator_ge_right B P
    have hQP : Q ≤ normalizer (P : Set G) := by
      apply le_trans _ (centralizer_le_normalizer _)
      apply commutator_eq_bot_iff_le_centralizer.mp
      rwa [commutator_comm]
    have hQU : Q ≤ normalizer (U : Set G) := by
      intro q hq
      rw [mem_normalizer_iff_map_conj_eq, map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (hQB hq),
        mem_normalizer_iff_map_conj_eq.mp (hQP hq)]
    have hUQ : ⁅U, Q⁆ = ⊥ := ih (Nat.card U) hUcard U (hUB.trans hBT) hPU hQU
      (hcop.of_dvd_right (card_dvd_of_le hUB))
      ((inf_le_inf_right _ hUB).trans hfixed) rfl
    have hPQB : ⁅⁅P, Q⁆, B⁆ = ⊥ := by simp [hPQ]
    have hQBP : ⁅⁅Q, B⁆, P⁆ = ⊥ :=
      commutator_commutator_eq_bot_of_rotate hUQ hPQB
    have hBQcentP : ⁅B, Q⁆ ≤ centralizer (P : Set G) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      simpa only [commutator_comm B Q] using hQBP
    have hBQleB : ⁅B, Q⁆ ≤ B := le_normalizer_iff_commutator_le_left.mp hQB
    have hdouble : ⁅⁅B, Q⁆, Q⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        ((le_inf hBQleB hBQcentP).trans hfixed)
    let : Group.IsNilpotent T := hT
    have hBnil : Group.IsNilpotent B :=
      isNilpotent_of_ker_le_center (inclusion hBT) (by
        rw [(MonoidHom.ker_eq_bot_iff _).mpr (inclusion_injective hBT)]
        exact bot_le)
    let : Group.IsNilpotent B := hBnil
    exact commutator_eq_bot_of_coprime_quadratic B Q hQB inferInstance hcop hdouble

/-- An actor centralizing Y has the same kernel on a nilpotent X and on
C_X(Y), provided its order is coprime to |X|. -/
public theorem nilpotent_centralizer_restriction_kernel
    {G : Type*} [Group G] [Finite G]
    (X Y P : Subgroup G) (hX : Group.IsNilpotent X) (hYX : Y ≤ X)
    (hPX : P ≤ normalizer (X : Set G))
    (hPY : P ≤ centralizer (Y : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card X)) :
    P ⊓ centralizer (X ⊓ centralizer (Y : Set G) : Set G) =
      P ⊓ centralizer (X : Set G) := by
  let C := P ⊓ centralizer (X ⊓ centralizer (Y : Set G) : Set G)
  have hCP : C ≤ P := inf_le_left
  have hYC : ⁅Y, C⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hCP.trans hPY)
  have hfix : X ⊓ centralizer (Y : Set G) ≤ centralizer (C : Set G) := by
    intro x hx c hc
    exact (hc.2 x hx).symm
  have hXC := nilpotent_a_times_b_centralizer X X Y C hX le_rfl hYX
    (hYX.trans X.le_normalizer) (hCP.trans hPX) hYC
    (hcop.of_dvd_left (card_dvd_of_le hCP)) hfix
  apply le_antisymm
  · exact le_inf hCP (commutator_eq_bot_iff_le_centralizer.mp
      (by simpa only [commutator_comm] using hXC))
  · exact inf_le_inf_left _ (centralizer_le inf_le_left)

end Subgroup
