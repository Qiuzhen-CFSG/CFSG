module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# Intersections with a conjugate in an abelian supplement

Suppose a finite abelian subgroup E is U B, with |U ∩ B| = 2. If an
ambient conjugator preserves E and makes B disjoint from its conjugate,
then U meets its conjugate in more than two elements. Write u, b, e for
the three orders. The product formula gives ub = 2e and b² ≤ e. If the
other intersection had order at most two, it would also give u² ≤ 2e.
These inequalities imply 2b ≤ u ≤ b, a contradiction.

Source application: the corrected A₈ point-fixed supplement in
Aschbacher--Smith 12.2.16, printed p.800. This counting argument does not
assume that B is a hyperplane or specify the dimension of U.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A disjoint conjugate supplement forces the other intersection above order two. -/
theorem two_lt_card_inf_conjugate_of_disjoint_supplement
    (E U B : Subgroup G) [IsMulCommutative E]
    (hU : U ≤ E) (hB : B ≤ E) (hs : E = U ⊔ B)
    (hi : Nat.card (U ⊓ B : Subgroup G) = 2)
    (g : G) (hg : g ∈ normalizer (E : Set G))
    (hd : B ⊓ B.map (MulAut.conj g).toMonoidHom = ⊥) :
    2 < Nat.card (U ⊓ U.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
  let f := (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g).injective
  have hE : E.map f = E := mem_normalizer_iff_map_conj_eq.mp hg
  have hUg : U.map f ≤ E := by rw [← hE]; exact map_mono hU
  have hBg : B.map f ≤ E := by rw [← hE]; exact map_mono hB
  have hn (X Y : Subgroup G) (hX : X ≤ E) (hY : Y ≤ E) :
      Y ≤ normalizer (X : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    exact hY.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le hX))
  have he := card_mul_eq_card_inf_mul_card_sup_of_normalizes U B (hn U B hU hB)
  rw [hi, ← hs] at he
  have hb : Nat.card B * Nat.card B ≤ Nat.card E := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes B (B.map f)
      (hn B (B.map f) hB hBg)
    rw [card_map_of_injective hf, hd, card_bot, one_mul] at hh
    exact hh.le.trans (card_le_of_le (sup_le hB hBg))
  have hu : Nat.card U * Nat.card U ≤
      Nat.card (U ⊓ U.map f : Subgroup G) * Nat.card E := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes U (U.map f)
      (hn U (U.map f) hU hUg)
    rw [card_map_of_injective hf] at hh
    exact hh.le.trans (Nat.mul_le_mul_left _ (card_le_of_le (sup_le hU hUg)))
  have hbpos : 0 < Nat.card B := Nat.card_pos
  have hupos : 0 < Nat.card U := Nat.card_pos
  have hbU : 2 * Nat.card B ≤ Nat.card U := by
    exact Nat.le_of_mul_le_mul_right (by nlinarith [Nat.mul_le_mul_left 2 hb]) hbpos
  change 2 < Nat.card (U ⊓ U.map f : Subgroup G)
  by_contra hnot
  have hsmall : Nat.card (U ⊓ U.map f : Subgroup G) ≤ 2 := by omega
  have huB : Nat.card U ≤ Nat.card B := by
    exact Nat.le_of_mul_le_mul_left
      (by nlinarith [Nat.mul_le_mul_right (Nat.card E) hsmall]) hupos
  omega
end Subgroup
