module
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.Frattini.NormalImage
import Mathlib.Tactic

/-!
# A characteristic cubic in a small abelian three-group

An elementary subgroup of order 27 lies in the kernel of cubing. If the
ambient abelian three-group has order at most 81, the cube image has order
at most three. Non-elementarity makes it nontrivial. This image is the
Frattini subgroup, hence characteristic, and it is normal in every ambient
group in which the original three-group is normal.

Source application: Aschbacher--Smith G.9.4, printed p.355, abelian
high-rank three-core branch.
-/

open Subgroup
namespace Theory.GroupTheory.AbelianThreeCubic
open scoped IsMulCommutative

/-- Cubing produces a characteristic subgroup of order three. -/
public theorem frattini_card_three
    {B : Type*} [Group B] [Finite B] [IsMulCommutative B]
    (hB : IsPGroup 3 B) (hcard : Nat.card B ≤ 81)
    (E : Subgroup B) [IsElementaryAbelian 3 E] (hE : Nat.card E = 27)
    (hne : ¬ IsElementaryAbelian 3 B) : Nat.card (frattini B) = 3 := by
  let : CommGroup B := IsMulCommutative.instCommGroup
  let f : B →* B := powMonoidHom 3
  have hEk : E ≤ f.ker := by
    intro x hx
    exact elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) x hx
  have hk : 27 ≤ Nat.card f.ker :=
    Nat.le_of_dvd Nat.card_pos (hE ▸ card_dvd_of_le hEk)
  have hprod := f.ker.card_mul_index
  rw [index_ker] at hprod
  have hrle : Nat.card f.range ≤ 3 := by nlinarith
  have hrne : f.range ≠ ⊥ := by
    intro hz
    apply hne
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    have hx : f x ∈ f.range := ⟨x,rfl⟩
    rw [hz,mem_bot] at hx
    exact hx
  have hrpos := f.range.one_lt_card_iff_ne_bot.mpr hrne
  obtain ⟨n,hn⟩ := (hB.to_subgroup f.range).exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra hh
    have hp : 9 ≤ 3 ^ n := by
      simpa only [show (3:ℕ)^2=9 by decide] using
        Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 2 ≤ n)
    rw [← hn] at hp
    omega
  have hn1 : n = 1 := by
    have hn0 : n ≠ 0 := by
      intro hz
      have hh : Nat.card f.range = 1 := by simpa [hz] using hn
      omega
    omega
  rw [← IsPGroup.pow_range_eq_frattini hB]
  change Nat.card f.range = 3
  simpa only [hn1,pow_one] using hn

/-- The cubic Frattini subgroup of a normal abelian three-group is normal
in the original ambient group, with its literal inclusion retained. -/
public theorem exists_normal_cubic
    {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) [B.Normal] [IsMulCommutative B]
    (hB : IsPGroup 3 B) (hcard : Nat.card B ≤ 81)
    (E : Subgroup B) [IsElementaryAbelian 3 E] (hE : Nat.card E = 27)
    (hne : ¬ IsElementaryAbelian 3 B) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C = 3 ∧ C ≤ B := by
  refine ⟨(frattini B).map B.subtype,inferInstance,?_,map_subtype_le _⟩
  rw [card_map_of_injective B.subtype_injective]
  exact frattini_card_three hB hcard E hE hne

end Theory.GroupTheory.AbelianThreeCubic
