module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.ThreeElements
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import Theory.GroupTheory.CommutingFactorsOddRank
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Perfect subgroups fix the short-block conjugacy family

Distinct commuting conjugates of a short block contribute independent
three-elements: its center is a two-group. The ambient three-rank bound
therefore allows at most two conjugates. The normalizer has index at most
two, so every perfect subgroup lies in it.

The proof retains the literal conjugate subgroups and uses the checked
commuting-factor rank inequality. Block commutation remains an explicit
premise here; the assembly module supplies exact C.1.9 with its core
condition discharged.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–9,
printed p.123, and the commuting-conjugate arguments in E.6.14 and E.6.23,
printed pp.251 and 254–255.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
open InvariantSubspaces.BlockSelection

/-- A short group with a three-element has at most two commuting conjugates
in three-rank at most two. Thus every perfect subgroup normalizes it. -/
theorem perfect_normalizes_of_commuting_three_conjugates {G : Type*} [Group G] [Finite G]
    (B X : Subgroup G) [Group.IsPerfect X] (hB : ChapterC.IsShort B)
    (ha : ∃ a : B, orderOf a = 3) (hr : primeRank 3 G ≤ 2)
    (hc : ∀ g h : G,
      B.map (MulAut.conj g).toMonoidHom ≠ B.map (MulAut.conj h).toMonoidHom →
      ⁅B.map (MulAut.conj g).toMonoidHom, B.map (MulAut.conj h).toMonoidHom⁆ = ⊥) :
    X ≤ normalizer (B : Set G) := by
  apply le_of_isPerfect_of_index_le_two
  rw [← ncard_conjugates_eq_index_normalizer]
  classical
  by_contra hn
  obtain ⟨A, C, D, ⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff).mp (Nat.lt_of_not_ge hn)
  let g : Fin 3 → G := ![a, b, c]
  let F : Fin 3 → Subgroup G := fun i => B.map (MulAut.conj (g i)).toMonoidHom
  have hF : Function.Injective F := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [F, g]
  have hcomm : Pairwise fun i j => F i ≤ centralizer (F j : Set G) := by
    intro i j hij
    exact commutator_eq_bot_iff_le_centralizer.mp
      (hc (g i) (g j) (fun he => hij (hF he)))
  let e (i : Fin 3) : B ≃* F i := (MulAut.conj (g i)).subgroupMap B
  have hz (i : Fin 3) : IsPGroup 2 (center (F i)) :=
    (center_isTwoGroup hB).of_equiv (centerCongr (e i))
  obtain ⟨x, hx⟩ := ha
  have hx' (i : Fin 3) : orderOf (e i x) = 3 := (e i).orderOf_eq x |>.trans hx
  have hl := card_le_primeRank_of_commuting_factors F (by decide : Odd 3)
    hcomm hz (fun i => e i x) hx'
  have hh : Fintype.card (Fin 3) = 3 := Fintype.card_fin _
  omega

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.CharacteristicTwoBlocks
