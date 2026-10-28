module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IsPerfect

/-!
# Sylow two-subgroups of perfect groups of even order

Such a Sylow subgroup has order greater than two. Otherwise it is cyclic,
and Burnside transfer for the smallest prime supplies a surjection from the
perfect group onto that abelian Sylow subgroup. The image must be trivial,
contrary to even order and the odd Sylow index.

This gives the strict Sylow size comparison used in Aschbacher–Smith,
Lemma 16.2.12, printed p.1176, without any group-model order calculation.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- Every Sylow two-subgroup of a finite perfect group of even order has
order greater than two. -/
theorem perfect_sylow_two_card_gt_two {M : Type*} [Group M] [Finite M]
    [Group.IsPerfect M] (P : Sylow 2 M) (heven : Even (Nat.card M)) :
    2 < Nat.card P := by
  by_contra! hsmall
  have hdiv : Nat.card P ∣ 2 := by
    have hp : 0 < Nat.card P := Nat.card_pos
    have hc : Nat.card P = 1 ∨ Nat.card P = 2 := by omega
    rcases hc with hc | hc <;> simp [hc]
  let : IsCyclic P := isCyclic_of_card_dvd_prime hdiv
  let : IsMulCommutative P := IsCyclic.isMulCommutative
  have hn : normalizer (P : Set M) ≤ centralizer (P : Set M) :=
    IsCyclic.normalizer_le_centralizer ((Nat.minFac_eq_two_iff _).mpr (even_iff_two_dvd.mp heven))
      (inferInstance : IsCyclic P)
  let f := MonoidHom.transferSylow P hn
  have hb : Function.Bijective (f.domRestrict (P : Subgroup M)) :=
    (MonoidHom.transferSylow_domRestrict_eq_pow P hn).symm ▸
      (P.isPGroup'.powEquiv' P.not_dvd_index).bijective
  have hf : Function.Surjective f := fun y => by
    obtain ⟨x, hx⟩ := hb.surjective y
    exact ⟨x, hx⟩
  let : Group.IsPerfect P := Group.IsPerfect.ofSurjective hf
  have hc : Nat.card P = 1 := Nat.card_unique
  have hi := (P : Subgroup M).card_mul_index
  rw [hc, one_mul] at hi
  exact P.not_dvd_index (hi ▸ even_iff_two_dvd.mp heven)

end Theory.GroupTheory
