module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# A two-group detected by two symmetric-four actions

If a two-group acts faithfully through a pair of homomorphisms to S4,
the first image has order at most eight. Suppose its kernel centralizes an
involution whose second image is outside O2(S4). That image is a transposition,
with centralizer of order four, so the first kernel has order at most four.
The original two-group consequently has order at most 32.

This is the finite action calculation used to exclude large overlaps in
Goldschmidt, *Automorphisms of trivalent graphs* (1980), proof of (4.2).
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricFour.BinaryPairBound
open Theory.SpecificGroups.SymmetricSix.DuadCalculation

private theorem two_subgroup_card_le (P : Subgroup Four) (hp : IsPGroup 2 P) :
    Nat.card P ≤ 8 := by
  have hc : Nat.card Four = 24 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hd : Nat.card P ∣ 24 := hc ▸ P.card_subgroup_dvd_card
  have hcop : (Nat.card P).Coprime 3 := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  exact Nat.le_of_dvd (by decide) (hcop.dvd_mul_left.mp hd)

private theorem outside_involution_cycle : ∀ t : Four, t ^ 2 = 1 → t ∉ core →
    t.cycleType = {2} := by decide +kernel

private theorem outside_involution_centralizer (t : Four) (ht : t ^ 2 = 1) (ho : t ∉ core) :
    Nat.card (centralizer ({t} : Set Four)) = 4 := by
  rw [Equiv.Perm.nat_card_centralizer, outside_involution_cycle t ht ho]
  norm_num [Nat.factorial]

/-- Two faithful degree-four actions, with the first kernel centralizing an
involution whose second image is outside the Klein four core, bound a two-group. -/
theorem card_le_thirtyTwo {T : Type*} [Group T] [Finite T] (hp : IsPGroup 2 T)
    (f g : T →* Four) (hi : Function.Injective (f.prod g))
    (t : T) (ht : t ^ 2 = 1) (ho : g t ∉ core)
    (hc : f.ker ≤ centralizer ({t} : Set T)) : Nat.card T ≤ 32 := by
  let C := centralizer ({g t} : Set Four)
  let k : f.ker →* C := (g.comp f.ker.subtype).codRestrict C (fun x => by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MonoidHom.comp_apply, Subgroup.subtype_apply] using
      congrArg g (mem_centralizer_singleton_iff.mp (hc x.property)))
  have hk : Function.Injective k := by
    intro x y hxy
    apply Subtype.ext
    apply hi
    apply Prod.ext
    · exact (show f (x : T) = 1 from x.property).trans
        (show f (y : T) = 1 from y.property).symm
    · exact congrArg Subtype.val hxy
  have hkcard : Nat.card f.ker ≤ 4 := by
    calc
      Nat.card f.ker ≤ Nat.card C := Nat.card_le_card_of_injective k hk
      _ = 4 := outside_involution_centralizer _ (by rw [← map_pow, ht, map_one]) ho
  have hr : Nat.card f.range ≤ 8 := two_subgroup_card_le f.range (hp.of_surjective
    f.rangeRestrict f.rangeRestrict_surjective)
  have he := f.ker.card_mul_index
  rw [index_ker] at he
  calc
    Nat.card T = Nat.card f.ker * Nat.card f.range := he.symm
    _ ≤ 4 * 8 := Nat.mul_le_mul hkcard hr
    _ = 32 := rfl

end Theory.SpecificGroups.SymmetricFour.BinaryPairBound
