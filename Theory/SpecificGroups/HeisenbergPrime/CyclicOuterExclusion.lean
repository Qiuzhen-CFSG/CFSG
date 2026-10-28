module
public import Theory.SpecificGroups.HeisenbergPrime
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic kernels obstruct ternary Heisenberg actions

Every cyclic subgroup or cyclic image of the exponent-three Heisenberg group
has order at most three. A homomorphism cannot have both cyclic kernel and
cyclic image, since their orders multiply to 27. Consequently the group
cannot act faithfully on a centerless finite group whose inner and outer
three-subgroups are cyclic. Odd-prime rank at most one supplies that cyclicity.

Source application: the rank-one rows of the automorphism exclusions in
Aschbacher–Smith 14.7.26, printed p.1053 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace HeisenbergPrime

/-- The ternary Heisenberg group is not cyclic by cyclic. -/
theorem no_cyclic_kernel_range {D : Type*} [Group D]
    (f : HeisenbergPrime 3 →* D) [IsCyclic f.ker] [IsCyclic f.range] : False := by
  have hk : Nat.card f.ker ≤ 3 := by
    apply Nat.le_of_dvd (by decide)
    rw [←IsCyclic.exponent_eq_card]
    exact (Monoid.exponent_dvd_of_monoidHom f.ker.subtype f.ker.subtype_injective).trans
      (dvd_of_eq (HeisenbergPrime.exponent (by decide : 3 ≠ 2)))
  have hr : Nat.card f.range ≤ 3 := by
    apply Nat.le_of_dvd (by decide)
    rw [←IsCyclic.exponent_eq_card]
    exact (MonoidHom.exponent_dvd f.rangeRestrict_surjective).trans
      (dvd_of_eq (HeisenbergPrime.exponent (by decide : 3 ≠ 2)))
  have hc : Nat.card (HeisenbergPrime 3) = Nat.card f.ker * Nat.card f.range := by
    rw [←index_ker,f.ker.card_mul_index]
  rw [HeisenbergPrime.card] at hc
  nlinarith

private theorem cyclic_three_subgroup {D : Type*} [Group D] [Finite D]
    (hr : primeRank 3 D ≤ 1) (P : Subgroup D) (hP : IsPGroup 3 P) : IsCyclic P := by
  obtain ⟨S,hS⟩ := hP.exists_le_sylow
  let := S.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  exact isCyclic_of_injective (inclusion hS) (inclusion_injective hS)

/-- Cyclic inner and outer three-subgroups exclude a faithful Heisenberg action. -/
theorem no_faithful_action_of_rank_one {Q : Type*} [Group Q] [Finite Q]
    (hz : center Q = ⊥) (hQ : primeRank 3 Q ≤ 1)
    (ho : primeRank 3 (MulAut.Outer Q) ≤ 1)
    (f : HeisenbergPrime 3 →* MulAut Q) (hf : Function.Injective f) : False := by
  have hP : IsPGroup 3 (HeisenbergPrime 3) := IsPGroup.of_card (HeisenbergPrime.card (p := 3))
  let q := QuotientGroup.mk' (MulAut.innerSubgroup Q)
  let g := q.comp f
  let j : g.ker →* MulAut.innerSubgroup Q := (f.comp g.ker.subtype).codRestrict _
    (fun x => (QuotientGroup.eq_one_iff (f x.val)).mp x.property)
  have hj : Function.Injective j := fun _ _ hh =>
    Subtype.ext (hf (congrArg Subtype.val hh))
  let ei : Q ≃* MulAut.innerSubgroup Q :=
    MonoidHom.ofInjective (Theory.GroupTheory.conj_injective_of_center_eq_bot hz)
  let k := ei.symm.toMonoidHom.comp j
  have hk : Function.Injective k := ei.symm.injective.comp hj
  have hkr : IsPGroup 3 k.range := (hP.to_subgroup g.ker).of_surjective
    k.rangeRestrict k.rangeRestrict_surjective
  let := cyclic_three_subgroup hQ k.range hkr
  let : IsCyclic g.ker := isCyclic_of_injective k.rangeRestrict
    ((MonoidHom.rangeRestrict_injective_iff).mpr hk)
  let : IsCyclic g.range := cyclic_three_subgroup ho g.range
    (hP.of_surjective g.rangeRestrict g.rangeRestrict_surjective)
  exact no_cyclic_kernel_range g
end HeisenbergPrime
