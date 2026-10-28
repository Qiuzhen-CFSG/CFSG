module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Representatives
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.PointRestrictions
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Cubic Sylow bounds in two native M₂₄ centralizers

The five- and seven-parts of the marked mixed-order elements have four and
three nontrivial cycles. Their centralizers act on these cycles. A cubic
element in the action kernel would act trivially on each cycle, since its
order is coprime to the cycle lengths. It would therefore fix at least
twenty points, contradicting the native cubic fixed-point bound of zero or
six. The action kernel has order prime to three, and its image in a symmetric
group of degree at most five has order not divisible by nine.

These bounds are the local inputs for `MixedCoverage`, which proves coverage
of the orders 15 and 21 in the actual Witt-design carrier. The source
application is the M₂₄ paragraph of Guralnick–Malle, Classification of
2F-modules I, Proposition 5.1, manuscript p.17; see also James, The modular
characters of the Mathieu groups, J. Algebra 27 (1973), 57–111.
-/

public section
namespace Sporadic.Mathieu.M24OddCyclic

open Equiv.Perm Subgroup
open Equiv.Perm.OnCycleFactors

private lemma kernel_fixes_support {α : Type*} [Fintype α] [DecidableEq α]
    (f : Equiv.Perm α) (k : centralizer {f})
    (hk : k ∈ (toPermHom f).ker) (hk3 : (k : Equiv.Perm α) ^ 3 = 1)
    (hp : Nat.Coprime 3 (orderOf f)) :
    ∀ x ∈ f.support, (k : Equiv.Perm α) x = x := by
  have hr : (k : Equiv.Perm α) ∈ (kerParam f).range := by
    rw [kerParam_range_eq]
    exact ⟨k, hk, rfl⟩
  obtain ⟨⟨u, v⟩, huv⟩ := hr
  have hcube : (u, v) ^ 3 = 1 := (kerParam_injective f) (by
    rw [map_pow, huv, hk3, map_one])
  have hv : v = 1 := by
    funext c
    have hv3 : v c ^ 3 = 1 := congrArg (fun z => z.2 c) hcube
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hp (orderOf_dvd_of_pow_eq_one hv3)
    apply (orderOf_dvd_natCard (v c)).trans
    rw [Nat.card_zpowers, (mem_cycleFactorsFinset_iff.mp c.property).1.orderOf]
    apply dvd_of_mem_cycleType
    simp only [cycleType_def, Multiset.mem_map]
    exact ⟨c.val, c.property, rfl⟩
  intro x hx
  rw [← huv, hv]
  rw [kerParam_apply]
  split_ifs with hc
  · rfl
  · exact (hc (cycleOf_mem_cycleFactorsFinset_iff.mpr hx)).elim

private noncomputable def cycleAction (a : M24) :
    centralizer ({a} : Set M24) →* Equiv.Perm a.val.cycleFactorsFinset :=
  (toPermHom a.val).comp
    { toFun := fun c => ⟨c.val.val, by
        apply mem_centralizer_singleton_iff.mpr
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

private lemma centralizer_not_nine (a : M24)
    (hp : Nat.Coprime 3 (orderOf a.val))
    (hsupp : 6 < a.val.support.card)
    (hcycles : a.val.cycleFactorsFinset.card ≤ 5) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set M24)) := by
  classical
  let f := cycleAction a
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    intro hd
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 3 hd
    let g : M24 := k.val.val
    have hg : orderOf g = 3 := by
      simpa only [g, Subgroup.orderOf_coe] using hk
    have hfix : ∀ x ∈ a.val.support, g.val x = x := by
      apply kernel_fixes_support a.val ⟨g.val, ?_⟩ ?_ ?_ hp
      · apply mem_centralizer_singleton_iff.mpr
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp k.val.property)
      · exact k.property
      · have h := congrArg (fun z : M24 => z.val) (pow_orderOf_eq_one g)
        simpa only [hg, Subgroup.coe_pow, OneMemClass.coe_one] using h
    have hD : Nat.card (zpowers g) = 3 := (Nat.card_zpowers g).trans hg
    have hb := MathieuCode.m24_odd_prime_point_restriction (zpowers g)
      (by decide : Nat.Prime 3) (by decide : Odd 3) hD
    have hb' : Nat.card (MulAction.fixedPoints (zpowers g) (Fin 24)) ≤ 6 := by
      rcases hb with ⟨_, h | h⟩ | ⟨h, _⟩ <;> omega
    let e : a.val.support → MulAction.fixedPoints (zpowers g) (Fin 24) :=
      fun x => ⟨x.val, fun d => smul_eq_self_of_mem_zpowers d.property (hfix x x.property)⟩
    have hi : Function.Injective e := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : MulAction.fixedPoints (zpowers g) (Fin 24) => z.val) h
    have hc := Nat.card_le_card_of_injective e hi
    rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hc
    omega
  have hrange : Nat.card f.range ∣ 120 := by
    apply (card_subgroup_dvd_card f.range).trans
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe]
    exact Nat.factorial_dvd_factorial hcycles
  have heq : Nat.card f.ker * Nat.card f.range =
      Nat.card (centralizer ({a} : Set M24)) := by
    rw [← Subgroup.index_ker f]
    exact f.ker.card_mul_index
  intro hd
  have hcop : Nat.Coprime 9 (Nat.card f.ker) := by
    exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hker).pow_left 2
  have : 9 ∣ Nat.card f.range := hcop.dvd_of_dvd_mul_left (heq ▸ hd)
  have : 9 ∣ 120 := this.trans hrange
  norm_num at this

/-- The centralizer of the marked order-five element has no factor nine. -/
theorem fivePart_centralizer_not_nine :
    ¬ 9 ∣ Nat.card (centralizer ({representative 0 ^ 3} : Set M24)) := by
  apply centralizer_not_nine
  · rw [Subgroup.orderOf_coe, orderOf_pow, representative_order]
    decide
  · change 6 < (representativePerm 0 ^ 3).support.card
    decide +kernel
  · change (representativePerm 0 ^ 3).cycleFactorsFinset.card ≤ 5
    decide +kernel

/-- The centralizer of the marked order-seven element has no factor nine. -/
theorem sevenPart_centralizer_not_nine :
    ¬ 9 ∣ Nat.card (centralizer ({representative 1 ^ 3} : Set M24)) := by
  apply centralizer_not_nine
  · rw [Subgroup.orderOf_coe, orderOf_pow, representative_order]
    decide
  · change 6 < (representativePerm 1 ^ 3).support.card
    decide +kernel
  · change (representativePerm 1 ^ 3).cycleFactorsFinset.card ≤ 5
    decide +kernel

end Sporadic.Mathieu.M24OddCyclic
