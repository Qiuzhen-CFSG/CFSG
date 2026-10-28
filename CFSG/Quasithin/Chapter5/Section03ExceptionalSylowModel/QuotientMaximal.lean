module

public import Theory.SpecificGroups.PSL3Four.SylowModel
public import Theory.SpecificGroups.PSL3Four.SylowModel.QuaternionCoordinates
public import CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel.SubgroupGeometry
public import Mathlib.Tactic.LinearCombination

/-!
# Maximal elementary abelian subgroups of the central quotient

The two root coordinates and their commutator determinant bound elementary
subgroups inside `S`; outside `S`, the exponent-two quotient forces both root
coordinates into the trace kernel `Q`.  The quotient image `Qbar` therefore has
order sixteen and is the unique maximal elementary abelian subgroup of that
order.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.7,
printed pp. 660--661 (PDF pp. 677--678).
-/

@[expose] public section
open Matrix.PSL3Four
namespace Matrix.PSL3Four.SylowModel
noncomputable section

private theorem det_fixed (W : Subgroup T)
    [IsElementaryAbelian 2 (W.map quotient)] (hS : W ≤ S)
    (a b : W) : fieldFrobenius (a.val.left.x * b.val.left.y -
      b.val.left.x * a.val.left.y) =
      a.val.left.x * b.val.left.y - b.val.left.x * a.val.left.y := by
  have hab : quotient (a.val * b.val) = quotient (b.val * a.val) := by
    rw [map_mul, map_mul]
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := W.map quotient)).comm
      ⟨quotient a.val, ⟨a.val, a.property, rfl⟩⟩
      ⟨quotient b.val, ⟨b.val, b.property, rfl⟩⟩)
  let d := (a.val * b.val) * (b.val * a.val)⁻¹
  have hd : d ∈ C := (QuotientGroup.eq_one_iff d).mp (by
    change quotient ((a.val * b.val) * (b.val * a.val)⁻¹) = 1
    rw [map_mul, map_inv, hab, mul_inv_cancel])
  have hc : fieldFrobenius d.left.c = d.left.c := by
    rcases (mem_C_iff d).mp hd with h | h <;> simp [h, z, inclusion, central]
  have he : d * (b.val * a.val) = a.val * b.val := by
    dsimp [d]
    exact inv_mul_cancel_right _ _
  have hz := (mem_Z d).mp (C_le_Z hd)
  have h := congrArg (fun t : T => t.left.c) he
  simp only [SemidirectProduct.mul_left, hz.1, (mem_S _).mp (hS a.property),
    (mem_S _).mp (hS b.property), map_one, MulAut.one_apply, mul_c, hz.2.1,
    zero_mul, add_zero] at h
  have heq : a.val.left.x * b.val.left.y - b.val.left.x * a.val.left.y = d.left.c := by
    linear_combination -h
  rw [heq]
  exact hc

private theorem card_lift_inside (W : Subgroup T)
    [IsElementaryAbelian 2 (W.map quotient)] (hS : W ≤ S) : Nat.card W ≤ 16 := by
  by_cases hdet : ∃ a b : W, a.val.left.x * b.val.left.y - b.val.left.x * a.val.left.y ≠ 0
  · obtain ⟨a, b, hab⟩ := hdet
    let f : W → PrimeField × PrimeField × F := fun u =>
      (⟨a.val.left.x * u.val.left.y - u.val.left.x * a.val.left.y,
        det_fixed W hS a u⟩,
       ⟨b.val.left.x * u.val.left.y - u.val.left.x * b.val.left.y,
        det_fixed W hS b u⟩, u.val.left.c)
    have hf : Function.Injective f := by
      intro u v huv
      have h₁ := congrArg (fun p : PrimeField × PrimeField × F => p.1.val) huv
      have h₂ := congrArg (fun p : PrimeField × PrimeField × F => p.2.1.val) huv
      have h₃ := congrArg (fun p : PrimeField × PrimeField × F => p.2.2) huv
      change a.val.left.x * u.val.left.y - u.val.left.x * a.val.left.y =
        a.val.left.x * v.val.left.y - v.val.left.x * a.val.left.y at h₁
      change b.val.left.x * u.val.left.y - u.val.left.x * b.val.left.y =
        b.val.left.x * v.val.left.y - v.val.left.x * b.val.left.y at h₂
      have hx : (a.val.left.x * b.val.left.y - b.val.left.x * a.val.left.y) *
          (u.val.left.x - v.val.left.x) = 0 := by
        linear_combination b.val.left.x * h₁ - a.val.left.x * h₂
      have hy : (a.val.left.x * b.val.left.y - b.val.left.x * a.val.left.y) *
          (u.val.left.y - v.val.left.y) = 0 := by
        linear_combination b.val.left.y * h₁ - a.val.left.y * h₂
      apply Subtype.ext
      apply SemidirectProduct.ext
      · exact U.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hab))
          (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hab)) h₃
      · exact ((mem_S _).mp (hS u.property)).trans ((mem_S _).mp (hS v.property)).symm
    have hcard := Nat.card_le_card_of_injective f hf
    simpa only [Nat.card_prod, card_primeField, card_F] using hcard
  · push Not at hdet
    by_cases hx : ∃ a : W, a.val.left.x ≠ 0
    · obtain ⟨a, ha⟩ := hx
      let f : W → F × F := fun u => (u.val.left.x, u.val.left.c)
      have hf : Function.Injective f := by
        intro u v huv
        have hx := congrArg Prod.fst huv
        have hc := congrArg Prod.snd huv
        change u.val.left.x = v.val.left.x at hx
        change u.val.left.c = v.val.left.c at hc
        have hu := hdet a u
        have hv := hdet a v
        have hy : a.val.left.x * (u.val.left.y - v.val.left.y) = 0 := by
          rw [hx] at hu
          linear_combination hu - hv
        apply Subtype.ext
        exact SemidirectProduct.ext (U.ext hx
          (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left ha)) hc)
          (((mem_S _).mp (hS u.property)).trans ((mem_S _).mp (hS v.property)).symm)
      have hcard := Nat.card_le_card_of_injective f hf
      simpa only [Nat.card_prod, card_F] using hcard
    · push Not at hx
      let f : W → F × F := fun u => (u.val.left.y, u.val.left.c)
      have hf : Function.Injective f := by
        intro u v huv
        apply Subtype.ext
        exact SemidirectProduct.ext
          (U.ext ((hx u).trans (hx v).symm) (congrArg Prod.fst huv) (congrArg Prod.snd huv))
          (((mem_S _).mp (hS u.property)).trans ((mem_S _).mp (hS v.property)).symm)
      have hcard := Nat.card_le_card_of_injective f hf
      simpa only [Nat.card_prod, card_F] using hcard

private theorem card_map_quotient (H : Subgroup T) (hC : C ≤ H) :
    2 * Nat.card (H.map quotient) = Nat.card H := by
  have hh := (C.subgroupOf H).card_mul_index
  have hc : Nat.card (C.subgroupOf H) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv).trans card_C
  have hi : (C.subgroupOf H).index = Nat.card (H.map quotient) := by
    simpa only [quotient, QuotientGroup.ker_mk', Subgroup.relIndex] using
      Subgroup.relIndex_ker H quotient
  rwa [hc, hi] at hh

private theorem card_lift (A : Subgroup Tbar) :
    2 * Nat.card A = Nat.card (A.comap quotient) := by
  have hc : C ≤ A.comap quotient := by
    intro a ha
    change quotient a ∈ A
    have he : quotient a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    exact he ▸ A.one_mem
  have hh := card_map_quotient (A.comap quotient) hc
  have heq : (A.comap quotient).map quotient = A :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) A
  rw [heq] at hh
  exact hh

private theorem card_Qbar_aux : Nat.card Qbar = 16 := by
  have hh := card_map_quotient Q C_le_Q
  change 2 * Nat.card Qbar = Nat.card Q at hh
  rw [card_Q] at hh
  omega

private theorem outside_mem_Q (W : Subgroup T)
    [IsElementaryAbelian 2 (W.map quotient)] (a : T) (ha : a ∈ W)
    (hr : a.right = τ) : a ∈ Q := by
  have hp : quotient (a ^ 2) = 1 := by
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := W.map quotient)
      _ ⟨a, ha, rfl⟩
  have hz := (mem_Z _).mp (C_le_Z ((QuotientGroup.eq_one_iff _).mp hp))
  apply (mem_Q a).mpr
  have hx : trace a.left.x = 0 := by
    simpa only [trace, pow_two, SemidirectProduct.mul_left, hr, action_τ, mul_x, frob_x]
      using hz.2.1
  have hy : trace a.left.y = 0 := by
    simpa only [trace, pow_two, SemidirectProduct.mul_left, hr, action_τ, mul_y, frob_y]
      using hz.2.2
  exact ⟨(trace_eq_zero _).mp hx, (trace_eq_zero _).mp hy⟩

private theorem outside_le_Q (W : Subgroup T)
    [IsElementaryAbelian 2 (W.map quotient)] (hS : ¬ W ≤ S) : W ≤ Q := by
  obtain ⟨a, ha, has⟩ := Set.not_subset.mp hS
  have hr : a.right = τ := (c2_cases _).resolve_left (by simpa using has)
  have haQ := outside_mem_Q W a ha hr
  intro b hb
  rcases c2_cases b.right with hbr | hbr
  · have habQ := outside_mem_Q W (a * b) (W.mul_mem ha hb) (by simp [hr, hbr])
    exact (Q.mul_mem_cancel_left haQ).mp habQ
  · exact outside_mem_Q W b hb hbr

private theorem elementary_map_lift (A : Subgroup Tbar) [IsElementaryAbelian 2 A] :
    IsElementaryAbelian 2 ((A.comap quotient).map quotient) := by
  have heq : (A.comap quotient).map quotient = A :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) A
  rw [heq]
  infer_instance

theorem elementary_quotient_card_le_eight (A : Subgroup Tbar)
    [IsElementaryAbelian 2 A] (hS : A.comap quotient ≤ S) : Nat.card A ≤ 8 := by
  let _ : IsElementaryAbelian 2 ((A.comap quotient).map quotient) := elementary_map_lift A
  have hbound := card_lift_inside (A.comap quotient) hS
  have hcard := card_lift A
  omega

theorem elementary_quotient_le_Qbar_of_outside (A : Subgroup Tbar)
    [IsElementaryAbelian 2 A] (hS : ¬ A.comap quotient ≤ S) : A ≤ Qbar := by
  let _ : IsElementaryAbelian 2 ((A.comap quotient).map quotient) := elementary_map_lift A
  have h := Subgroup.map_mono (outside_le_Q (A.comap quotient) hS) (f := quotient)
  have heq : (A.comap quotient).map quotient = A :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C) A
  rw [heq] at h
  exact h

theorem elementary_quotient_card_le (A : Subgroup Tbar)
    [IsElementaryAbelian 2 A] : Nat.card A ≤ 16 := by
  by_cases hS : A.comap quotient ≤ S
  · exact (elementary_quotient_card_le_eight A hS).trans (by decide)
  · exact (Subgroup.card_le_of_le (elementary_quotient_le_Qbar_of_outside A hS)).trans_eq
      card_Qbar_aux

theorem elementary_quotient_eq_Qbar_of_card (A : Subgroup Tbar)
    [IsElementaryAbelian 2 A] (hcard : Nat.card A = 16) : A = Qbar := by
  by_cases hS : A.comap quotient ≤ S
  · have h := elementary_quotient_card_le_eight A hS
    omega
  · exact Subgroup.eq_of_le_of_card_ge (elementary_quotient_le_Qbar_of_outside A hS)
      (by rw [hcard, card_Qbar_aux])

theorem elementaryAbelianMaxJ_Tbar (helem : IsElementaryAbelian 2 Qbar)
    (hcard : Nat.card Qbar = 16) :
    Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup Tbar) = Qbar := by
  have hQ : Qbar ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup Tbar) := by
    refine ⟨le_top, helem, ?_⟩
    intro A _ hA
    let _ : IsElementaryAbelian 2 A := hA
    rw [hcard]
    exact elementary_quotient_card_le A
  apply le_antisymm
  · apply sSup_le
    intro A hA
    let _ : IsElementaryAbelian 2 A := hA.2.1
    have hge : 16 ≤ Nat.card A := by
      simpa only [hcard] using hA.2.2 Qbar le_top helem
    have heq := elementary_quotient_eq_Qbar_of_card A
      (Nat.le_antisymm (elementary_quotient_card_le A) hge)
    exact heq.le
  · exact le_sSup hQ

end
end Matrix.PSL3Four.SylowModel
