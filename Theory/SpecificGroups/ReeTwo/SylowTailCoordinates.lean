module

public import Theory.SpecificGroups.ReeTwo.SylowTail
public import Theory.SpecificGroups.ReeTwo.CoreCharacterKernel

/-!
# Coordinates and normality of the Ree two tail

The last six roots generate exactly the core elements whose first four
coordinates vanish. The six remaining binary coordinates give order 64.
The kernel description proves invariance under conjugation by the core;
the cyclic-four factor preserves the tail by its checked action on the
six generating roots. Thus the Sylow quotient by the tail has order 64.

Source: the multiplication and action formulas of Shinoda (1975), (2.3),
pp. 81–82, as verified in `ReeTwo.Core` and `ReeTwo.RootAction`.
-/

namespace ReeTwo.Core

/-- The first four core coordinates, with their additive group structure. -/
@[expose] public def leadingFour : Core →* Multiplicative (Fin 4 → ZMod 2) where
  toFun x := Multiplicative.ofAdd ![x.b0, x.b1, x.b2, x.b3]
  map_one' := by
    change (![0, 0, 0, 0] : Fin 4 → ZMod 2) = 0
    funext i; fin_cases i <;> rfl
  map_mul' x y := by
    change (![_, _, _, _] : Fin 4 → ZMod 2) = _ + _
    funext i; fin_cases i <;> rfl

/-- Vanishing of the four coordinates describes the kernel. -/
public theorem mem_leadingFour_ker (x : Core) : x ∈ leadingFour.ker ↔
    x.b0 = 0 ∧ x.b1 = 0 ∧ x.b2 = 0 ∧ x.b3 = 0 := by
  change (![x.b0, x.b1, x.b2, x.b3] : Fin 4 → ZMod 2) = 0 ↔ _
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3]

/-- The last six coordinates parametrize the kernel independently. -/
@[expose] public def tailCoordinates : leadingFour.ker ≃ (Fin 6 → ZMod 2) where
  toFun x := ![x.val.b4, x.val.b5, x.val.b6, x.val.b7, x.val.b8, x.val.b9]
  invFun v := ⟨⟨0, 0, 0, 0, v 0, v 1, v 2, v 3, v 4, v 5⟩, (mem_leadingFour_ker _).mpr ⟨rfl, rfl, rfl, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨h0, h1, h2, h3⟩ := (mem_leadingFour_ker x).mp x.property
    apply Core.ext <;> simp_all
  right_inv v := by funext i; fin_cases i <;> rfl
end ReeTwo.Core

namespace ReeTwo.SylowModel

/-- The tail is the embedded kernel of the four leading core coordinates. -/
public theorem tailSubgroup_eq_map : tailSubgroup =
    Core.leadingFour.ker.map (SemidirectProduct.inl : Core →* SylowModel) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨i, hi, rfl⟩
    apply Subgroup.mem_map_of_mem
    rw [Core.mem_leadingFour_ker]
    fin_cases i <;> simp_all [Core.root, Core.ofCoords]
  · rintro x ⟨c, hc, rfl⟩
    obtain ⟨h0, h1, h2, h3⟩ := (Core.mem_leadingFour_ker c).mp hc
    have hroot (i : CoreRoot) (hi : 4 ≤ i.val) : root i ∈ tailSubgroup :=
      Subgroup.subset_closure ⟨i, hi, rfl⟩
    have hn := congrArg (SemidirectProduct.inl : Core →* SylowModel) (Core.normal_form c)
    simp only [map_mul, map_pow, h0, h1, h2, h3,
      ZMod.val_zero, pow_zero, one_mul] at hn
    rw [← hn]
    exact tailSubgroup.mul_mem
      (tailSubgroup.mul_mem
        (tailSubgroup.mul_mem
          (tailSubgroup.mul_mem
            (tailSubgroup.mul_mem
              (tailSubgroup.pow_mem (hroot 4 (by decide)) _)
              (tailSubgroup.pow_mem (hroot 5 (by decide)) _))
            (tailSubgroup.pow_mem (hroot 6 (by decide)) _))
          (tailSubgroup.pow_mem (hroot 7 (by decide)) _))
        (tailSubgroup.pow_mem (hroot 8 (by decide)) _))
      (tailSubgroup.pow_mem (hroot 9 (by decide)) _)

/-- A coordinate membership test for the six-root tail. -/
public theorem mem_tailSubgroup (x : SylowModel) : x ∈ tailSubgroup ↔
    x.right = 1 ∧ x.left.b0 = 0 ∧ x.left.b1 = 0 ∧ x.left.b2 = 0 ∧ x.left.b3 = 0 := by
  rw [tailSubgroup_eq_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨rfl, (Core.mem_leadingFour_ker c).mp hc⟩
  · rintro ⟨hr, hc⟩
    exact ⟨x.left, (Core.mem_leadingFour_ker _).mpr hc, SemidirectProduct.ext rfl hr.symm⟩

/-- The six-root tail has order 64. -/
public theorem tailSubgroup_card : Nat.card tailSubgroup = 64 := by
  rw [tailSubgroup_eq_map]
  rw [← Nat.card_congr (Core.leadingFour.ker.equivMapOfInjective
    (SemidirectProduct.inl : Core →* SylowModel) SemidirectProduct.inl_injective).toEquiv]
  rw [Nat.card_congr Core.tailCoordinates, Nat.card_fun]
  simp

/-- The tail lies in the canonical order-1024 core. -/
public theorem tailSubgroup_le_coreSubgroup : tailSubgroup ≤ coreSubgroup := by
  rw [tailSubgroup_eq_map]
  rintro x ⟨c, _, rfl⟩
  exact ⟨c, rfl⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem tail_conjugation_test : ∀ (t : FiveFour.Cyclic 4) (i : CoreRoot),
    4 ≤ i.val →
    let x := (SemidirectProduct.inr t : SylowModel) * root i *
      (SemidirectProduct.inr t : SylowModel)⁻¹
    x.right = 1 ∧ x.left.b0 = 0 ∧ x.left.b1 = 0 ∧ x.left.b2 = 0 ∧ x.left.b3 = 0 :=
  by decide +kernel

/-- Both factors of the Sylow semidirect product normalize the tail. -/
public instance tailSubgroup_normal : tailSubgroup.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  apply Subgroup.mul_mem
  · have h := Subgroup.le_normalizer_map (H := Core.leadingFour.ker)
      (SemidirectProduct.inl : Core →* SylowModel)
    rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, ← tailSubgroup_eq_map] at h
    exact h ⟨x.left, rfl⟩
  · have h : (SemidirectProduct.inr : FiveFour.Cyclic 4 →* SylowModel).range ≤
        Subgroup.normalizer tailSubgroup := by
      apply Subgroup.le_normalizer_closure_iff.mpr
      rintro y ⟨t, rfl⟩ z ⟨i, hi, rfl⟩
      exact (mem_tailSubgroup _).mpr (tail_conjugation_test t i hi)
    exact h ⟨x.right, rfl⟩

/-- The quotient by the tail has 64 elements. -/
public theorem tailSubgroup_index : tailSubgroup.index = 64 := by
  have h := tailSubgroup.index_mul_card
  rw [tailSubgroup_card, card] at h
  omega
end ReeTwo.SylowModel
