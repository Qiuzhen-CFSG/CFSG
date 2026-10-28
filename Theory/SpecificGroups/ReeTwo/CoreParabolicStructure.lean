module

public import Theory.SpecificGroups.ReeTwo.CoreQuotientCenter
public import Theory.ElementaryAbelian.Basic

/-!
# Derived subgroup and centralizer of the full Ree two core

The derived subgroup consists of the last five binary root coordinates.
The root commutators generate these coordinates; the abelian head homomorphism
proves the reverse inclusion. Commutation with the tail detects four head
coordinates, yielding its centralizer and the elementary quotient of order 16.
A bilinear commutation formula identifies the second center with the derived
subgroup, rather than with its larger centralizer.

These are intrinsic calculations in the verified root-coordinate model.
Compatibility with a parabolic in an ambient Ree group is a separate obligation.
Source: Shinoda (1975), (2.3), pp.81–82, as implemented in `Core`; compare
Aschbacher, *The Tits group as a standard subgroup* (1982), Section 3.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace ReeTwo.Core

/-- The abelian head records the first five root coordinates. -/
def derivedHead : Core →* Multiplicative (Fin 5 → ZMod 2) where
  toFun x := Multiplicative.ofAdd ![x.b0, x.b1, x.b2, x.b3, x.b4]
  map_one' := by apply congrArg Multiplicative.ofAdd; funext i; fin_cases i <;> rfl
  map_mul' x y := by apply congrArg Multiplicative.ofAdd; funext i; fin_cases i <;> rfl

/-- Vanishing of the abelian head in coordinates. -/
theorem derivedHead_ker (x : Core) : x ∈ derivedHead.ker ↔
    x.b0 = 0 ∧ x.b1 = 0 ∧ x.b2 = 0 ∧ x.b3 = 0 ∧ x.b4 = 0 := by
  change derivedHead x = 1 ↔ _
  constructor
  · intro h
    exact ⟨congrArg (fun v => v.toAdd 0) h, congrArg (fun v => v.toAdd 1) h,
      congrArg (fun v => v.toAdd 2) h, congrArg (fun v => v.toAdd 3) h,
      congrArg (fun v => v.toAdd 4) h⟩
  · rintro ⟨h0,h1,h2,h3,h4⟩
    apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i <;> assumption

/-- Each of the last five roots is a commutator. -/
theorem tail_root_mem_derived (i : Fin 5) :
    root ⟨5 + i.val, by omega⟩ ∈ commutator Core := by
  have h (a b : Core) : rightComm a b ∈ commutator Core := by
    simpa [rightComm, commutatorElement_def, _root_.commutator_def] using
      (commutator_mem_commutator (show a⁻¹ ∈ (⊤ : Subgroup Core) from trivial)
        (show b⁻¹ ∈ (⊤ : Subgroup Core) from trivial))
  have h5 : rightComm (root 0) (root 2) = root 5 := by decide +kernel
  have h6 : rightComm (root 1) (root 2) = root 6 := by decide +kernel
  have h7 : rightComm (root 2) (root 3) = root 7 := by decide +kernel
  have h8 : rightComm (root 2) (root 4) = root 8 := by decide +kernel
  have h9 : rightComm (root 0) (root 8) = root 9 := by decide +kernel
  fin_cases i
  · exact h5 ▸ h _ _
  · exact h6 ▸ h _ _
  · exact h7 ▸ h _ _
  · exact h8 ▸ h _ _
  · exact h9 ▸ h _ _

/-- Exact coordinate description of the derived subgroup. -/
theorem mem_derived_iff (x : Core) : x ∈ commutator Core ↔
    x.b0 = 0 ∧ x.b1 = 0 ∧ x.b2 = 0 ∧ x.b3 = 0 ∧ x.b4 = 0 := by
  constructor
  · intro h
    exact (derivedHead_ker x).mp (Abelianization.commutator_subset_ker derivedHead h)
  · rintro ⟨h0,h1,h2,h3,h4⟩
    have hn := normal_form x
    rw [h0,h1,h2,h3,h4] at hn
    simp only [ZMod.val_zero, pow_zero, one_mul] at hn
    exact hn ▸ mul_mem (mul_mem (mul_mem (mul_mem
      (pow_mem (tail_root_mem_derived 0) _) (pow_mem (tail_root_mem_derived 1) _))
      (pow_mem (tail_root_mem_derived 2) _)) (pow_mem (tail_root_mem_derived 3) _))
      (pow_mem (tail_root_mem_derived 4) _)

/-- The derived subgroup, with its specified binary basis. -/
def derivedCoordinates : commutator Core ≃* Multiplicative (Fin 5 → ZMod 2) where
  toFun x := Multiplicative.ofAdd ![x.val.b5,x.val.b6,x.val.b7,x.val.b8,x.val.b9]
  invFun v := ⟨⟨0,0,0,0,0,v.toAdd 0,v.toAdd 1,v.toAdd 2,v.toAdd 3,v.toAdd 4⟩,
    (mem_derived_iff _).mpr ⟨rfl,rfl,rfl,rfl,rfl⟩⟩
  left_inv x := by
    obtain ⟨h0,h1,h2,h3,h4⟩ := (mem_derived_iff x.val).mp x.property
    apply Subtype.ext
    apply Core.ext <;> simp_all
  right_inv v := by apply congrArg Multiplicative.ofAdd; funext i; fin_cases i <;> rfl
  map_mul' x y := by
    obtain ⟨h0,h1,h2,h3,h4⟩ := (mem_derived_iff y.val).mp y.property
    apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i <;> simp [show ∀ a b : commutator Core, (a * b).val = mul a.val b.val from fun _ _ => rfl, mul,h0,h1,h2,h3,h4]

/-- The derived subgroup has order 32. -/
theorem derived_card : Nat.card (commutator Core) = 32 := by
  rw [Nat.card_congr derivedCoordinates.toEquiv]
  change Nat.card (Fin 5 → ZMod 2) = 32
  simp

/-- The derived subgroup is elementary abelian of exponent two. -/
theorem derived_elementary : IsElementaryAbelian 2 (commutator Core) := by
  have hs (x : commutator Core) : x ^ 2 = 1 := by
    apply derivedCoordinates.injective
    rw [map_pow, map_one, pow_two]
    apply congrArg Multiplicative.ofAdd
    funext i
    change (derivedCoordinates x).toAdd i + (derivedCoordinates x).toAdd i = 0
    ring_nf
    reduce_mod_char
  exact { toIsMulCommutative := ⟨⟨fun x y => derivedCoordinates.injective (by
              simp only [map_mul, mul_comm])⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

/-- The four head coordinates detected by commutation with the derived subgroup. -/
def centralizerHead : Core →* Multiplicative (Fin 4 → ZMod 2) where
  toFun x := Multiplicative.ofAdd ![x.b0, x.b1, x.b3, x.b4]
  map_one' := by apply congrArg Multiplicative.ofAdd; funext i; fin_cases i <;> rfl
  map_mul' x y := by apply congrArg Multiplicative.ofAdd; funext i; fin_cases i <;> rfl

/-- Vanishing of the four-coordinate head. -/
theorem centralizerHead_ker (x : Core) : x ∈ centralizerHead.ker ↔
    x.b0 = 0 ∧ x.b1 = 0 ∧ x.b3 = 0 ∧ x.b4 = 0 := by
  change centralizerHead x = 1 ↔ _
  constructor
  · intro h
    exact ⟨congrArg (fun v => v.toAdd 0) h, congrArg (fun v => v.toAdd 1) h,
      congrArg (fun v => v.toAdd 2) h, congrArg (fun v => v.toAdd 3) h⟩
  · rintro ⟨h0,h1,h3,h4⟩
    apply congrArg Multiplicative.ofAdd
    funext i
    fin_cases i <;> assumption

/-- Exact coordinate description of the centralizer inside the core. -/
theorem mem_centralizer_derived_iff (x : Core) :
    x ∈ centralizer (commutator Core : Set Core) ↔
      x.b0 = 0 ∧ x.b1 = 0 ∧ x.b3 = 0 ∧ x.b4 = 0 := by
  constructor
  · intro hx
    have h (i : Fin 4) := congrArg Core.b9
      (mem_centralizer_iff.mp hx (root ⟨5 + i.val, by omega⟩)
        (tail_root_mem_derived ⟨i.val, by omega⟩))
    have h5 := h 0
    have h6 := h 1
    have h7 := h 2
    have h8 := h 3
    change (mul _ _).b9 = (mul _ _).b9 at h5 h6 h7 h8
    simp [mul, root, ofCoords] at h5 h6 h7 h8
    exact ⟨h8,h7,h6,h5⟩
  · rintro ⟨h0,h1,h3,h4⟩
    apply mem_centralizer_iff.mpr
    intro y hy
    obtain ⟨k0,k1,k2,k3,k4⟩ := (mem_derived_iff y).mp hy
    change mul y x = mul x y
    apply Core.ext <;> simp [mul,h0,h1,h3,h4,k0,k1,k2,k3,k4,add_comm]

/-- The centralizer is the kernel of the four-coordinate head. -/
theorem centralizer_derived_eq_ker :
    centralizer (commutator Core : Set Core) = centralizerHead.ker := by
  ext x
  rw [mem_centralizer_derived_iff, centralizerHead_ker]

/-- All four head coordinates occur independently. -/
theorem centralizerHead_surjective : Function.Surjective centralizerHead := by
  intro v
  refine ⟨⟨v.toAdd 0,v.toAdd 1,0,v.toAdd 2,v.toAdd 3,0,0,0,0,0⟩, ?_⟩
  apply congrArg Multiplicative.ofAdd
  funext i
  fin_cases i <;> rfl

/-- The quotient by the derived centralizer with its specified binary basis. -/
noncomputable def quotientCentralizerDerivedEquiv :
    Core ⧸ centralizer (commutator Core : Set Core) ≃*
      Multiplicative (Fin 4 → ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq centralizer_derived_eq_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective centralizerHead centralizerHead_surjective)

/-- The quotient by the derived centralizer has order 16. -/
theorem quotient_centralizer_derived_card :
    Nat.card (Core ⧸ centralizer (commutator Core : Set Core)) = 16 := by
  rw [Nat.card_congr quotientCentralizerDerivedEquiv.toEquiv]
  change Nat.card (Fin 4 → ZMod 2) = 16
  simp

/-- The derived centralizer inside the full core has order 64. -/
theorem centralizer_derived_card :
    Nat.card (centralizer (commutator Core : Set Core)) = 64 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (centralizer (commutator Core : Set Core))
  rw [card, quotient_centralizer_derived_card] at h
  omega


/-- The centralizer is generated by the middle root and the derived tail. -/
theorem centralizer_derived_eq_sup : centralizer (commutator Core : Set Core) =
    zpowers (root 2) ⊔ commutator Core := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h0,h1,h3,h4⟩ := (mem_centralizer_derived_iff x).mp hx
    have hn := normal_form x
    rw [h0,h1,h3,h4] at hn
    simp only [ZMod.val_zero, pow_zero, one_mul, mul_one] at hn
    have ht (i : Fin 5) : root ⟨5 + i.val, by omega⟩ ∈
        zpowers (root 2) ⊔ commutator Core :=
      (show commutator Core ≤ zpowers (root 2) ⊔ commutator Core from le_sup_right)
        (tail_root_mem_derived i)
    exact hn ▸ mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (pow_mem ((show zpowers (root 2) ≤ zpowers (root 2) ⊔ commutator Core from le_sup_left)
        (mem_zpowers (root 2))) _) (pow_mem (ht 0) _))
      (pow_mem (ht 1) _)) (pow_mem (ht 2) _)) (pow_mem (ht 3) _)) (pow_mem (ht 4) _)
  · apply sup_le
    · exact zpowers_le_of_mem root_two_mem_centralizer_derived
    · intro x hx
      obtain ⟨h0,h1,_,h3,h4⟩ := (mem_derived_iff x).mp hx
      exact (mem_centralizer_derived_iff x).mpr ⟨h0,h1,h3,h4⟩

private theorem tail_commutes_mod_center (x y : Core) (hx : x ∈ commutator Core) :
    x * y = y * x * root 9 ^
      (x.b5 * y.b4 + x.b6 * y.b3 + x.b7 * y.b1 + x.b8 * y.b0).val := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := (mem_derived_iff x).mp hx
  rw [root_pow]
  change mul x y = mul (mul y x) _
  apply Core.ext <;> simp [mul,ofCoords,h0,h1,h2,h3,h4] <;> ring

/-- In the full core the second center is exactly the derived subgroup. -/
theorem second_center_eq_derived : Subgroup.upperCentralSeries Core 2 =
    commutator Core := by
  apply le_antisymm second_center_le_derived
  intro x hx
  apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
  intro y
  rw [Subgroup.upperCentralSeries_one]
  let z := root 9 ^ (x.b5 * y.b4 + x.b6 * y.b3 + x.b7 * y.b1 + x.b8 * y.b0).val
  have hz : z ∈ center Core := pow_mem root_nine_mem_center _
  have he : ⁅x,y⁆ = z := by
    have hxy : x * y = y * x * z := tail_commutes_mod_center x y hx
    rw [commutatorElement_def, hxy]
    have hzy := (mem_center_iff.mp hz (y * x)).symm
    calc
      y * x * z * x⁻¹ * y⁻¹ = z * (y * x) * x⁻¹ * y⁻¹ := by rw [hzy]
      _ = z := by group
  exact he ▸ hz

/-- The quotient by the derived centralizer is elementary abelian. -/
theorem quotient_centralizer_derived_elementary :
    IsElementaryAbelian 2 (Core ⧸ centralizer (commutator Core : Set Core)) := by
  let e := quotientCentralizerDerivedEquiv
  have hs (x : Core ⧸ centralizer (commutator Core : Set Core)) : x ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, pow_two]
    apply congrArg Multiplicative.ofAdd
    funext i
    change (e x).toAdd i + (e x).toAdd i = 0
    ring_nf
    reduce_mod_char
  exact { toIsMulCommutative := ⟨⟨fun x y => e.injective (by
              simp only [map_mul, mul_comm])⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

end ReeTwo.Core
