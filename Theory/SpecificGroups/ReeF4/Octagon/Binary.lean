module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.Incidence
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.WeylGroup
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.MarkedParabolics

/-!
# The octagonal datum of the full binary Ree group

The binary Borel has order 4096 and the linear seed has order 12288. Its
linear Weyl lift lies outside the Borel, so these two subgroups generate
the seed, by its prime relative index. The Suzuki calculation and marked
Weyl presentation already hold at the binary endpoint. This constructs the
actual octagonal datum, including the source order of the two vertices:
first Suzuki, then linear. No simplicity or path-transitivity is assumed.

Source: the rank-two BN-pair construction, GLS3 §§2.3 and 2.6; Aschbacher–Smith
F.1.12 and F.4.8, the full group ²F₄(2), not its Tits derived subgroup.
-/

public noncomputable section
namespace ReeF4.Octagon.Binary
open Subgroup LargeLocalSeeds Parabolics Parabolics.Binary.FixedGeometry
open SectionGeometry.BNPair
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
open Theory.AlgebraicGroup.TitsSystem
attribute [local instance] borel_inf_normalizerWords_normal

/-- The existing marked word presentation includes the binary endpoint. -/
theorem markedWeyl (m : ℕ) : HasOctagonalWeylGroup m := by
  have hgen := simpleReflections_generate_of_normalizerWords m
    (normalizerWords_le_fixedTorus_sup_weylSubgroup m)
  rw [simpleReflections_eq_pair] at hgen
  exact MarkedWeyl.markedEquiv_of_involutions
    (simpleReflection m .linear) (simpleReflection m .suzuki)
    (simpleReflection_sq m .linear) (simpleReflection_sq m .suzuki)
    (MarkedWeyl.relativeRotation_pow_eight m)
    (MarkedWeyl.relativeRotation_pow_four_ne_one m) hgen

/-- The omitted binary linear generation follows from the actual local orders. -/
theorem linear_parabolic_generation :
    Parabolics.parabolic 0 .linear = borel 0 ⊔ zpowers (weylLift 0 .linear) := by
  let H := borel 0 ⊔ zpowers (weylLift 0 .linear)
  have hBH : borel 0 ≤ H := le_sup_left
  have hHP : H ≤ Parabolics.parabolic 0 .linear :=
    sup_le (borel_le_parabolic 0 .linear)
      (zpowers_le.mpr (seed_le_parabolic 0 .linear (weylLift_mem_seed 0 .linear)))
  have hnot : weylLift 0 .linear ∉ borel 0 := by
    intro hw
    have hc := (titsSystem 0).representative_mem_bruhatCell
      (simpleReflection 0 .linear) (simpleLift 0 .linear) rfl
    have h1 : weylLift 0 .linear ∈ (titsSystem 0).bruhatCell 1 := by
      rwa [(titsSystem 0).bruhatCell_one]
    have he := (titsSystem 0).doubleCoset_index_unique hc h1
    exact ((titsSystem 0).involutions _ (simpleReflection_mem 0 .linear)).1 he
  have hP : Nat.card (Parabolics.parabolic 0 .linear) = 12288 := by
    rw [← Tits.ExceptionalParabolics.FullRee.second_eq_parabolic]
    exact Tits.ExceptionalParabolics.FullRee.second_card
  have hB : Nat.card (borel 0) = 4096 := Tits.ExceptionalParabolics.FullRee.borel_card
  obtain ⟨k, hk⟩ := card_dvd_of_le hBH
  rw [hB] at hk
  have hd : 4096 * k ∣ 4096 * 3 := by
    simpa only [hk, hP] using card_dvd_of_le hHP
  have hk3 : k ∣ 3 := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 4096)).mp hd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hk3 with hk1 | hk3
  · have he : borel 0 = H := eq_of_le_of_card_ge hBH (by rw [hk, hk1, mul_one, hB])
    exact (hnot (he ▸ (show weylLift 0 .linear ∈ H from
      mem_sup_right (mem_zpowers _)))).elim
  · exact (eq_of_le_of_card_ge hHP (by rw [hk, hk3, hP])).symm

/-- Both singleton standard parabolics are the actual full binary root parabolics. -/
theorem standardParabolic_singleton (s : Side) :
    (titsSystem 0).standardParabolic {simpleReflection 0 s} = Parabolics.parabolic 0 s := by
  let T := titsSystem 0
  have hcell : weylLift 0 s ∈ T.bruhatCell (simpleReflection 0 s) :=
    T.representative_mem_bruhatCell _ (simpleLift 0 s) rfl
  apply le_antisymm
  · apply T.standardParabolic_le (Parabolics.parabolic 0 s) (borel_le_parabolic 0 s)
    rintro w (rfl : w = simpleReflection 0 s)
    exact T.bruhatCell_subset_of_mem (Parabolics.parabolic 0 s) (borel_le_parabolic 0 s)
      hcell (seed_le_parabolic 0 s (weylLift_mem_seed 0 s))
  · have hgen : Parabolics.parabolic 0 s = borel 0 ⊔ zpowers (weylLift 0 s) := by
      cases s with
      | suzuki => exact suzuki_parabolic_eq_borel_sup_weyl 0
      | linear => exact linear_parabolic_generation
    rw [hgen]
    exact sup_le (T.B_le_standardParabolic _)
      (zpowers_le.mpr (T.bruhatCell_subset_standardParabolic_of_mem
        (Set.mem_singleton _) hcell))

/-- The binary datum on the original Side-indexed parabolics. -/
theorem exists_native_datum :
    Nonempty (DihedralGeometry.OctagonalDatum (titsSystem 0) (Parabolics.parabolic 0)) := by
  obtain ⟨e, he₀, he₁⟩ := markedWeyl 0
  refine ⟨{
    typeEquiv := {
      toFun := fun s => match s with | .linear => false | .suzuki => true
      invFun := fun b => if b then .suzuki else .linear
      left_inv := by intro s; cases s <;> rfl
      right_inv := by intro b; cases b <;> rfl }
    simple := simpleReflection 0
    simple_range := rfl
    weylEquiv := e
    map_simple := ?_
    parabolic_eq := fun s => (standardParabolic_singleton s).symm }⟩
  intro s
  cases s with
  | linear => exact he₀
  | suzuki => exact he₁

/-- The actual source vertex family: Suzuki first, linear second. -/
@[expose] def family : Bool → Subgroup (Model 0) := fun b =>
  if b then Tits.ExceptionalParabolics.FullRee.second else Tits.ExceptionalParabolics.FullRee.first

/-- The Weyl marking swaps the source's Bool labels, preserving its actual subgroups. -/
theorem exists_datum :
    Nonempty (DihedralGeometry.OctagonalDatum (titsSystem 0) family) := by
  obtain ⟨e, he₀, he₁⟩ := markedWeyl 0
  let side : Bool → Side := fun b => if b then .linear else .suzuki
  refine ⟨{
    typeEquiv := {
      toFun := Bool.not
      invFun := Bool.not
      left_inv := Bool.not_not
      right_inv := Bool.not_not }
    simple := fun b => simpleReflection 0 (side b)
    simple_range := ?_
    weylEquiv := e
    map_simple := ?_
    parabolic_eq := ?_ }⟩
  · change Set.range (fun b => simpleReflection 0 (side b)) = Set.range (simpleReflection 0)
    ext w
    constructor
    · rintro ⟨b, rfl⟩; exact ⟨side b, rfl⟩
    · rintro ⟨s, rfl⟩
      cases s with
      | linear => exact ⟨true, rfl⟩
      | suzuki => exact ⟨false, rfl⟩
  · intro b
    cases b with
    | false => exact he₁
    | true => exact he₀
  · intro b
    cases b
    · exact Tits.ExceptionalParabolics.FullRee.first_eq_parabolic.trans
        (standardParabolic_singleton .suzuki).symm
    · exact Tits.ExceptionalParabolics.FullRee.second_eq_parabolic.trans
        (standardParabolic_singleton .linear).symm

end ReeF4.Octagon.Binary
