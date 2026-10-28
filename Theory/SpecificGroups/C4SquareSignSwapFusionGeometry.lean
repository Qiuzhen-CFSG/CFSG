module
public import Theory.SpecificGroups.C4SquareSignSwapCentricData
public import Theory.GroupTheory.C4SquareInvertingCharacteristic

/-!
# Central involutions and the inverter core in the sign-and-swap Sylow model

The exceptional nonabelian centric candidates have a unique central
involution. The abelian C₄-square inside the inverter core is characteristic,
so all its automorphisms preserve the marked transfer intersection. These
are the finite and structural inputs used in the full binary G₂ fusion
argument for source 14.2.22.
-/

@[expose] public noncomputable section
namespace C4SquareSignSwap
open Subgroup
local instance : DecidableEq Model := inferInstanceAs (DecidableEq (SemidirectProduct Base Actor action))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem central_involution_eq (z : Model)
    (hz : ∀ g : Model, g * z = z * g) (hpow : z ^ 2 = 1) (hne : z ≠ 1) :
    z = coordinateElement 10 := by
  have h : ∀ z : Model, (∀ g : Model, g * z = z * g) → z ^ 2 = 1 → z ≠ 1 →
      z = coordinateElement 10 := by decide +kernel
  exact h z hz hpow hne

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem candidate_central_involution_eq (i : Fin 32)
    (hi : i = 17 ∨ i = 26 ∨ i = 28 ∨ i = 31) (z : Model)
    (hmem : z ∈ centricCandidate i)
    (hz : ∀ g : Model, g ∈ centricCandidate i → g * z = z * g)
    (hpow : z ^ 2 = 1) (hne : z ≠ 1) : z = coordinateElement 10 := by
  have h : ∀ i : Fin 32, (i = 17 ∨ i = 26 ∨ i = 28 ∨ i = 31) →
      ∀ z : Model, z ∈ centricCandidate i →
      (∀ g : Model, g ∈ centricCandidate i → g * z = z * g) →
      z ^ 2 = 1 → z ≠ 1 → z = coordinateElement 10 := by decide +kernel
  exact h i hi z hmem hz hpow hne

private theorem base_le_inverter : base ≤ inverterCore := by
  intro x hx
  change x.right.2 = 1
  exact congrArg Prod.snd hx

instance base_inverter_characteristic : (base.subgroupOf inverterCore).Characteristic := by
  let A := base.subgroupOf inverterCore
  have hA : Nonempty (A ≃* C4 × C4) :=
    ⟨(subgroupOfEquivOfLe base_le_inverter).trans baseEquiv⟩
  have hcard : Nat.card A = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe base_le_inverter).toEquiv).trans card_base
  have hi : A.index = 2 := by
    have hh := A.card_mul_index
    rw [hcard,card_inverterCore] at hh
    omega
  let t : inverterCore := ⟨inverter,rfl⟩
  apply characteristic_of_inverted_c4_square A hA hi t
  · change inverter ∉ base
    decide +kernel
  · intro a ha
    apply Subtype.ext
    have h : ∀ x : Model, x ∈ base → inverter * x * inverter⁻¹ = x⁻¹ := by decide +kernel
    exact h a ha

theorem inverterCore_automorphism_preserves_transfer
    (a : MulAut inverterCore) (x : inverterCore) :
    (a x : Model) ∈ transfer ↔ (x : Model) ∈ transfer := by
  have hmem (y : inverterCore) : (y : Model) ∈ transfer ↔ y ∈ base.subgroupOf inverterCore := by
    change y.val.right.1 = 1 ↔ y.val.right = 1
    constructor
    · intro h
      exact Prod.ext h y.property
    · exact fun h => congrArg Prod.fst h
  rw [hmem,hmem]
  exact SetLike.ext_iff.mp (characteristic_iff_comap_eq.mp
    base_inverter_characteristic a) x

end C4SquareSignSwap
