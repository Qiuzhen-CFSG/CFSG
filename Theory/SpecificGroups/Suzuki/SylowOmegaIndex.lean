module
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.SpecificGroups.Suzuki.SmallAutomorphisms
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# Suzuki Sylow omega orders and indices at every parameter

For q=2^(2m+1) with m>0 the existing root calculation gives Sylow order q²
and omega-center order q, hence index q. At m=0 the actual Sz(2) Sylow
is cyclic of order four; its squaring kernel has order and index two.
This treats the small parameter without applying a nonbinary center formula.

CoreProductOrders uses exactly these two invariants in the source (11.4)
comparison, where the odd field exponent excludes a square field order.
Source: Huppert--Blackburn III, XI.3.1; DGS, Groups and Graphs (1985),
(5.3) and (11.4), printed pp.105--106,171.
-/

public noncomputable section
open Subgroup
namespace BenderSuzuki.MatrixGroups
open scoped IsMulCommutative

private theorem small_sylow_cyclic (S : Sylow 2 (SuzukiMatrixGroup 0)) : IsCyclic S := by
  let P : Sylow 2 (SuzukiMatrixGroup 0) := Sylow.ofCard (zpowers suzukiZeroRootGenerator) (by
    rw [Nat.card_zpowers, suzukiZeroRootGenerator_order, suzukiZero_card]
    decide +kernel)
  let : IsCyclic P := inferInstanceAs (IsCyclic (zpowers suzukiZeroRootGenerator))
  exact (Sylow.equiv P S).isCyclic.mp inferInstance

/-- The omega-center order and index for every Suzuki parameter, including zero. -/
theorem suzukiSylow_omegaCenter_card_index (m : ℕ) (S : Sylow 2 (SuzukiMatrixGroup m)) :
    Nat.card (omegaCenterIn (S : Subgroup (SuzukiMatrixGroup m))) = 2^(2*m+1) ∧
      (omegaCenterIn (S : Subgroup (SuzukiMatrixGroup m))).relIndex S = 2^(2*m+1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · let : IsCyclic S := small_sylow_cyclic S
    have hc : Nat.card S = 4 := by
      rw [S.card_eq_multiplicity,suzukiZero_card]
      decide +kernel
    let f : S →* S := powMonoidHom 2
    have he : (omegaCenterIn (S : Subgroup (SuzukiMatrixGroup 0))).subgroupOf (S : Subgroup (SuzukiMatrixGroup 0)) = f.ker := by
      ext x
      change x.val ∈ omegaCenterIn (S : Subgroup (SuzukiMatrixGroup 0)) ↔ x^2=1
      rw [mem_omegaCenterIn_iff]
      exact ⟨fun hx => Subtype.ext hx.2.2,fun hx =>
        ⟨x.property,fun y hy => congrArg Subtype.val (mul_comm (⟨y,hy⟩ : S) x),
          congrArg Subtype.val hx⟩⟩
    have hle : omegaCenterIn (S : Subgroup (SuzukiMatrixGroup 0)) ≤ (S : Subgroup _) := map_subtype_le _
    constructor
    · rw [←Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,he]
      change Nat.card (powMonoidHom 2 : S →* S).ker = _
      rw [IsCyclic.card_powMonoidHom_ker,hc]
      decide
    · change ((omegaCenterIn (S : Subgroup (SuzukiMatrixGroup 0))).subgroupOf (S : Subgroup (SuzukiMatrixGroup 0))).index = _
      rw [he]
      change (powMonoidHom 2 : S →* S).ker.index = _
      rw [IsCyclic.index_powMonoidHom_ker,hc]
      decide
  · have hω : omegaCenterIn (S : Subgroup (SuzukiMatrixGroup m)) = omegaOneAmbient (S : Subgroup (SuzukiMatrixGroup m)) := by
      rw [omegaCenterIn_eq_omegaOneAmbient,←suzukiSylow_omega_eq_center hm (MulEquiv.refl _) S]
      let := suzukiSylow_omega_elementary hm (MulEquiv.refl _) S
      exact omegaOneAmbient_eq_self _
    have hc : Nat.card (omegaCenterIn (S : Subgroup (SuzukiMatrixGroup m))) = 2^(2*m+1) := by
      rw [hω,suzukiSylow_omega_card hm (MulEquiv.refl _) S]
    have hle : omegaCenterIn (S : Subgroup (SuzukiMatrixGroup m)) ≤ (S : Subgroup _) := map_subtype_le _
    have hx := ((omegaCenterIn (S : Subgroup (SuzukiMatrixGroup m))).subgroupOf (S : Subgroup (SuzukiMatrixGroup m))).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,hc,
      suzukiSylow_card hm (MulEquiv.refl _) S,pow_two] at hx
    exact ⟨hc,Nat.eq_of_mul_eq_mul_left (by positivity) hx⟩
end BenderSuzuki.MatrixGroups
