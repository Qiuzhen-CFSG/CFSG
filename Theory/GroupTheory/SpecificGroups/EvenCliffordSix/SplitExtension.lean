module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The intrinsic signed split extension and its two central layers

The group is the literal semidirect product of the even Clifford group with
its proved signed A₆ action. The radical embedding retains the cyclic-four
center and the shared sign involution as actual subgroups of the extension.
The action fixes the center, so this embedded C₄ is central in the extension.

These are the stable model boundaries for the second E₁₆ restriction in
Aschbacher–Smith I.2.2(6a), printed pp.410 and 412. A subgroup containing the
central C₄, of order 64, and with all squares in the sign subgroup has an
order-16 elementary image modulo that C₄. Identifying these restrictions as
C₄ ∗ Q₈ ∗ Q₈ remains a separate calculation; no classification is assumed here.
-/

@[expose] public section
open Subgroup
namespace EvenCliffordSix
/-- The action is intrinsic and independent of any ambient covering group. -/
abbrev SplitExtension := Model ⋊[action] A
namespace SplitExtension
instance : Finite SplitExtension :=
  Finite.of_equiv (Model × A) SemidirectProduct.equivProd.symm
abbrev radicalEmbedding : Model →* SplitExtension := SemidirectProduct.inl
/-- The actual cyclic-four subgroup, embedded through the radical. -/
abbrev central : Subgroup SplitExtension := (center Model).map radicalEmbedding
/-- The actual sign involution subgroup, embedded through the radical. -/
abbrev sign : Subgroup SplitExtension := signKernel.map radicalEmbedding

theorem radicalEmbedding_injective : Function.Injective radicalEmbedding :=
  fun _ _ h => congrArg SemidirectProduct.left h

theorem central_card : Nat.card central = 4 := by
  rw [central, card_map_of_injective radicalEmbedding_injective, Structure.center_card]

theorem sign_card : Nat.card sign = 2 := by
  rw [sign, card_map_of_injective radicalEmbedding_injective, signKernel_card]

theorem sign_le_central : sign ≤ central := map_mono signKernel_le_center

theorem central_le_center : central ≤ center SplitExtension := by
  rintro _ ⟨z, hz, rfl⟩
  apply mem_center_iff.mpr
  intro x
  apply SemidirectProduct.ext
  · change x.left * action x.right z = z * action 1 x.left
    rw [action_center _ _ hz]
    simpa only [map_one, MulAut.one_apply] using mem_center_iff.mp hz x.left
  · simp

theorem mem_sign_iff (x : SplitExtension) : x ∈ sign ↔ x.left ∈ signKernel ∧ x.right = 1 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hz, rfl⟩
  · rintro ⟨hl, hr⟩
    exact ⟨x.left, hl, SemidirectProduct.ext rfl hr.symm⟩
end SplitExtension
end EvenCliffordSix
