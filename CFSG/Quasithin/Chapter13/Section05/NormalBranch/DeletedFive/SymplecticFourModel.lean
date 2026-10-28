module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SymplecticFour.Sylow.SelfCentralizingElementary

/-!
# Excluding Sp₄(4) in the deleted-five model inspection

The original order-sixteen module in the centralizer quotient is elementary
and self-centralizing. In Sp₄(4), every elementary subgroup extends to a root
wing of order 4³. That wing centralizes the module, contradicting its order.
This uses the actual symplectic field witness and does not require a stronger
classification of normalizers or of alternating-five blocks.

Source: Aschbacher--Smith, 13.5.15, printed p.921.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

/-- The self-centralizing order-sixteen module excludes the Sp₄(4) model. -/
theorem not_symplecticFour_model (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 16) (hC : centralizer (E : Set G) ≤ E)
    (hmodel : ClassicalGroup.IsPSp G 2 4) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ 2 := by simpa using hF
  let _ : CharP F 2 := EvenProjective.charTwo_of_card hF'
  have h := CentralRootGeometry.card_ge_of_selfCentralizing_elementary
    (e.trans (EvenProjective.equiv (F := F)).symm) hF' (by decide) E hC
  rw [hF, hE] at h
  norm_num at h

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
