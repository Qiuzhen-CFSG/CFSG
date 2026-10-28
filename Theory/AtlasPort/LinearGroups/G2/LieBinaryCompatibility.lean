module

public import Theory.AtlasPort.LinearGroups.G2.LieSpecialRadical
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.CoreIdentification
/-!
# Compatibility with the full binary G₂ parabolic pair

At field order two the torus disappears. The root-defined locals therefore
agree with the existing binary parabolics, and the first five-root subgroup
agrees with the embedded quaternion central product. The checked binary
intersection and two-core calculations give the whole Borel overlap and an
actual isomorphism from the intrinsic first two-core to the special subgroup.
The ambient model throughout is full G₂(2), not its derived subgroup.

Source: Aschbacher--Smith, F.1.12(I)(3), printed pp. 262--264, and
Lemma 14.2.21, printed p. 988.
-/

@[expose] public section

namespace Atlas.G2.LieParabolicSetup

theorem radical₁_binary : radical₁ (F := ZMod 2) = BinaryCore.core := by
  apply le_antisymm
  · rintro g ⟨t,ht,rfl⟩
    refine ⟨⟨t 0,t 1,t 2,t 3,t 4⟩, ?_⟩
    simp [BinaryCore.embedding, BinaryCore.parameters, unipotentProduct, ht]
  · rintro g ⟨t,rfl⟩
    exact ⟨BinaryCore.parameters t, rfl, rfl⟩

theorem local₁_binary : local₁ (F := ZMod 2) = BinaryParabolicPair.firstParabolic := rfl

theorem borel_binary : borel (K := ZMod 2) = unipotent :=
  borel_eq_unipotent_of_card_two (by simp [Nat.card_eq_fintype_card])

theorem parabolic₁_binary : parabolic₁ (F := ZMod 2) = BinaryParabolicPair.firstParabolic := by
  unfold parabolic₁
  rw [borel_binary]
  rfl

theorem local₂_binary : local₂ (F := ZMod 2) = BinaryCore.secondParabolic := by
  change unipotent ⊔ Subgroup.closure {weylR} = borel ⊔ Subgroup.closure {weylR}
  rw [borel_binary]

theorem binary_overlap : parabolic₁ (F := ZMod 2) ⊓ parabolic₂ = borel := by
  rw [parabolic₁_binary, borel_binary]
  exact BinaryParabolicPair.parabolic_intersection

theorem local₁_binary_pCore : (local₁ (F := ZMod 2)).pCoreIn 2 = radical₁ := by
  rw [local₁_binary, radical₁_binary]
  exact BinaryParabolicPair.firstParabolic_pCore

noncomputable def local₁_binary_coreEquiv : pCore 2 (local₁ (F := ZMod 2)) ≃* radical₁ (F := ZMod 2) :=
  (Subgroup.equivMapOfInjective _ (local₁ (F := ZMod 2)).subtype
    (local₁ (F := ZMod 2)).subtype_injective).trans
      (MulEquiv.subgroupCongr local₁_binary_pCore)

end Atlas.G2.LieParabolicSetup
