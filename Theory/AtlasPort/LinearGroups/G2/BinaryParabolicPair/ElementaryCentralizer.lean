module
public import Theory.AtlasPort.LinearGroups.G2.BinaryCore

/-!
# The binary G₂ elementary eight is self-centralizing in the Sylow subgroup

The positive-root coordinates identify the common Sylow subgroup. Commuting
with each of the first three root elements forces its last three coordinates
to vanish, leaving exactly the elementary eight. The finite check concerns
only six binary coordinates, using the proved root multiplication law.

This supplies C_T(E) = E for the point-stabilizer argument in
Aschbacher–Smith, Lemma 14.2.21, printed p.988. Root conventions and the
multiplication law come from the licensed ATLAS port imported above.
-/

namespace Atlas.G2.BinaryCore
open scoped IsMulCommutative
set_option maxRecDepth 100000

private theorem elementary_centralizing_parameters (t : Fin 6 → ZMod 2)
    (ht : ∀ j : Fin 3,
      unipotentProductParameters (Pi.single (Fin.castLE (by decide) j) 1) t =
      unipotentProductParameters t (Pi.single (Fin.castLE (by decide) j) 1)) :
    t = ![t 0,t 1,t 2,0,0,0] := by
  have h : ∀ t : Fin 6 → ZMod 2, (∀ j : Fin 3,
      unipotentProductParameters (Pi.single (Fin.castLE (by decide) j) 1) t =
      unipotentProductParameters t (Pi.single (Fin.castLE (by decide) j) 1)) →
      t = ![t 0,t 1,t 2,0,0,0] := by decide +kernel
  exact h t ht

private theorem elementary_root_mem (j : Fin 3) :
    unipotentProduct (Pi.single (Fin.castLE (by decide) j) (1 : ZMod 2)) ∈ elementary := by
  let x : Coordinates := ⟨if j = 0 then 1 else 0, if j = 1 then 1 else 0,
    if j = 2 then 1 else 0, 0, 0⟩
  refine ⟨x, ⟨rfl, rfl⟩, ?_⟩
  change unipotentProduct (parameters x) = _
  congr 1
  revert j
  decide +kernel

public theorem unipotent_centralizer_elementary :
    unipotent (K := ZMod 2) ⊓ Subgroup.centralizer
      (elementary : Set (Model (ZMod 2))) = elementary := by
  apply le_antisymm
  · rintro g ⟨hg, hc⟩
    obtain ⟨t, rfl⟩ := (show g ∈ unipotentRange from
      (unipotent_eq_range (K := ZMod 2)) ▸ hg)
    have ht := elementary_centralizing_parameters t (fun j => by
      apply unipotentProduct_injective
      rw [← unipotentProduct_mul, ← unipotentProduct_mul]
      exact hc _ (elementary_root_mem j))
    refine ⟨⟨t 0,t 1,t 2,0,0⟩, ⟨rfl,rfl⟩, ?_⟩
    change unipotentProduct (parameters _) = unipotentProduct t
    exact congrArg unipotentProduct ht.symm
  · intro g hg
    refine ⟨core_le_unipotent (elementary_le_core hg), ?_⟩
    intro x hx
    exact congrArg Subtype.val (mul_comm (⟨x,hx⟩ : elementary) ⟨g,hg⟩)
end Atlas.G2.BinaryCore
