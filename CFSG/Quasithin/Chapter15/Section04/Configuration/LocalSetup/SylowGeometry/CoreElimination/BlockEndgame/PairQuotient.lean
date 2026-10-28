module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.Models

/-!
# Four-group bounds through a quotient of the two block layers

An internal product of blocks need not be an external direct product. Given a
homomorphism from the two commutator layers whose kernel lies in their central
fixed layers, the natural pair-module map descends to its image. Its image on
an invariant subgroup therefore has cardinality at most the subgroup's image
in the ambient group. This permits the Borel bound without a splitting or a
four-element lift in the external product.

Commutator generation in the ambient group proves that the module image is
nontrivial, provided the images of the fixed layers centralize the actor. The
source placement proof must construct the homomorphism, its kernel bound,
this centralization, and invariance under the actual product Borel. These
lemmas do not assume or assert that the source blocks form a direct product.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the natural
block modules in C.1.7 and C.1.12, and the proof of 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame

private theorem card_map_le_of_ker_le {D A B : Type*}
    [Group D] [Group A] [Group B] [Finite D]
    (f : D →* A) (g : D →* B) (hker : f.ker ≤ g.ker) (W : Subgroup D) :
    Nat.card (W.map g) ≤ Nat.card (W.map f) := by
  let fW := f.subgroupMap W
  let gW := g.subgroupMap W
  let : Finite (W.map f) := Finite.of_surjective fW (f.subgroupMap_surjective W)
  have hkg : fW.ker ≤ gW.ker := by
    intro w hw
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact hker (congrArg Subtype.val (MonoidHom.mem_ker.mp hw))
  let q := QuotientGroup.lift fW.ker gW (fun w hw => hkg hw)
  let e := QuotientGroup.quotientKerEquivOfSurjective fW (f.subgroupMap_surjective W)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨w, rfl⟩ := g.subgroupMap_surjective W y
    exact ⟨QuotientGroup.mk' fW.ker w, rfl⟩
  exact Nat.card_le_card_of_surjective (q.comp e.symm.toMonoidHom)
    (hq.comp e.symm.surjective)

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame
variable {L₁ L₂ F A : Type*} [Group L₁] [Group L₂] [Group A] [Field F]
variable (m₁ : BlockModuleModel L₁ (Matrix.SL2.naturalAction F))
    (m₂ : BlockModuleModel L₂ (Matrix.SL2.naturalAction F))

/-- The field order is bounded by the ambient image, even when its lift is larger. -/
theorem pairBorelLift_image_card_bound [Finite L₁] [Finite L₂] [Finite F] [CharP F 2]
    (hq : 4 ≤ Nat.card F) (f : (blockU L₁ × blockU L₂) →* A)
    (hker : f.ker ≤ (blockFixed L₁).prod (blockFixed L₂))
    (W : Subgroup (blockU L₁ × blockU L₂))
    (hne : W.map (pairModuleMap m₁ m₂) ≠ ⊥)
    (hinv : ∀ l ∈ pairBorelLift m₁ m₂, ∀ w ∈ W,
      (blockConjugate L₁ l.1 w.1, blockConjugate L₂ l.2 w.2) ∈ W) :
    Nat.card F ≤ Nat.card (W.map f) := by
  have hact : ∀ a ∈ (BenderSuzuki.Converse.Borel F).prod (BenderSuzuki.Converse.Borel F),
      ∀ v ∈ W.map (pairModuleMap m₁ m₂),
      Matrix.SL2.naturalPairAction F a v ∈ W.map (pairModuleMap m₁ m₂) := by
    intro a ha v hv
    obtain ⟨l, hl, rfl⟩ := (pairBorelLift_map m₁ m₂ hq).symm ▸ ha
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨_, hinv l hl w hw, pairModuleMap_intertwining m₁ m₂ l w⟩
  rw [← rankOneBorel_eq_sourceBorel] at hact
  exact (Matrix.SL2.card_le_of_naturalPairAction_borel_invariant _ hne hact).trans
    (card_map_le_of_ker_le f (pairModuleMap m₁ m₂)
      (by rwa [pairModuleMap_ker]) W)

/-- Ambient commutator generation prevents the whole subgroup being lost in the fixed layers. -/
theorem pair_nontrivial_module_image_of_image_commutator
    (f : (blockU L₁ × blockU L₂) →* A) (D : Subgroup A)
    (hfixed : ((blockFixed L₁).prod (blockFixed L₂)).map f ≤ centralizer (D : Set A))
    (W : Subgroup (blockU L₁ × blockU L₂)) (hne : W.map f ≠ ⊥)
    (hcomm : ⁅W.map f, D⁆ = W.map f) :
    W.map (pairModuleMap m₁ m₂) ≠ ⊥ := by
  intro he
  have hWF : W ≤ (blockFixed L₁).prod (blockFixed L₂) := by
    rwa [Subgroup.map_eq_bot_iff, pairModuleMap_ker] at he
  have hc := commutator_eq_bot_iff_le_centralizer.mpr ((map_mono hWF).trans hfixed)
  rw [hcomm] at hc
  exact hne hc

/-- An invariant four-group image forces field four without requiring a subgroup splitting. -/
theorem pairBorelLift_image_field_bound [Finite L₁] [Finite L₂] [Finite F] [CharP F 2]
    (hq : 4 ≤ Nat.card F) (f : (blockU L₁ × blockU L₂) →* A)
    (hker : f.ker ≤ (blockFixed L₁).prod (blockFixed L₂))
    (D : Subgroup A)
    (hfixed : ((blockFixed L₁).prod (blockFixed L₂)).map f ≤ centralizer (D : Set A))
    (W : Subgroup (blockU L₁ × blockU L₂)) (hcard : Nat.card (W.map f) = 4)
    (hcomm : ⁅W.map f, D⁆ = W.map f)
    (hinv : ∀ l ∈ pairBorelLift m₁ m₂, ∀ w ∈ W,
      (blockConjugate L₁ l.1 w.1, blockConjugate L₂ l.2 w.2) ∈ W) :
    Nat.card F = 4 := by
  have hne : W.map f ≠ ⊥ := by intro he; rw [he] at hcard; simp at hcard
  have hb := pairBorelLift_image_card_bound m₁ m₂ hq f hker W
    (pair_nontrivial_module_image_of_image_commutator m₁ m₂ f D hfixed W hne hcomm) hinv
  exact Nat.le_antisymm (hcard ▸ hb) hq

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame
