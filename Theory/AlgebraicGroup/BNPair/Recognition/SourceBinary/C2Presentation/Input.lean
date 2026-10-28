module
public import Theory.SpecificGroups.SymplecticFour.RootPresentation.Presentation
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SplitCore
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.MarkedQuotient
import Mathlib.Tactic.FinCases

/-!
# Explicit C₂ input on the same marked finite quotient

These data retain all eight additive roots, the literal chamber relations,
whole-group and positive generation, and the two oriented negative-root
placements. The presentation gives an onto map to this very quotient. Positive
collection also gives an onto map from concrete U to its specified split U.
Thus the source root equations have a concrete, usable presentation consumer.
Neither map is asserted injective on the whole group. The Weyl, torus and
Bruhat arguments needed to construct a map from Sp₄ remain separate work.

The numerator X need not be finite. This is the finite split quotient used in
DGS, Groups and Graphs, Theorem D, printed p.224, with C₂ relations from
Steinberg §6, pp.68–74. Source reconstruction of these root data is an input.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
open RootPresentation PositiveRelations
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2Presentation
variable {X F : Type*} [Group X] [Field F]
variable {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The rank-two marking itself rules out quotient orders one and two.
No simplicity or root-coordinate nondegeneracy is required. -/
theorem two_lt_card : 2 < Nat.card (X ⧸ Q.D) := by
  let W := Q.tits.N ⧸ (Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N
  have h0 : Q.simple 0 ≠ 1 := (Q.tits.involutions _ (Q.simple_mem 0)).1
  have h1 : Q.simple 1 ≠ 1 := (Q.tits.involutions _ (Q.simple_mem 1)).1
  have h01 : Q.simple 0 ≠ Q.simple 1 := fun h => (by decide : (0 : Fin 2) ≠ 1)
    (Q.simple_injective h)
  have hi : Function.Injective (![1,Q.simple 0,Q.simple 1] : Fin 3 → W) := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all
  have h3 : 3 ≤ Nat.card W := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective _ hi
  have hW : Nat.card W ≤ Nat.card Q.tits.N := Nat.card_le_card_of_surjective _
    (QuotientGroup.mk'_surjective ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N))
  have hN : Nat.card Q.tits.N ≤ Nat.card (X ⧸ Q.D) :=
    Nat.card_le_card_of_injective _ Q.tits.N.subtype_injective
  exact lt_of_lt_of_le (by decide : 2 < 3) (h3.trans (hW.trans hN))

/-- The actual eight-root contract; no ambient matrix map or word faithfulness
is hidden in its fields. Local characteristic two comes from source markings. -/
structure RootData where
  x : Fin 8 → Multiplicative F →* (X ⧸ Q.D)
  relations : Relations (fun r t => x r (.ofAdd t))
  generate : closure {g | ∃ r t, x r (.ofAdd t) = g} = ⊤
  positive : positiveSubgroup (fun r t => x r (.ofAdd t)) = split.U
  negative_long : x 3 (.ofAdd 1) ∈ Q.tits.standardParabolic {Q.simple 0}
  negative_short : x 7 (.ofAdd 1) ∈ Q.tits.standardParabolic {Q.simple 1}

namespace RootData
variable {Q split} (d : RootData (F := F) Q split)
include d

/-- This map targets X/Q.D, including when X is an infinite completion. -/
def presentationMap : SteinbergGroup F →* (X ⧸ Q.D) := lift d.relations

@[simp] theorem presentationMap_generator (r : Fin 8) (t : F) :
    d.presentationMap (generator r t) = d.x r (.ofAdd t) := lift_generator _ _ _

theorem presentationMap_surjective : Function.Surjective d.presentationMap :=
  lift_surjective d.relations d.generate

variable [Finite F] [CharP F 2]

/-- The concrete positive group maps to the specified source Sylow group. -/
def unipotentMap : unipotent (F := F) →* (X ⧸ Q.D) := d.relations.positive.unipotentMap

theorem unipotentMap_range : d.unipotentMap.range = split.U :=
  d.relations.positive.unipotentMap_range.trans d.positive

/-- Source U has an ordered product in its four literal positive root maps. -/
theorem positive_normal_form (g : X ⧸ Q.D) (hg : g ∈ split.U) :
    ∃ b k w v : F, d.x 6 (.ofAdd b) * d.x 0 (.ofAdd k) *
      d.x 4 (.ofAdd w) * d.x 2 (.ofAdd v) = g :=
  d.relations.positive.positive_normal_form g (d.positive ▸ hg)

/-- Positive collection removes any need to assume an extra upper-order bound. -/
theorem card_unipotent_le : Nat.card split.U ≤ Nat.card F ^ 4 := by
  let f : unipotent (F := F) → split.U := fun u =>
    ⟨d.unipotentMap u, d.unipotentMap_range ▸ (show d.unipotentMap u ∈ d.unipotentMap.range from ⟨u,rfl⟩)⟩
  have hf : Function.Surjective f := by
    intro u
    have hu : (u : X ⧸ Q.D) ∈ d.unipotentMap.range := d.unipotentMap_range.symm ▸ u.property
    obtain ⟨v,hv⟩ := hu
    exact ⟨v,Subtype.ext hv⟩
  simpa only [card_unipotent] using Nat.card_le_card_of_surjective f hf

end RootData
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.C2Presentation
