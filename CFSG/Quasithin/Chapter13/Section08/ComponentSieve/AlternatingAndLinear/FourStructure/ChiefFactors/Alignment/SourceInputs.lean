module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceSeed

/-!
# Recovering the linear seed from the earlier source section

The subgroup V₃ maps into the actual U_H/V₁. Its image has order
[V₃ : V₁ ∩ V₃], so the source index four gives binary dimension two.
The earlier invariant-subgroup criterion proves irreducibility through
pullback along the literal quotient, and normalization gives invariance.
Together with H-conjugate generation this constructs the GeneratingSeed
used by the maximal-quotient argument. All normality is relative to U_H.

The inputs are the original subgroup statements about V₃/V₁, not assertions
about the heads of U_H/V₁. Source: Aschbacher–Smith, combined manuscript
(1 March 2004), §13.2 notation, §13.5 standing flag, and the uses of this
irreducible two-space in 13.8.16 and 13.8.25, printed pp.952,960–961.
-/

@[expose] public section

open Representation Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
variable {G : Type*} [Group G] [Finite G] (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The source relative index computes the dimension of its literal image. -/
theorem sourceSeed_finrank_of_index (hindex : V₁.relIndex V₃ = 4) :
    Module.finrank (ZMod 2) (sourceSeedSpace H V₃ V₁) = 2 := by
  let I := (V₃.subgroupOf (Source.UH H V₃)).map (sourceProjection H V₃ V₁)
  let e : (sourceSeedSpace H V₃ V₁) ≃ I := {
    toFun := fun v => ⟨v.val.toMul, v.property⟩
    invFun := fun v => ⟨Additive.ofMul v.val, v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc : Nat.card (sourceSeedSpace H V₃ V₁) = 4 := by
    rw [Nat.card_congr e, ← Subgroup.relIndex_ker]
    change (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))).ker.relIndex
      (V₃.subgroupOf (Source.UH H V₃)) = 4
    rw [QuotientGroup.ker_mk']
    exact (Subgroup.relIndex_subgroupOf (H := V₁) (L := Source.UH H V₃)
      (show V₃ ≤ Source.UH H V₃ from le_conjugateSpanBy V₃ H)).trans hindex
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) (hc.trans (by decide : 4 = 2 ^ 2))

open Components.Swapped.LinearTwo.ModuleAlternatives
/-- Construct the linear seed from the literal earlier invariant-subgroup criterion and index. -/
noncomputable def sourceSeedOfEarlier
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) (P T : Subgroup G)
    (hPH : P ≤ H) (hTP : T ≤ P) (hT : IsPGroup 2 T)
    (hN : P ≤ normalizer (V₃ : Set G)) (hline : V₁ < V₃)
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      P ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃)
    (hindex : V₁.relIndex V₃ = 4) : GeneratingSeed ρ where
  parabolic := Source.starImage H P
  sylow := Source.starImage H T
  sylow_le := Subgroup.map_mono (Subgroup.subgroupOf_mono H hTP)
  sylow_two_group := (starImage_isPGroup_iff H T (hTP.trans hPH)).mpr hT
  space := markedSeed H V₃ V₁ ρ hρ P hN
  irreducible := (Subrepresentation.irreducible_iff_isAtom _).mp
    (markedSeed_irreducible H V₃ V₁ ρ hρ P hPH hN hline hirr)
  dim_two := sourceSeed_finrank_of_index H V₃ V₁ hindex
  generates := sourceSeedSpace_generates H V₃ V₁ ρ hρ

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
