module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.SectionStructure.SourceAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.Images
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.Quotient

/-!
# Dimensions of the literal local images in U_L/V

The subgroup-image cardinality is the relative index of its denominator.
For U_H the marked natural U_H/V₁ has dimension four and the image of V₃
has dimension two, so the V₃-index is four. The source intersection
V ∩ U_H = V₃ then gives a plane in U_L/V. For U₂, its supplied rank six
and the original natural module V of order sixteen give the second plane.
The argument requires only relative normality and an elementary quotient;
it does not assume U_L is abelian.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.6(4), printed p.948 (PDF p.965), using 13.8.4(5).
The commutator generation and local actor identifications are separate.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]

/-- The image uses the actual relative index, even for a nonabelian numerator. -/
theorem card_sectionImage (B Z D : Subgroup G) [(Z.subgroupOf B).Normal]
    [IsElementaryAbelian 2 (B ⧸ Z.subgroupOf B)] (hDB : D ≤ B) :
    Nat.card (sectionImage B Z D) = Z.relIndex D := by
  change Nat.card ((D.subgroupOf B).map (QuotientGroup.mk' (Z.subgroupOf B))) = _
  rw [← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf hDB]

/-- Convert relative index to the dimension of the literal binary image. -/
theorem pow_finrank_sectionImage [Finite G] (B Z D : Subgroup G)
    [(Z.subgroupOf B).Normal] [IsElementaryAbelian 2 (B ⧸ Z.subgroupOf B)] (hDB : D ≤ B) :
    2 ^ Module.finrank (ZMod 2) (sectionImage B Z D) = Z.relIndex D := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := sectionImage B Z D)
  rw [Nat.card_zmod] at hc
  exact hc.symm.trans (card_sectionImage B Z D hDB)

/-- The marked four-space modulo its marked plane has order four. -/
theorem UH_relativeIndex_four [Finite G]
    (H V₁ V₃ : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) U)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (h13 : V₁ ≤ V₃)
    (E : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hmark : (s.image V₃).map E.toLinearMap = canonicalPlane) :
    V₃.relIndex (Source.UH H V₃) = 4 := by
  let : Finite U := Finite.of_surjective (fun u => (s.quotient u).toAdd) s.surjective
  let C := (V₃.subgroupOf (Source.UH H V₃)).map s.quotient
  have hd : Module.finrank (ZMod 2) (s.image V₃) = 2 := by
    rw [← E.finrank_map_eq, hmark, canonicalPlane_finrank]
  have hc : Nat.card C = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := s.image V₃)
    rw [Nat.card_zmod, hd] at h
    exact h
  have hU : Nat.card (Multiplicative U) = 16 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
    rw [Nat.card_zmod, E.finrank_eq,
      BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at h
    exact h
  have hi := C.card_mul_index
  rw [hc, hU] at hi
  have hrel := s.relativeIndex_image (Source.UH H V₃) V₃ le_rfl h13
  rw [subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr s.surjective,
    relIndex_top_right] at hrel
  change C.index = V₃.relIndex (Source.UH H V₃) at hrel
  omega

/-- The source intersection identifies U_H V/V with the order-four section. -/
theorem UH_image_finrank [Finite G]
    (L H V V₁ V₃ : Subgroup G)
    [(V.subgroupOf (Source.UL L H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.ULsection L H V₃ V)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) U)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (h13 : V₁ ≤ V₃)
    (E : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hmark : (s.image V₃).map E.toLinearMap = canonicalPlane)
    (hinter : V ⊓ Source.UH H V₃ = V₃) :
    Module.finrank (ZMod 2) (sectionImage (Source.UL L H V₃) V (Source.UH H V₃)) = 2 := by
  have hr : V.relIndex (Source.UH H V₃) = 4 := by
    rw [← inf_relIndex_left, inf_comm, hinter]
    exact UH_relativeIndex_four H V₁ V₃ ρ s h13 E hmark
  have hp := pow_finrank_sectionImage (Source.UL L H V₃) V (Source.UH H V₃)
    (le_conjugateSpanBy _ _)
  rw [hr] at hp
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hp

/-- The original natural L-module V has order sixteen when C_V(L)=1. -/
theorem original_V_card (L T V V₁ : Subgroup G)
    (n : NaturalSetup L T V V₁) (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card V = 16 := by
  have hc := Nat.card_congr (Equiv.ofBijective n.naturalMap
    ⟨SectionStructure.original_naturalMap_injective L T V V₁ n hfixed,
      n.naturalMap_surjective⟩)
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := BinaryPermutation.natural (Fin 6))
  rw [Nat.card_zmod, BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at h
  exact hc.trans h

/-- The parabolic rank-six output gives a second plane and U₂ ≠ V. -/
theorem U2_image_finrank [Finite G]
    (L H T V V₁ V₂ V₃ : Subgroup G)
    [(V.subgroupOf (Source.UL L H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.ULsection L H V₃ V)]
    [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]
    (n : NaturalSetup L T V V₁) (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hU : Source.U2 H V V₂ ≤ Source.UL L H V₃)
    (hrank : Module.finrank (ZMod 2) (Additive (Source.U2 H V V₂)) = 6) :
    Module.finrank (ZMod 2) (sectionImage (Source.UL L H V₃) V (Source.U2 H V V₂)) = 2 ∧
      Source.U2 H V V₂ ≠ V := by
  have hV := original_V_card L T V V₁ n hfixed
  have hUcard : Nat.card (Source.U2 H V V₂) = 64 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (Source.U2 H V V₂))
    rw [Nat.card_zmod, hrank] at h
    exact h
  have hi := (V.subgroupOf (Source.U2 H V V₂)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (Source.seed_le_U2 H V V₂)).toEquiv, hV,
    hUcard] at hi
  change 16 * V.relIndex (Source.U2 H V V₂) = 64 at hi
  have hp := pow_finrank_sectionImage (Source.UL L H V₃) V (Source.U2 H V V₂) hU
  have hr : V.relIndex (Source.U2 H V V₂) = 4 := by omega
  rw [hr] at hp
  refine ⟨Nat.pow_right_injective (by decide : 2 ≤ 2) hp, ?_⟩
  intro he
  rw [he, hV] at hUcard
  contradiction
end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

end
