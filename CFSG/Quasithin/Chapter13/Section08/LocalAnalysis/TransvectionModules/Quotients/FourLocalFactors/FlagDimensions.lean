module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.Dimensions
/-!
# The index-two source flag from the two actual marked modules

The original natural L-module identifies V₁ with a binary line, so it has
order two. The marked plane V₃/V₁ in the natural U_H/V₁ has order four.
Thus V₃ has order eight and index two in the original V of order sixteen.
This establishes the applicability of the intersection argument in
13.8.4(5) without inserting V∩U_H=V₃ as a new source premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and proofs of 13.8.4(5), 13.8.6(4), printed pp.947–948.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]

/-- The original marked line has order two, using C_V(L)=1. -/
theorem original_V1_card (L T V V₁ : Subgroup G)
    (n : NaturalSetup L T V V₁) (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card V₁ = 2 := by
  rw [n.line_eq, sourceLinePreimage]
  rw [← Nat.card_congr (equivMapOfInjective _ V.subtype Subtype.val_injective).toEquiv]
  rw [Nat.card_congr (equivMapOfInjective _ n.naturalMap
    (SectionStructure.original_naturalMap_injective L T V V₁ n hfixed)).toEquiv]
  rw [map_comap_eq, MonoidHom.range_eq_top.mpr n.naturalMap_surjective, top_inf_eq]
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := n.point)
  rw [Nat.card_zmod, n.point_dim] at hc
  exact hc

/-- The original V and the marked U_H/V₁ give the literal flag index. -/
theorem source_flag_index [Finite G]
    (L H T V V₁ V₃ : Subgroup G)
    (n : NaturalSetup L T V V₁) (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) U)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (h13 : V₁ ≤ V₃) (h3V : V₃ ≤ V)
    (E : U ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hmark : (s.image V₃).map E.toLinearMap = canonicalPlane) :
    V₃.relIndex V = 2 := by
  let : Finite U := Finite.of_surjective (fun u => (s.quotient u).toAdd) s.surjective
  have hd : Module.finrank (ZMod 2) (s.image V₃) = 2 := by
    rw [← E.finrank_map_eq, hmark, canonicalPlane_finrank]
  have hc : V₁.relIndex V₃ = 4 := by
    rw [← relIndex_subgroupOf (le_conjugateSpanBy V₃ H)]
    change (V₁.subgroupOf (Source.UH H V₃)).relIndex
      (V₃.subgroupOf (Source.UH H V₃)) = 4
    rw [← s.kernel, relIndex_ker]
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := s.image V₃)
    rw [Nat.card_zmod, hd] at h
    exact h
  have hcard₃ := (V₁.subgroupOf V₃).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe h13).toEquiv,
    original_V1_card L T V V₁ n hfixed] at hcard₃
  change 2 * V₁.relIndex V₃ = Nat.card V₃ at hcard₃
  rw [hc] at hcard₃
  have hindex := (V₃.subgroupOf V).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe h3V).toEquiv, ← hcard₃,
    original_V_card L T V V₁ n hfixed] at hindex
  change (2 * 4) * V₃.relIndex V = 16 at hindex
  omega
end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

end
