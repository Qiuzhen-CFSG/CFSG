module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Transvections
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.FieldTheory.Finiteness

/-!
# The corrected rank-one argument of 13.8.10

The actual star image in H/O₂(H) has order equal to the index of the
intersection with O₂(H). The F.9.13 kernel identity and F.9.16 comparison
therefore turn a star image of order two into one-dimensional quotients
on both ends of the critical pair. If V₁ is outside Uγ, the fixed subgroup
is Dγ. Its index two forces the actual conjugation maps on Uγ to be
linear transvections with that common axis.

This retains the strict inclusion D_H<U_H, correcting the reversed
inequality in the printed statement. The F.9 kernel/comparison inputs
remain explicit, as required for the conditional §13.8 development.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma
13.8.10 and Remark F.9.17, printed pp.950 and 324.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
variable {G : Type*} [Group G]

def conjugationAction (P U : Subgroup G) (hn : P ≤ normalizer (U : Set G)) :
    P →* MulAut U :=
  let _ := conjMulDistribMulActionOfLeNormalizer P U hn
  MulDistribMulAction.toMulAut P U

theorem conjugationAction_apply (P U : Subgroup G)
    (hn : P ≤ normalizer (U : Set G)) (p : P) (u : U) :
    (conjugationAction P U hn p u : G) = (p : G) * u * (p : G)⁻¹ := rfl

theorem conjugationAction_fixed (P U : Subgroup G)
    (hn : P ≤ normalizer (U : Set G)) :
    FixedPoints.subgroup (conjugationAction P U hn).range U =
      (centralizer (P : Set G)).subgroupOf U := by
  ext u
  constructor
  · intro hu
    apply mem_centralizer_iff.mpr
    intro p hp
    have hh := hu ⟨conjugationAction P U hn ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩⟩
    have hh' : p * (u : G) * p⁻¹ = u := congrArg Subtype.val hh
    have hh'' := congrArg (fun x : G => x * p) hh'
    simpa only [mul_assoc, inv_mul_cancel, mul_one, coe_subtype] using hh''
  · intro hu a
    obtain ⟨p, hp⟩ := a.property
    apply Subtype.ext
    change ((a : MulAut U) u : G) = u
    rw [← hp, conjugationAction_apply]
    have hh := mem_centralizer_iff.mp hu p p.property
    simp only [coe_subtype] at hh
    rw [hh, mul_inv_cancel_right]

theorem binary_finrank_eq_one {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hc : Nat.card E = 2) :
    Module.finrank (ZMod 2) (Additive E) = 1 := by
  apply Nat.pow_right_injective (by decide : 1 < 2)
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
  change Nat.card E = _ at hh
  simpa only [Nat.card_zmod, pow_one, hc] using hh.symm

theorem corrected_rank_one [Finite G]
    (UH Uγ A₁ V₁ : Subgroup G) [IsElementaryAbelian 2 UH]
    [IsElementaryAbelian 2 Uγ]
    (hproper : Source.DH UH Uγ A₁ < UH)
    (hcomparison : (Source.DH UH Uγ A₁).relIndex UH ≤
      (Source.Dgamma Uγ UH V₁).relIndex Uγ)
    (hγ : (Source.Dgamma Uγ UH V₁).relIndex Uγ = 2)
    (hline : Nat.card V₁ = 2)
    (hn : UH ≤ normalizer (Uγ : Set G))
    (hline_norm : Uγ ≤ normalizer (V₁ : Set G)) :
    Module.finrank (ZMod 2) (Additive (UH ⧸ (Source.DH UH Uγ A₁).subgroupOf UH)) = 1 ∧
      (V₁ ≤ Uγ ∨
        (FixedPoints.subgroup (conjugationAction UH Uγ hn).range Uγ =
            (Source.Dgamma Uγ UH V₁).subgroupOf Uγ ∧
          ((Source.Dgamma Uγ UH V₁).subgroupOf Uγ).index = 2 ∧
          ∀ u : UH, binaryLinear (conjugationAction UH Uγ hn u) ∈
            LinearEquiv.transvections (ZMod 2) (Additive Uγ))) := by
  obtain ⟨hindex, hcases⟩ := corrected_13_8_10_fixed_hyperplane
    UH Uγ A₁ V₁ hproper hcomparison hγ hline hn hline_norm
  refine ⟨binary_finrank_eq_one hindex, ?_⟩
  rcases hcases with hline | ⟨hfixed, hfixedIndex⟩
  · exact Or.inl hline
  · have hfix : FixedPoints.subgroup (conjugationAction UH Uγ hn).range Uγ =
        (Source.Dgamma Uγ UH V₁).subgroupOf Uγ := by
      rw [conjugationAction_fixed, ← hfixed]
      ext u
      exact ⟨fun h => ⟨u.property, h⟩, fun h => h.2⟩
    refine Or.inr ⟨hfix, hγ, ?_⟩
    intro u
    exact transvections_of_fixed_index_two (conjugationAction UH Uγ hn).range
      (by rw [hfix]; exact hγ) _ ⟨u, rfl⟩

/-- The star image has exactly the index of the actual two-core intersection. -/
theorem starImage_card [Finite G] (H X : Subgroup G) (hXH : X ≤ H) :
    Nat.card (Source.starImage H X) = (Source.QH H).relIndex X := by
  change Nat.card ((X.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = _
  rw [← relIndex_ker, QuotientGroup.ker_mk']
  have hcore : (Source.QH H).subgroupOf H = pCore 2 H := by
    change ((pCore 2 H).map H.subtype).comap H.subtype = pCore 2 H
    exact comap_map_eq_self_of_injective H.subtype_injective _
  rw [← hcore, relIndex_subgroupOf hXH]

/-- Corrected 13.8.10 from the actual star-image order and F.9.13/16 inputs.
The two quotient ranks are one; every nonidentity action in the second branch
is a transvection with the common axis Dγ. -/
theorem corrected_rank_one_of_starImage [Finite G]
    (H UH Uγ A₁ V₁ : Subgroup G) [IsElementaryAbelian 2 UH]
    [IsElementaryAbelian 2 Uγ]
    (hUγH : Uγ ≤ H)
    (hstar : Nat.card (Source.starImage H Uγ) = 2)
    (hDγ : Source.Dgamma Uγ UH V₁ = Uγ ⊓ Source.QH H)
    (hproper : Source.DH UH Uγ A₁ < UH)
    (hcomparison : (Source.DH UH Uγ A₁).relIndex UH ≤
      (Source.Dgamma Uγ UH V₁).relIndex Uγ)
    (hline : Nat.card V₁ = 2)
    (hn : UH ≤ normalizer (Uγ : Set G))
    (hline_norm : Uγ ≤ normalizer (V₁ : Set G)) :
    Module.finrank (ZMod 2) (Additive (UH ⧸ (Source.DH UH Uγ A₁).subgroupOf UH)) = 1 ∧
    Module.finrank (ZMod 2) (Additive (Uγ ⧸ (Source.Dgamma Uγ UH V₁).subgroupOf Uγ)) = 1 ∧
      (V₁ ≤ Uγ ∨
        (FixedPoints.subgroup (conjugationAction UH Uγ hn).range Uγ =
            (Source.Dgamma Uγ UH V₁).subgroupOf Uγ ∧
          ((Source.Dgamma Uγ UH V₁).subgroupOf Uγ).index = 2 ∧
          ∀ u : UH, binaryLinear (conjugationAction UH Uγ hn u) ∈
            LinearEquiv.transvections (ZMod 2) (Additive Uγ))) := by
  have hγ : (Source.Dgamma Uγ UH V₁).relIndex Uγ = 2 := by
    rw [hDγ, inf_relIndex_left, ← starImage_card H Uγ hUγH]
    exact hstar
  have hh := corrected_rank_one UH Uγ A₁ V₁ hproper hcomparison hγ hline hn hline_norm
  exact ⟨hh.1, binary_finrank_eq_one hγ, hh.2⟩

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry

end
