module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedTransitivity
/-!
# The original source plane is one point modulo the source line

The literal image of V₂ in U_H/V₁ has order two and dimension one. Every
nonzero original plane vector therefore spans that image. This supplies
the exact point subspace used in the simultaneous seven-letter flag marking.

Source: Aschbacher–Smith, 13.7.6(iii), printed p.939.
-/
@[expose] public section
open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition
open Section08.TransvectionParabolic.Marking
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d
/-- The image of the original plane is one-dimensional. -/
theorem plane_section_finrank : finrank (ZMod 2) (sectionImage H V₃ V₁ V₂) = 1 := by
  have hcard := (V₁.subgroupOf V₂).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe d.line_le_plane).toEquiv, d.line_card, d.plane_card] at hcard
  have hi : V₁.relIndex V₂ = 2 := by change 2 * V₁.relIndex V₂ = 4 at hcard; omega
  rw [← relIndex_subgroupOf (d.plane_le_seed.trans (le_conjugateSpanBy V₃ H))] at hi
  have hi' : Nat.card (sectionImage H V₃ V₁ V₂) = 2 := by
    let e : sectionImage H V₃ V₁ V₂ ≃
        (V₂.subgroupOf (Section08.Source.UH H V₃)).map
          (QuotientGroup.mk' (V₁.subgroupOf (Section08.Source.UH H V₃))) := {
      toFun := fun x => ⟨x.val.toMul,x.property⟩
      invFun := fun x => ⟨Additive.ofMul x.val,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr e,← relIndex_ker (V₂.subgroupOf (Section08.Source.UH H V₃))
      (QuotientGroup.mk' (V₁.subgroupOf (Section08.Source.UH H V₃))),QuotientGroup.ker_mk']
    exact hi
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := sectionImage H V₃ V₁ V₂)
  rw [Nat.card_zmod,hi'] at hd
  exact (Nat.pow_right_injective (by decide : 1 < 2)) (by simpa using hd.symm)

/-- Every nonzero original plane vector spans the exact quotient point. -/
theorem plane_section_span (v : V₂)
    (hv : seedVector H V₃ V₁ ⟨v,d.plane_le_seed v.property⟩ ≠ 0) :
    sectionImage H V₃ V₁ V₂ = Submodule.span (ZMod 2)
      {seedVector H V₃ V₁ ⟨v,d.plane_le_seed v.property⟩} := by
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ rfl
    exact ⟨⟨v,le_conjugateSpanBy V₃ H (d.plane_le_seed v.property)⟩,v.property,rfl⟩
  · rw [finrank_span_singleton hv,plane_section_finrank d]
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
