module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Definitions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions.Transport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.SixExtension
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The same source action in the critical comparison

Conjugation constructs the representation on the literal U_H/V1. Conversely,
any source representation satisfies the same formula as the quotient action
used by the critical-geometry theorems. A nonidentity transvection has fixed
codimension one, so absence of these actors passes between the two APIs.
No module recognition or faithfulness assumption is introduced.

Source: Aschbacher--Smith, F.9.2 and 13.8.8,18,21, printed pp.318,949,953,957.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison
open CriticalGeometry CriticalGeometry.SectionActions
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open ComponentSieve.FieldComponents.LinearThree
variable {G : Type*} [Group G] [Finite G] {H V₃ V₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

noncomputable def conjugationAction
    (hline : V₁ ≤ Source.UH H V₃) (hseed : V₃ ≤ H)
    (hz : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) : SourceAction H V₃ V₁ where
  line_le := hline
  seed_le := hseed
  representation := {
    toFun := fun a => (binaryLinear (uStarAction H V₃ V₁ hz hQ a)).toLinearMap
    map_one' := by
      ext v
      change Additive.ofMul (uStarAction H V₃ V₁ hz hQ 1 v.toMul) = v
      rw [map_one]
      rfl
    map_mul' := by
      intro a b
      ext v
      change Additive.ofMul (uStarAction H V₃ V₁ hz hQ (a*b) v.toMul) = _
      rw [map_mul]
      rfl }
  conjugation := by
    intro h u
    change Additive.ofMul (uStarAction H V₃ V₁ hz hQ (QuotientGroup.mk' (pCore 2 H) h)
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) = _
    rw [uStarAction_mk]
    exact congrArg Additive.ofMul (quotientAction_apply H (Source.UH H V₃) V₁
      (le_normalizer_conjugateSpanBy V₃ H) hz h u)

noncomputable def sourceSection (act : SourceAction H V₃ V₁)
    (hz : H ≤ centralizer (V₁ : Set G)) :
    ConjugationSection H (Source.UH H V₃) V₁ act.representation where
  le := conjugateSpanBy_le_self act.seed_le
  normalizes := le_normalizer_conjugateSpanBy V₃ H
  centralizes := hz
  line_le := act.line_le
  quotient := {
    toFun := fun u => Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  surjective := QuotientGroup.mk'_surjective _
  kernel := QuotientGroup.ker_mk' _
  conjugates := act.conjugation

omit [Finite G] in
theorem sourceAction_eq (act : SourceAction H V₃ V₁)
    (hz : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (a : Source.Hstar H) (v : Additive (Source.Utilde H V₃ V₁)) :
    act.representation a v = binaryLinear (uStarAction H V₃ V₁ hz hQ a) v := by
  obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) a
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  change act.representation _ (Additive.ofMul (QuotientGroup.mk' _ u)) = _
  rw [act.conjugation,uStarAction_mk]
  change _ = Additive.ofMul (uAction H V₃ V₁ hz h (QuotientGroup.mk' _ u))
  exact congrArg Additive.ofMul (quotientAction_apply H (Source.UH H V₃) V₁
    (le_normalizer_conjugateSpanBy V₃ H) hz h u).symm

theorem no_source_transvection (act : SourceAction H V₃ V₁)
    (hz : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hno : ∀ a : Source.Hstar H, fixedCodim act.representation (zpowers a) ≠ 1) :
    ∀ a : Source.Hstar H, uStarAction H V₃ V₁ hz hQ a ≠ 1 →
      binaryLinear (uStarAction H V₃ V₁ hz hQ a) ∉
        LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := by
  intro a ha ht
  obtain ⟨f,z,hfz,he⟩ := ht
  have hform (v : Additive (Source.Utilde H V₃ V₁)) :
      act.representation a v = v + f v • z := by
    rw [sourceAction_eq act hz hQ,he,LinearEquiv.transvection.apply]
  have hf : f ≠ 0 := by
    intro hf
    apply ha
    ext v
    have hv := hform (Additive.ofMul v)
    rw [sourceAction_eq act hz hQ] at hv
    have hv' : binaryLinear (uStarAction H V₃ V₁ hz hQ a) (Additive.ofMul v) = Additive.ofMul v := by simpa [hf] using hv
    exact congrArg Additive.toMul hv'
  have hz' : z ≠ 0 := by
    intro hz'
    apply ha
    ext v
    have hv := hform (Additive.ofMul v)
    rw [sourceAction_eq act hz hQ] at hv
    have hv' : binaryLinear (uStarAction H V₃ V₁ hz hQ a) (Additive.ofMul v) = Additive.ofMul v := by simpa [hz'] using hv
    exact congrArg Additive.toMul hv'
  apply hno a
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact TransvectionRecognition.Component.transvection_displacement_rank
    ⟨f,z,hf,hz',hfz,hform⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Comparison
