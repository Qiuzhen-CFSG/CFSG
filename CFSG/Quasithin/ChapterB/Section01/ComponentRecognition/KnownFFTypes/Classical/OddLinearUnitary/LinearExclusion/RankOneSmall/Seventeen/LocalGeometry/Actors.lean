module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen.Reduction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.ProjectiveDegree
public import Theory.SpecificGroups.PSL2.InvolutionFusion

/-!
# Frobenius actors in the compatible PSL₂(17) component

The proved universal double-cover theorem, together with the trivial binary
component two-core, first identifies the actual component with PSL₂(17).
A field isomorphism to ZMod 17 then transports the concrete root and torus
actors. Involution fusion is transported through the same actual component.
No centerless-cover or inner-ambient-action hypothesis is imposed.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript p.9; Aschbacher--Smith K.2, printed p.453.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- A genuine isomorphism of the source component with the prime-field model.
The compatible covering center is eliminated by the checked universal-cover
and modular two-core theorems. -/
theorem source_component_equiv_seventeen
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17) :
    Nonempty (generalizedFitting G ≃* Theory.PSL2.SeventeenFrobenius.Model) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := RankOneSize.source_component_isPSL ρ h
    (by decide) (by decide) (by decide) hm
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod 17 := (ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  exact ⟨e.trans (Atlas.fieldEquivPSL 2 f)⟩

/-- The 17:8 generators live in the actual component inside G. -/
theorem source_component_frobenius_actors
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17) :
    ∃ x r : G, x ∈ generalizedFitting G ∧ r ∈ generalizedFitting G ∧
      orderOf x = 17 ∧ orderOf r = 8 ∧ r * x * r⁻¹ = x ^ 2 := by
  obtain ⟨e⟩ := source_component_equiv_seventeen ρ h hm
  let x := e.symm Theory.PSL2.SeventeenFrobenius.root
  let r := e.symm Theory.PSL2.SeventeenFrobenius.generator
  refine ⟨x, r, x.property, r.property, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact (e.symm.orderOf_eq _).trans Theory.PSL2.SeventeenFrobenius.root_order
  · rw [Subgroup.orderOf_coe]
    exact (e.symm.orderOf_eq _).trans Theory.PSL2.SeventeenFrobenius.generator_order
  · have he : r * x * r⁻¹ = x ^ 2 := by
      simpa only [r, x, map_mul, map_inv, map_pow] using
        congrArg e.symm Theory.PSL2.SeventeenFrobenius.generator_conjugates_root
    exact congrArg (generalizedFitting G).subtype he

/-- Fusion of any two actual inner involutions, without assuming all ambient
involutions are inner. -/
theorem source_inner_involutions_isConj
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    {a b : G} (haL : a ∈ generalizedFitting G) (hbL : b ∈ generalizedFitting G)
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := RankOneSize.source_component_isPSL ρ h
    (by decide) (by decide) (by decide) hm
  let aL : generalizedFitting G := ⟨a, haL⟩
  let bL : generalizedFitting G := ⟨b, hbL⟩
  have ha' : orderOf (e aL) = 2 := by
    rw [e.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ha
  have hb' : orderOf (e bL) = 2 := by
    rw [e.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hb
  have hc := Theory.PSL2.involutions_isConj (K := F) (e aL) (e bL) ha' hb'
  have hcL : IsConj aL bL := by simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using e.symm.toMonoidHom.map_isConj hc
  exact (generalizedFitting G).subtype.map_isConj hcL

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
