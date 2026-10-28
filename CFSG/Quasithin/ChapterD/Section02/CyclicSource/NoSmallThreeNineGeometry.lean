module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeCyclicGeometry
public import Theory.Representation.ElementaryNineSupportGeometry
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The moving-nine fixed-plane geometry on the original source module

The literal support family inside a normal elementary nine-group is transported
to its restricted action. Its three four-dimensional supports give dimension
six, three fixed planes spanning the original module, and a unique excluded
cubic with zero fixed space. Conjugation preserves support dimension, so that
excluded cubic is normal in the original group.

The source commutator fixed-space theorem supplies the moving hypothesis in
D.2.28–29, printed pp.191–192. No model recognition premise is used.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped BigOperators
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Cubic support factors in the literal subgroup and its abstract restriction
have the same cardinality. -/
theorem card_factorsIn (E : Subgroup G) :
    Nat.card {K : {K : Subgroup E // Nat.card K = 3} //
      Module.finrank (ZMod 2) (subspaceCommutator (ρ.comp E.subtype) ⊤ K.val) = 4} =
      Nat.card (fourSpaceThreeFactorsIn ρ E) := by
  let e : {K : {K : Subgroup E // Nat.card K = 3} //
      Module.finrank (ZMod 2) (subspaceCommutator (ρ.comp E.subtype) ⊤ K.val) = 4} ≃
      fourSpaceThreeFactorsIn ρ E := {
    toFun K := ⟨K.val.val.map E.subtype, map_subtype_le _,
      (card_map_of_injective E.subtype_injective).trans K.val.property, by
        rw [← subspaceCommutator_comp_map]
        exact K.property⟩
    invFun D := ⟨⟨D.val.subgroupOf E,
      (Nat.card_congr (subgroupOfEquivOfLe D.property.1).toEquiv).trans D.property.2.1⟩, by
        rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le D.property.1]
        exact D.property.2.2⟩
    left_inv K := by
      apply Subtype.ext
      apply Subtype.ext
      exact comap_map_eq_self_of_injective E.subtype_injective _
    right_inv D := Subtype.ext (map_subgroupOf_eq_of_le D.property.1) }
  exact Nat.card_congr e

private theorem full_line_fixed_span (E : Subgroup G) [IsElementaryAbelian 3 E]
    (hE : Nat.card E = 9) (hfix : fixedSpace ρ E = ⊥) :
    (⨆ K : {K : Subgroup E // Nat.card K = 3},
      fixedSpace ρ (K.val.map E.subtype)) = ⊤ := by
  have ht : (⊤ : Subgroup E).map E.subtype = E := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hf : fixedSpace (ρ.comp E.subtype) ⊤ = ⊥ := by
    rw [fixedSpace_comp_map, ht, hfix]
  simpa only [fixedSpace_comp_map] using
    ElementaryNineFixedDecomposition.iSup_fixed_eq_top (ρ.comp E.subtype) hE hf

/-- The moving-nine support family has at most three members. -/
theorem nine_support_card_le_three (E : Subgroup G) [IsElementaryAbelian 3 E]
    (hE : Nat.card E = 9) (hfix : fixedSpace ρ E = ⊥) :
    Nat.card (fourSpaceThreeFactorsIn ρ E) ≤ 3 := by
  have ht : (⊤ : Subgroup E).map E.subtype = E := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hf : fixedSpace (ρ.comp E.subtype) ⊤ = ⊥ := by
    rw [fixedSpace_comp_map, ht, hfix]
  rw [← card_factorsIn ρ E]
  exact ElementaryNineSupportGeometry.card_support_four_le_three (ρ.comp E.subtype) hE hf

/-- The original three-factor family gives three fixed planes spanning the
module, and the unique excluded cubic is normal and fixed-point-free. -/
theorem CoreHypotheses.nine_support_geometry (h : CoreHypotheses ρ)
    (E : Subgroup G) [E.Normal] [IsElementaryAbelian 3 E]
    (hE : Nat.card E = 9) (hfix : fixedSpace ρ E = ⊥)
    (hS : Nat.card (fourSpaceThreeFactorsIn ρ E) = 3) :
    Module.finrank (ZMod 2) V = 6 ∧
    (∀ D ∈ fourSpaceThreeFactorsIn ρ E,
      Module.finrank (ZMod 2) (fixedSpace ρ D) = 2) ∧
    (⨆ D : fourSpaceThreeFactorsIn ρ E, fixedSpace ρ D.val) = ⊤ ∧
    ∃ Z : Subgroup G, Z ≤ E ∧ Z.Normal ∧ Nat.card Z = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Z) = 6 ∧
      fixedSpace ρ Z = ⊥ ∧
      ∀ D : Subgroup G, D ≤ E → Nat.card D = 3 →
        (D ≠ Z ↔ D ∈ fourSpaceThreeFactorsIn ρ E) := by
  have ht : (⊤ : Subgroup E).map E.subtype = E := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hf : fixedSpace (ρ.comp E.subtype) ⊤ = ⊥ := by
    rw [fixedSpace_comp_map, ht, hfix]
  obtain ⟨hdim, hplanes, Z, hZcard, hZfix, hZsupport, hZchar⟩ :=
    ElementaryNineSupportGeometry.geometry (ρ.comp E.subtype) hE
      (h.faithful.comp E.subtype_injective) hf ((card_factorsIn ρ E).trans hS)
  let ZG := Z.map E.subtype
  have hZGle : ZG ≤ E := map_subtype_le _
  have hZGcard : Nat.card ZG = 3 :=
    (card_map_of_injective E.subtype_injective).trans hZcard
  have hZGfix : fixedSpace ρ ZG = ⊥ := by
    rw [← fixedSpace_comp_map]
    exact hZfix
  have hZGsupport : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ZG) = 6 := by
    rw [← subspaceCommutator_comp_map]
    exact hZsupport
  have hchar (D : Subgroup G) (hDE : D ≤ E) (hD : Nat.card D = 3) :
      D ≠ ZG ↔ D ∈ fourSpaceThreeFactorsIn ρ E := by
    have hDc : Nat.card (D.subgroupOf E) = 3 :=
      (Nat.card_congr (subgroupOfEquivOfLe hDE).toEquiv).trans hD
    have hm := hZchar (D.subgroupOf E) hDc
    have hn : D.subgroupOf E ≠ Z ↔ D ≠ ZG := by
      constructor
      · intro hh he
        apply hh
        rw [he]
        exact comap_map_eq_self_of_injective E.subtype_injective _
      · intro hh he
        apply hh
        rw [← map_subgroupOf_eq_of_le hDE, he]
    rw [hn, subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hDE] at hm
    simpa only [fourSpaceThreeFactorsIn, Set.mem_ofPred_eq, hDE, hD, true_and] using hm
  have hnormal : ZG.Normal := by
    constructor
    intro z hz g
    have hm : ZG.map (MulAut.conj g).toMonoidHom = ZG := by
      have hle : ZG.map (MulAut.conj g).toMonoidHom ≤ E :=
        (map_mono hZGle).trans_eq (Normal.map_conj_eq E g)
      have hc : Nat.card (ZG.map (MulAut.conj g).toMonoidHom) = 3 := by
        rw [card_map_of_injective (MulAut.conj g).injective]
        exact hZGcard
      have hs : Module.finrank (ZMod 2)
          (subspaceCommutator ρ ⊤ (ZG.map (MulAut.conj g).toMonoidHom)) = 6 := by
        rw [← moved_map_conjugate]
        exact (LinearEquiv.finrank_map_eq
          (LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)) _).trans hZGsupport
      by_contra hn
      have hfam := (hchar _ hle hc).mp hn
      have hh := hfam.2.2
      omega
    have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom hz
    rwa [hm] at hh
  refine ⟨hdim, ?_, ?_, ZG, hZGle, hnormal, hZGcard, hZGsupport, hZGfix, hchar⟩
  · intro D hD
    have hc : Nat.card (D.subgroupOf E) = 3 :=
      (Nat.card_congr (subgroupOfEquivOfLe hD.1).toEquiv).trans hD.2.1
    have hh := hplanes (D.subgroupOf E) hc (by
      rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hD.1]
      exact hD.2.2)
    rwa [fixedSpace_comp_map, map_subgroupOf_eq_of_le hD.1] at hh
  · apply top_unique
    rw [← full_line_fixed_span ρ E hE hfix]
    apply iSup_le
    intro K
    by_cases he : K.val = Z
    · rw [he, ← fixedSpace_comp_map, hZfix]
      exact bot_le
    · have hm : K.val.map E.subtype ∈ fourSpaceThreeFactorsIn ρ E :=
        (hchar _ (map_subtype_le _) ((card_map_of_injective E.subtype_injective).trans K.property)).mp
          (fun hn => he (map_injective E.subtype_injective hn))
      exact le_iSup_of_le ⟨_,hm⟩ le_rfl

end CFSG.Quasithin.ChapterD.CyclicSource
