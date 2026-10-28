module
public import Theory.Representation.AlternatingSixPairedCovers.Movement
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
/-!
# Odd-order movement on the two covering supports

The reverse cubic comparison shows that the quotient by the second cover,
as well as the quotient by the first, is nontrivial. Every component cubic
moves four dimensions on one natural quotient and at least two on the other
actual section. An element of order five moves a positive multiple of four
on each of two faithful sections. Thus their ambient movements are at least
six and eight, even when the covering centers intersect.

Source: Aschbacher–Smith, original 14.6.24(2), printed p.1041. These bounds
are used in InvolutionMovement to exclude rank-one quadratic members.
-/

public section
open Representation Representation.BinaryOffender Subgroup BinaryPermutation
namespace AlternatingSixPairedCovers
private theorem codim_conj {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) D V)
    {a b : D} (h : IsConj a b) : fixedCodim σ (zpowers a) = fixedCodim σ (zpowers b) := by
  obtain ⟨c,rfl⟩ := isConj_iff.mp h
  rw [fixedCodim_zpowers_conj]

private theorem core_diagram_double : fixedCodim (coreRepresentation (Fin 6))
    (zpowers (BinaryAlternatingSix.diagramAut GLS3.Chapter5.doubleThreeCyclePerm)) = 2 := by
  have he : BinaryAlternatingSix.diagramAut GLS3.Chapter5.doubleThreeCyclePerm =
      BinaryAlternatingSix.align * GLS3.Chapter5.outerDoubleImagePerm * BinaryAlternatingSix.align⁻¹ := by
    change BinaryAlternatingSix.align * GLS3.Chapter5.outerHom GLS3.Chapter5.doubleThreeCyclePerm *
      BinaryAlternatingSix.align⁻¹ = _
    rw [GLS3.Chapter5.outerHom_doubleThreeCyclePerm_eq_outerDoubleImagePerm]
  rw [he,fixedCodim_zpowers_conj]
  have hc : IsConj GLS3.Chapter5.outerDoubleImagePerm GLS3.Chapter5.threeCyclePerm :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr
      (GLS3.Chapter5.outerDoubleImagePerm_isThreeCycle.trans
        GLS3.Chapter5.baseThreeCycle_isThreeCycle.symm)
  exact (codim_conj _ hc).trans core_threeCycle_fixedCodim

namespace Data
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] {ρ : Representation (ZMod 2) H E} (C : Data ρ)

/-- Reversing the cubic comparison proves that the second cover also has a
nontrivial ambient quotient. -/
theorem second_nontrivial_sections :
    (∃ g, C.second.toRepresentation g ≠ 1) ∧
      (∃ g, C.second.quotientRepresentation g ≠ 1) := by
  have hi := C.second_model.injective (BinaryAlternatingSix.diagramAut.injective.comp
    (alternatingGroup (Fin 6)).subtype_injective)
  have hn : GLS3.Chapter5.baseThreeCycle ≠ 1 := by decide +kernel
  let da : alternatingGroup (Fin 6) :=
    ⟨GLS3.Chapter5.doubleThreeCyclePerm,GLS3.Chapter5.doubleThreeCyclePerm_mem_alternating⟩
  refine ⟨⟨_,fun h => hn (hi (h.trans (map_one _).symm))⟩,
    ⟨da,?_⟩⟩
  intro hz
  have he := fixedCodim_cubic_eq_subrepresentation (ρ.comp C.component) C.second
    da (by
      apply Subtype.ext
      have ho : orderOf GLS3.Chapter5.doubleThreeCyclePerm = 3 := by
        rw [← Equiv.Perm.lcm_cycleType,GLS3.Chapter5.doubleThreeCyclePerm_cycleType]
        decide
      exact ho ▸ pow_orderOf_eq_one GLS3.Chapter5.doubleThreeCyclePerm) hz
  have hl := (C.first_model.fixedCodim_bounds (zpowers da)).1
  have hu := (C.second_model.fixedCodim_bounds (zpowers da)).2
  rw [MonoidHom.map_zpowers] at hl hu
  change fixedCodim (naturalRepresentation (Fin 6)) (zpowers GLS3.Chapter5.doubleThreeCyclePerm) ≤ _ at hl
  change _ ≤ fixedCodim (coreRepresentation (Fin 6))
    (zpowers (BinaryAlternatingSix.diagramAut GLS3.Chapter5.doubleThreeCyclePerm)) at hu
  rw [natural_doubleThree_fixedCodim] at hl
  rw [core_diagram_double] at hu
  have hh := fixedCodim_subrepresentation_le (ρ.comp C.component) C.first
    (zpowers da)
  omega

private theorem injective_section {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) W)
    (hs : ∃ g, σ g ≠ 1) : Function.Injective σ := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (MonoidHom.normal_ker σ).eq_bot_or_eq_top with hk | hk
  · exact σ.ker_eq_bot_iff.mp hk
  · obtain ⟨g,hg⟩ := hs
    exact (hg (show g ∈ σ.ker from hk ▸ mem_top g)).elim

private theorem two_le_section {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) W)
    (hs : ∃ g, σ g ≠ 1) (a : alternatingGroup (Fin 6)) (ha : a ≠ 1) :
    2 ≤ fixedCodim σ (zpowers a) := by
  by_contra hn
  exact ha (Representation.SixLetterTransvections.alternating_eq_one_of_displacement_le_one
    σ (injective_section σ hs) a (by rw [←fixedCodim_zpowers_eq_displacement_rank]; omega))

/-- Cubic component elements move at least six ambient dimensions. -/
theorem component_cubic_movement (a : alternatingGroup (Fin 6)) (ha : orderOf a = 3) :
    6 ≤ fixedCodim ρ (zpowers (C.component a)) := by
  have hn : a ≠ 1 := by intro h; simp [h] at ha
  have hh : 6 ≤ fixedCodim (ρ.comp C.component) (zpowers a) := by
    rcases GLS3.Chapter5.alternatingSix_cycleType_of_order_three a ha with hs | hd
    · have hc : IsConj GLS3.Chapter5.threeCyclePerm a.val :=
        Equiv.Perm.isConj_iff_cycleType_eq.mpr
          (GLS3.Chapter5.baseThreeCycle_isThreeCycle.trans hs.symm)
      have hm := (C.second_model.fixedCodim_bounds (zpowers a)).1
      rw [MonoidHom.map_zpowers] at hm
      have hc' := BinaryAlternatingSix.diagramAut.toMonoidHom.map_isConj hc
      have he := codim_conj (naturalRepresentation (Fin 6)) hc'
      change fixedCodim (naturalRepresentation (Fin 6))
        (zpowers (BinaryAlternatingSix.diagramAut GLS3.Chapter5.threeCyclePerm)) = _ at he
      rw [natural_diagram_threeCycle_fixedCodim] at he
      change fixedCodim (naturalRepresentation (Fin 6))
        (zpowers (BinaryAlternatingSix.diagramAut a.val)) ≤ _ at hm
      change 4 = fixedCodim (naturalRepresentation (Fin 6))
        (zpowers (BinaryAlternatingSix.diagramAut a.val)) at he
      rw [←he] at hm
      have hq := two_le_section C.second.quotientRepresentation C.second_nontrivial_sections.2 a hn
      have ht := fixedCodim_quotient_add_subrepresentation_le (ρ.comp C.component) C.second (zpowers a)
      omega
    · have hc : IsConj GLS3.Chapter5.doubleThreeCyclePerm a.val :=
        Equiv.Perm.isConj_iff_cycleType_eq.mpr
          (GLS3.Chapter5.doubleThreeCyclePerm_cycleType.trans hd.symm)
      have hm := (C.first_model.fixedCodim_bounds (zpowers a)).1
      rw [MonoidHom.map_zpowers] at hm
      have he := codim_conj (naturalRepresentation (Fin 6)) hc
      rw [natural_doubleThree_fixedCodim] at he
      change fixedCodim (naturalRepresentation (Fin 6)) (zpowers a.val) ≤ _ at hm
      rw [←he] at hm
      have hq := two_le_section C.first.quotientRepresentation C.nontrivial_sections.2 a hn
      have ht := fixedCodim_quotient_add_subrepresentation_le (ρ.comp C.component) C.first (zpowers a)
      omega
  change 6 ≤ Module.finrank (ZMod 2) (E ⧸ fixedSpace (ρ.comp C.component) (zpowers a)) at hh
  rw [fixedSpace_comp_map,MonoidHom.map_zpowers] at hh
  exact hh

/-- Order-five component elements move at least eight ambient dimensions. -/
theorem component_quintic_movement (a : alternatingGroup (Fin 6)) (ha : orderOf a = 5) :
    8 ≤ fixedCodim ρ (zpowers (C.component a)) := by
  have hn : a ≠ 1 := by intro h; simp [h] at ha
  have hu := two_le_section C.first.toRepresentation C.nontrivial_sections.1 a hn
  have hq := two_le_section C.first.quotientRepresentation C.nontrivial_sections.2 a hn
  have hdu := four_dvd_fixedCodim_of_order_five C.first.toRepresentation a ha
  have hdq := four_dvd_fixedCodim_of_order_five C.first.quotientRepresentation a ha
  have hu4 := Nat.le_of_dvd (by omega : 0 < fixedCodim C.first.toRepresentation (zpowers a)) hdu
  have hq4 := Nat.le_of_dvd (by omega : 0 < fixedCodim C.first.quotientRepresentation (zpowers a)) hdq
  have ht := fixedCodim_quotient_add_subrepresentation_le (ρ.comp C.component) C.first (zpowers a)
  have hh : 8 ≤ fixedCodim (ρ.comp C.component) (zpowers a) := by omega
  change 8 ≤ Module.finrank (ZMod 2) (E ⧸ fixedSpace (ρ.comp C.component) (zpowers a)) at hh
  rw [fixedSpace_comp_map,MonoidHom.map_zpowers] at hh
  exact hh
end Data
end AlternatingSixPairedCovers
