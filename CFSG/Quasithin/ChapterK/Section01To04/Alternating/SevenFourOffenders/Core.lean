module
public import Theory.Representation.AlternatingSevenConjugatePair.Model.InnerElements
public import Theory.Representation.AlternatingSevenConjugatePair.FixedFamily.Linear
public import Theory.Representation.AlternatingSevenConjugatePair.FixedFamily.Coordinates
public import Theory.Representation.BinaryOffender.GeneratedCore
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs

/-!
# The fixed-space and ratio calculation in K.1.2

The two four-groups are the literal even parts of the standard elementary
subgroups of S₇. In a faithful binary four-space every involution moves a
plane. A commuting cubic actor supplies a fixed plane for the regular
four-group R₁. Equality with each involution's fixed space then makes R₁
quadratic. The other four-group R₂ cannot fix a plane: that would make two
explicit noncommuting involutions commute in the faithful action. Its fixed
space is therefore a line.

Elementary subgroups have rank at most two and fixed codimension at least
two. Thus there are no strong offenders, R₁ is a best offender, and the
quadratic infimum is exactly one. `Geometry` supplies exhaustive Sylow
coverage; the parent module applies these calculations to the actual
A₇ ↪ A₈ ≃ SL₄(2) model through the supplied action equivalence.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
K.1.2, printed p.452/PDF p.463.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Alternating.SevenFourOffenders
open Representation.AlternatingSevenConjugatePair
open ElementaryGeometry FixedFamily
abbrev A7 := alternatingGroup (Fin 7)
abbrev R1 : Subgroup A7 := regularFour.subgroupOf A7
abbrev R2 : Subgroup A7 := pairFour.subgroupOf A7

private theorem elementary_subgroupOf {A : Subgroup S7} (hA : IsElementaryTwo A)
    (hle : A ≤ alternatingGroup (Fin 7)) : IsElementaryTwo (A.subgroupOf A7) := by
  let _ := hA.2
  refine ⟨?_, IsElementaryAbelian.subgroupOf hle⟩
  intro h
  apply hA.1
  rw [← Subgroup.map_subgroupOf_eq_of_le hle, h, Subgroup.map_bot]

theorem R1_elementary : IsElementaryTwo R1 := elementary_subgroupOf regularFour_elementary inf_le_right
theorem R2_elementary : IsElementaryTwo R2 := elementary_subgroupOf pairFour_elementary inf_le_right
theorem R1_rank : rank R1 = 2 := (rank_subgroupOf inf_le_right).trans regularFour_rank
theorem R2_rank : rank R2 = 2 := (rank_subgroupOf inf_le_right).trans pairFour_rank

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) A7 V) (hρ : Function.Injective ρ)
  (hdim : Module.finrank (ZMod 2) V = 4)

theorem elementary_rank_le_two {A : Subgroup A7} (hA : IsElementaryTwo A) : rank A ≤ 2 := by
  let _ := hA.2
  have he : IsElementaryTwo (A.map A7.subtype) := ⟨by
    intro h
    exact hA.1 ((A.map_eq_bot_iff_of_injective A7.subtype_injective).mp h),
    IsElementaryAbelian.map _⟩
  simpa only [rank_map_injective A7.subtype A7.subtype_injective] using
    rank_le_two_of_le_alternating _ he (Subgroup.map_subtype_le A)

include hρ hdim

theorem elementary_codim_ge_two {A : Subgroup A7} (hA : IsElementaryTwo A) :
    2 ≤ fixedCodim ρ A := by
  let _ := hA.2
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1
  have ha := a.property
  have ha1' : (a : A7) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have ha2 : orderOf (a : A7) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (a : A7) ha) ha1'
  rw [← Model.involution_fixedCodim ρ hρ hdim a ha2]
  have hl := Submodule.finrank_mono (fixedSpace_antitone ρ (Subgroup.zpowers_le.mpr ha))
  have h1 := fixedCodim_add_finrank ρ (Subgroup.zpowers (a : A7))
  have h2 := fixedCodim_add_finrank ρ A
  omega

theorem not_strong : ¬ IsStrongFFModule ρ := by
  rintro ⟨A, hA, hlt⟩
  have := elementary_rank_le_two hA
  have := elementary_codim_ge_two ρ hρ hdim hA
  omega

theorem offender_rank_codim {A : Subgroup A7} (hA : IsOffender ρ A) :
    rank A = 2 ∧ fixedCodim ρ A = 2 := by
  have := elementary_rank_le_two hA.1
  have := elementary_codim_ge_two ρ hρ hdim hA.1
  have := hA.2
  exact ⟨by omega, by omega⟩

theorem R1_fixed_dimension : Module.finrank (ZMod 2) (fixedSpace ρ R1) = 2 := by
  let _ := R1_elementary.2
  let c : A7 := ⟨cubic, cubic_even⟩
  have hlo := cubic_centralizer_fixed_dimension ρ hρ R1
    (IsElementaryAbelian.isPGroup 2 R1) c (Subtype.ext cubic_cube)
    (fun h => cubic_ne_one (congrArg Subtype.val h))
    (fun a ha => Subtype.ext (regularFour_commutes_cubic a ha))
  have hc := elementary_codim_ge_two ρ hρ hdim R1_elementary
  have hd := fixedCodim_add_finrank ρ R1
  omega

theorem R1_codim : fixedCodim ρ R1 = 2 := by
  have := fixedCodim_add_finrank ρ R1
  rw [R1_fixed_dimension ρ hρ hdim, hdim] at this
  omega

theorem R1_best : IsBestOffender ρ R1 :=
  (isBestOffender_iff_of_not_strong ρ (not_strong ρ hρ hdim) R1).mpr
    ⟨R1_elementary, (R1_codim ρ hρ hdim).trans R1_rank.symm⟩

theorem fixedSpace_eq_involution {A : Subgroup A7} (hA : fixedCodim ρ A = 2)
    (t : A7) (htA : t ∈ A) (ht : orderOf t = 2) :
    fixedSpace ρ A = fixedSpace ρ (Subgroup.zpowers t) := by
  apply Submodule.eq_of_le_of_finrank_eq
    (fixedSpace_antitone ρ (Subgroup.zpowers_le.mpr htA))
  have h1 := fixedCodim_add_finrank ρ A
  have h2 := fixedCodim_add_finrank ρ (Subgroup.zpowers t)
  rw [hA] at h1
  rw [Model.involution_fixedCodim ρ hρ hdim t ht] at h2
  omega

theorem R1_quadratic : IsQuadratic ρ R1 := by
  intro a ha b hb v
  by_cases hb1 : b = 1
  · simp [hb1]
  let _ := R1_elementary.2
  have hb2 : b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian b hb
  have hf := fixedSpace_eq_involution ρ hρ hdim (R1_codim ρ hρ hdim)
    b hb (orderOf_eq_prime hb2 hb1)
  have hv := involution_range_le_fixed ρ b hb2 (show ρ b v - v ∈
      LinearMap.range (ρ b - LinearMap.id) from ⟨v, rfl⟩)
  rw [← hf] at hv
  exact hv ⟨a, ha⟩

omit hρ hdim in
private def z : A7 := ⟨centralInvolution, centralInvolution_mem.1.2⟩
omit hρ hdim in
private def s : A7 := ⟨pairInvolution, pairInvolution_mem.2⟩
omit hρ hdim in
private def t : A7 := ⟨crossSwap, crossSwap_mem_regularFour.2⟩
omit hρ hdim in
private theorem z_order : orderOf z = 2 :=
  (orderOf_injective A7.subtype A7.subtype_injective z).symm.trans centralInvolution_order
omit hρ hdim in
private theorem s_order : orderOf s = 2 :=
  (orderOf_injective A7.subtype A7.subtype_injective s).symm.trans pairInvolution_order
omit hρ hdim in
private theorem t_order : orderOf t = 2 :=
  (orderOf_injective A7.subtype A7.subtype_injective t).symm.trans crossSwap_order

theorem R2_codim_ne_two : fixedCodim ρ R2 ≠ 2 := by
  intro hp
  have hpz := fixedSpace_eq_involution ρ hρ hdim hp z centralInvolution_mem.1 z_order
  have hrz := fixedSpace_eq_involution ρ hρ hdim (R1_codim ρ hρ hdim)
    z centralInvolution_mem.2 z_order
  have hps := fixedSpace_eq_involution ρ hρ hdim hp s pairInvolution_mem s_order
  have hrt := fixedSpace_eq_involution ρ hρ hdim (R1_codim ρ hρ hdim)
    t crossSwap_mem_regularFour t_order
  have hc := commute_of_same_involution_fixedSpace ρ hρ s t
    (by simpa only [s_order] using pow_orderOf_eq_one s)
    (by simpa only [t_order] using pow_orderOf_eq_one t)
    (hps.symm.trans (hpz.trans (hrz.symm.trans hrt)))
  exact pair_cross_noncommute (congrArg Subtype.val hc)

theorem R2_fixed_dimension : Module.finrank (ZMod 2) (fixedSpace ρ R2) = 1 := by
  let _ := R2_elementary.2
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) V)
  obtain ⟨v, hv0, hv⟩ := BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector
    (ρ.comp R2.subtype) (IsElementaryAbelian.isPGroup 2 R2)
  have hp : 0 < Module.finrank (ZMod 2) (fixedSpace ρ R2) := by
    let _ : Nontrivial (fixedSpace ρ R2) := ⟨⟨⟨v, hv⟩, 0,
      fun h => hv0 (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  have hd := fixedCodim_add_finrank ρ R2
  have hl := elementary_codim_ge_two ρ hρ hdim R2_elementary
  have hn := R2_codim_ne_two ρ hρ hdim
  omega

theorem quadraticRatio_eq_one : quadraticRatio ρ = 1 := by
  apply le_antisymm
  · have he : actionRatio ρ R1 = 1 := (actionRatio_eq_one_iff ρ R1_elementary).mpr
      ((R1_codim ρ hρ hdim).trans R1_rank.symm)
    exact iInf_le_of_le R1 (iInf_le_of_le ⟨R1_elementary, R1_quadratic ρ hρ hdim⟩ he.le)
  · apply le_iInf
    intro A
    apply le_iInf
    rintro ⟨hA, _⟩
    exact le_of_not_gt (fun h => not_strong ρ hρ hdim
      ⟨A, hA, (actionRatio_lt_one_iff ρ hA).mp h⟩)

/-- The source equality `C_V(R₁) = C_V(r) = [V,r]` for every nonidentity `r ∈ R₁`. -/
theorem R1_fixed_eq_range (r : A7) (hr : r ∈ R1) (hr1 : r ≠ 1) :
    fixedSpace ρ R1 = LinearMap.range (ρ r - LinearMap.id) := by
  let _ := R1_elementary.2
  have hr2 : r ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian r hr
  have ho : orderOf r = 2 := orderOf_eq_prime hr2 hr1
  have hf := fixedSpace_eq_involution ρ hρ hdim (R1_codim ρ hρ hdim) r hr ho
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [hf]
    exact involution_range_le_fixed ρ r hr2
  · rw [← fixedCodim_zpowers_eq_displacement_rank,
      Model.involution_fixedCodim ρ hρ hdim r ho, R1_fixed_dimension ρ hρ hdim]

/-- The other Sylow four-group moves three dimensions, so is not an offender. -/
theorem R2_codim : fixedCodim ρ R2 = 3 := by
  have hd := fixedCodim_add_finrank ρ R2
  rw [R2_fixed_dimension ρ hρ hdim, hdim] at hd
  omega

theorem R2_not_offender : ¬ IsOffender ρ R2 := by
  intro h
  have := h.2
  rw [R2_codim ρ hρ hdim, R2_rank] at this
  omega

end CFSG.Quasithin.ChapterK.Alternating.SevenFourOffenders
