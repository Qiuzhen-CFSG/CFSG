module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.FixedQuotient.Transvections
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.FixedQuotient.Cubic

/-!
# Displacement on the five-space of a commuting cubic actor

Conjugation by an element of order three fixing a nonidentity kernel element
has a nonzero fixed vector in the four-dimensional kernel module. Orbit
counting forces its fixed dimension to be two or four. Duality and odd-order
averaging through the fixed center transfer the displacement bound two to V5.
The lower bound on the ten-dimensional code is a separate scalar input.

Source: Aschbacher--Smith, H.16.4(5), printed p.403, 1 March 2004.
-/

public section
noncomputable section
namespace MathieuCode.Hexad.ChiefFlag.FixedQuotientData
open Representation Representation.BinaryOffender FixedQuotientCubic
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

theorem conjugation_finrank (D : Actions E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    Module.finrank (ZMod 2) E = 4 := by
  have hc := center_finrank h h24
  have h5 := codeCommutatorSubrepresentation_finrank h h24
  change Module.finrank (ZMod 2) V5.toSubmodule = 5 at h5
  have hq := center.toSubmodule.finrank_quotient_add_finrank
  have he := D.middleEquiv.finrank_eq
  rw [Subspace.dual_finrank_eq] at he
  omega

/-- The actual conjugation representation, not an unrelated four-space. -/
theorem conjugation_displacement_le_two (D : Actions E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (y : Stabilizer) (hy : orderOf y = 3) (z : Kernel) (hz : z ≠ 1)
    (hyz : Commute y.val z.val) :
    fixedCodim D.conjugation (Subgroup.zpowers y) ≤ 2 := by
  let v : E := Multiplicative.toAdd (D.kernelMarking.symm z)
  have hv : D.kernelMarking (Multiplicative.ofAdd v) = z := D.kernelMarking.apply_symm_apply z
  have hv0 : v ≠ 0 := by
    intro he
    apply hz
    rw [← hv, he]
    exact D.kernelMarking.map_one
  have hfix : D.conjugation y v = v := by
    apply Multiplicative.ofAdd.injective
    apply D.kernelMarking.injective
    apply Subtype.ext
    rw [D.kernelMarking_equivariant, hv]
    rw [hyz.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hvf : v ∈ fixedSpace D.conjugation (Subgroup.zpowers y) :=
    (mem_fixedSpace_zpowers_iff _ _ _).mpr hfix
  have hd := conjugation_finrank D h h24
  have hc : Nat.card (Subgroup.zpowers y) = 3 := (Nat.card_zpowers y).trans hy
  have hm := fixed_card_mod_three (D.conjugation.comp (Subgroup.zpowers y).subtype) hc
  rw [fixedSpace_restrict_top, hd] at hm
  have hn : Module.finrank (ZMod 2) (fixedSpace D.conjugation (Subgroup.zpowers y)) ≠ 0 := by
    intro hn
    have hb := Submodule.finrank_eq_zero.mp hn
    rw [hb] at hvf
    exact hv0 hvf
  have hl := (fixedSpace D.conjugation (Subgroup.zpowers y)).finrank_le
  rw [hd] at hl
  have hh : 2 ≤ Module.finrank (ZMod 2) (fixedSpace D.conjugation (Subgroup.zpowers y)) := by
    by_contra hh
    have he : Module.finrank (ZMod 2) (fixedSpace D.conjugation (Subgroup.zpowers y)) = 1 := by omega
    simp [he] at hm
  have hr := fixedCodim_add_finrank D.conjugation (Subgroup.zpowers y)
  omega

/-- Odd-order averaging through V1 identifies the displacement on V5 with
that on V5/V1; the genuine dual conjugation marking bounds it by two. -/
theorem five_displacement_le_two (D : Actions E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (y : Stabilizer) (hy : orderOf y = 3) (z : Kernel) (hz : z ≠ 1)
    (hyz : Commute y.val z.val) :
    fixedCodim V5.toRepresentation (Subgroup.zpowers y) ≤ 2 := by
  have he := fixedCodim_map_equivariant center.quotientRepresentation D.conjugation.dual
    (MonoidHom.id Stabilizer) D.middleEquiv D.middleEquiv_equivariant (Subgroup.zpowers y)
  rw [Subgroup.map_id, fixedCodim_zpowers_dual] at he
  have hc : Nat.card (Subgroup.zpowers y) = 3 := (Nat.card_zpowers y).trans hy
  have htriv := fixed_eq_top_of_dim_one
    (center.toRepresentation.comp (Subgroup.zpowers y).subtype) hc (center_finrank h h24)
  have htriv' : fixedSpace center.toRepresentation (Subgroup.zpowers y) = ⊤ :=
    (fixedSpace_restrict_top center.toRepresentation (Subgroup.zpowers y)).symm.trans htriv
  have hzero : fixedCodim center.toRepresentation (Subgroup.zpowers y) = 0 :=
    (fixedCodim_eq_zero_iff center.toRepresentation (Subgroup.zpowers y)).mpr htriv'
  have hadd := displacement_add_subgroup V5.toRepresentation center (Subgroup.zpowers y)
    (by rw [hc]; decide)
  have hbound := conjugation_displacement_le_two D h h24 y hy z hz hyz
  omega

end MathieuCode.Hexad.ChiefFlag.FixedQuotientData
