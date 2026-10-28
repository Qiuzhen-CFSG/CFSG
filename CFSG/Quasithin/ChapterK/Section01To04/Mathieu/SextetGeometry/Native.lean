module

public import Theory.Mathieu.M24.LocalGeometry.SextetCore
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions
public import Theory.Representation.HexacodeAction.Field
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions
public import Theory.Representation.BinaryOffender.Basic

/-!
# The noncentral part of the native sextet kernel

The actual coordinate equivalence of sextet stabilizers identifies the native
two-core with hexacode translations. A fixed-point-free translation has no zero
coordinate. Consequently evaluation at any one tetrad is injective on a subgroup
all of whose nonidentity elements are fixed-point-free, giving order at most four.
The existing full-weight hexacode plane is an actual one-dimensional F₄-submodule
and realizes equality. No subgroup classification is assumed.

Source: Aschbacher–Smith, K.4.2, printed p.458, and H.14.1(2), pp.396–397.
The coordinate model and field action use the licensed ATLAS ports, attributed
in `Theory.Mathieu.M24.LocalGeometry.SextetCore.Comparison` and
`Theory.Representation.HexacodeAction.Field`.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterK.Mathieu.SextetGeometry
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open Representation.BinaryOffender Atlas.Codes
open MathieuCode.CocodeOctad.Involutions

/-- The hexacode translations included in the original Witt-design M₂₄. -/
def translation : Multiplicative hexacode →* M24 :=
  (sextetStabilizer standardSextet).subtype.comp
    (SextetCore.sextetEquiv.symm.toMonoidHom.comp sextetTranslation)

theorem translation_injective : Function.Injective translation :=
  (sextetStabilizer standardSextet).subtype_injective.comp
    (SextetCore.sextetEquiv.symm.injective.comp sextetTranslation_injective)

/-- The range is the intrinsic two-core, included by the literal stabilizer map. -/
theorem translation_range : translation.range = SextetCore.core := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨SextetCore.sextetEquiv.symm (sextetTranslation w), ?_, rfl⟩
    rw [← SextetCore.quotientHom_ker]
    change sextetQuotient (SextetCore.sextetEquiv
      (SextetCore.sextetEquiv.symm (sextetTranslation w))) = 1
    rw [SextetCore.sextetEquiv.apply_symm_apply, sextetQuotient_translation]
  · rintro ⟨x, hx, rfl⟩
    rw [← SextetCore.quotientHom_ker] at hx
    have hm : SextetCore.sextetEquiv x ∈ sextetTranslation.range := by
      rw [← sextetQuotient_kernel]
      exact hx
    obtain ⟨w, hw⟩ := hm
    refine ⟨w, ?_⟩
    change (SextetCore.sextetEquiv.symm (sextetTranslation w)).val = x.val
    rw [hw, SextetCore.sextetEquiv.symm_apply_apply]

/-- Translation really acts by addition in each of the six four-point tetrads. -/
theorem translation_coordinates (w : Multiplicative hexacode) (i : HexIndex) (k : Fin 4) :
    (translation w).val (atlasPointEquiv (i,k)) =
      atlasPointEquiv (i, rowLabel.symm (rowLabel k + w.toAdd.val i)) := by
  have h := SextetCore.sextetEquiv_apply
    (SextetCore.sextetEquiv.symm (sextetTranslation w))
  rw [SextetCore.sextetEquiv.apply_symm_apply] at h
  have he := congrArg (fun p : Equiv.Perm Omega => atlasPointEquiv (p (i,k))) h
  simpa only [translation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply,
    sextetTranslation_coordinates, Equiv.permCongr_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply] using he.symm

/-- The natural action of the genuine sextet quotient is the hexacode action. -/
theorem translation_conjugation (g : HexAutomorphisms) (w : Multiplicative hexacode) :
    (SextetCore.sextetEquiv.symm (sextetSection g)).val * translation w *
      (SextetCore.sextetEquiv.symm (sextetSection g)).val⁻¹ =
        translation (hexAffineAction g w) := by
  have h := congrArg (fun s : Atlas.Codes.SextetStabilizer =>
    (SextetCore.sextetEquiv.symm s).val) (sextet_translation_conjugation g w)
  simpa only [translation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply,
    map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem noncentral_fixedPointFree {x : M24} (hx : IsConj t x) (i : Fin 24) :
    x • i ≠ i := by
  intro hi
  have hm := (M24ChapterHStabilizers.mem_fixedPoints x i).mpr hi
  rw [M24ChapterHStabilizers.class2B_fixed_empty hx] at hm
  exact Finset.notMem_empty _ hm

/-- On this native kernel, the noncentral class has full hexacode support. -/
theorem noncentral_translation_coordinates {w : Multiplicative hexacode}
    (hw : IsConj t (translation w)) (i : HexIndex) : w.toAdd.val i ≠ 0 := by
  intro hi
  apply noncentral_fixedPointFree hw (atlasPointEquiv (i,0))
  change (translation w).val (atlasPointEquiv (i,0)) = _
  rw [translation_coordinates, hi, add_zero, rowLabel.symm_apply_apply]

private def evaluation (i : HexIndex) : Multiplicative hexacode →* Multiplicative K where
  toFun w := Multiplicative.ofAdd (w.toAdd.val i)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Evaluation at a tetrad embeds every full-support subgroup in its additive F₄. -/
theorem fullSupport_card_le_four (A : Subgroup (Multiplicative hexacode))
    (hA : ∀ w ∈ A, w ≠ 1 → ∀ i : HexIndex, w.toAdd.val i ≠ 0) : Nat.card A ≤ 4 := by
  let f := (evaluation (0,0)).comp A.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro w hw
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    by_contra hn
    exact hA w w.property hn (0,0) hw
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    Fintype.card_prod, ZMod.card] using hc

/-- The concrete noncentral-subgroup bound inside the actual sextet two-core. -/
theorem core_noncentral_card_le_four (D : Subgroup M24) (hD : D ≤ SextetCore.core)
    (hclass : ∀ x ∈ D, x ≠ 1 → IsConj t x) : Nat.card D ≤ 4 := by
  let A := D.comap translation
  have hm : A.map translation = D := by
    apply Subgroup.map_comap_eq_self
    rwa [translation_range]
  have hc : Nat.card A ≤ 4 := fullSupport_card_le_four A (by
    intro w hw hn
    apply noncentral_translation_coordinates (hclass _ hw _)
    intro he
    exact hn (translation_injective (he.trans (map_one translation).symm)))
  rw [← hm, Subgroup.card_map_of_injective translation_injective]
  exact hc

theorem core_noncentral_rank_le_two (D : Subgroup M24) (hD : D ≤ SextetCore.core)
    (hclass : ∀ x ∈ D, x ≠ 1 → IsConj t x) : rank D ≤ 2 := by
  have h := Nat.log_mono_right (b := 2) (core_noncentral_card_le_four D hD hclass)
  exact h

/-- The source line is a submodule over the actual four-element field. -/
def fullWeightFieldLine : Submodule Representation.Hexacode.F hexacode :=
  Representation.Hexacode.scalarSubmodule Representation.Hexacode.fullWeightPlane
    Representation.Hexacode.fullWeightPlane_scalar_stable

theorem fullWeightFieldLine_finrank :
    Module.finrank Representation.Hexacode.F fullWeightFieldLine = 1 := by
  have h := Representation.Hexacode.scalarSubmodule_finrank
    Representation.Hexacode.fullWeightPlane
    Representation.Hexacode.fullWeightPlane_scalar_stable
  rw [Representation.Hexacode.fullWeightPlane_finrank] at h
  change 2 * Module.finrank Representation.Hexacode.F fullWeightFieldLine = 2 at h
  omega

theorem translation_fixedPointFree (w : Multiplicative hexacode)
    (hw : ∀ i : HexIndex, w.toAdd.val i ≠ 0) (p : Fin 24) :
    translation w • p ≠ p := by
  obtain ⟨⟨i,k⟩, rfl⟩ := atlasPointEquiv.surjective p
  intro he
  change (translation w).val (atlasPointEquiv (i,k)) = _ at he
  rw [translation_coordinates] at he
  have hr := congrArg (fun p : Omega => rowLabel p.2) (atlasPointEquiv.injective he)
  simp only [rowLabel.apply_symm_apply] at hr
  exact hw i (add_left_cancel (hr.trans (add_zero _).symm))

/-- Full support detects the actual noncentral conjugacy class in the native group. -/
theorem translation_isConj_t (w : Multiplicative hexacode)
    (hw : ∀ i : HexIndex, w.toAdd.val i ≠ 0) : IsConj t (translation w) := by
  let := SextetCore.core_ambient_elementary
  have hmem : translation w ∈ SextetCore.core := translation_range ▸ ⟨w, rfl⟩
  have hn : translation w ≠ 1 := by
    intro he
    have hf := translation_fixedPointFree w hw 0
    rw [he, one_smul] at hf
    exact hf rfl
  have ho : orderOf (translation w) = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ hmem) hn
  rcases M24InvolutionCentralizers.involution_classes _ ho with hz | ht
  · have hc := m24Blocks_card _ (M24ChapterHStabilizers.class2A_fixed_octad hz)
    have hempty : M24ChapterHStabilizers.fixedPoints (translation w) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact translation_fixedPointFree w hw p
        ((M24ChapterHStabilizers.mem_fixedPoints _ _).mp hp)
    rw [hempty, Finset.card_empty] at hc
    omega
  · exact ht

/-- A fixed-point-free representative lying in the standard sextet kernel. -/
def representative : M24 := translation (Multiplicative.ofAdd Representation.Hexacode.fullWeightWord)

theorem representative_mem : representative ∈ SextetCore.core :=
  translation_range ▸ ⟨_, rfl⟩

theorem representative_isConj : IsConj t representative := by
  apply translation_isConj_t
  change ∀ i : HexIndex, Representation.Hexacode.fullWeightWord.val i ≠ 0
  decide +kernel

/-- Every noncentral involution can be placed in the actual standard sextet kernel. -/
theorem noncentral_sextet_placement {x : M24} (hx : IsConj t x) :
    ∃ g : M24, (MulAut.conj g) x = representative :=
  isConj_iff.mp (hx.symm.trans representative_isConj)

/-- Include the full-weight field line as actual native translations. -/
def lineHom : Multiplicative Representation.Hexacode.fullWeightPlane →* M24 where
  toFun w := translation (Multiplicative.ofAdd w.toAdd.val)
  map_one' := map_one translation
  map_mul' _ _ := map_mul translation _ _

theorem lineHom_injective : Function.Injective lineHom := by
  intro w v h
  have he := translation_injective h
  exact Subtype.ext he

/-- The bound four is attained by the genuine F₄-line in the native kernel. -/
theorem fullWeightLine_native :
    lineHom.range ≤ SextetCore.core ∧ Nat.card lineHom.range = 4 ∧
      ∀ x ∈ lineHom.range, x ≠ 1 → IsConj t x := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    exact translation_range ▸ ⟨_, rfl⟩
  · calc
      Nat.card lineHom.range = Nat.card (Multiplicative Representation.Hexacode.fullWeightPlane) :=
        (Nat.card_congr (Equiv.ofInjective lineHom lineHom_injective)).symm
      _ = 4 := by
        rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative Representation.Hexacode.fullWeightPlane ≃ _)]
        let := Fintype.ofFinite Representation.Hexacode.fullWeightPlane
        rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := Bit),
          Representation.Hexacode.fullWeightPlane_finrank, ZMod.card]
        norm_num
  · rintro _ ⟨w, rfl⟩ hn
    apply translation_isConj_t
    have hw : w.toAdd.val ≠ 0 := by
      intro he
      apply hn
      change translation (Multiplicative.ofAdd w.toAdd.val) = 1
      rw [he]
      exact map_one translation
    obtain ⟨r, hr⟩ := w.toAdd.property
    have hrn : r ≠ 0 := by
      intro he
      apply hw
      rw [← hr, he, map_zero]
    rw [← hr]
    have hf : ∀ r : Atlas.Codes.Bit × Atlas.Codes.Bit, r ≠ 0 →
        ∀ i : HexIndex, (Representation.Hexacode.fullWeightPlaneEncoder r).val i ≠ 0 := by
      decide +kernel
    exact hf r hrn

end CFSG.Quasithin.ChapterK.Mathieu.SextetGeometry
