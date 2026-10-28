module

public import CFSG.Quasithin.ChapterH.Section13To16.Stabilizers.CommonFour
public import CFSG.Quasithin.ChapterH.Section13To16.Stabilizers.FixedSpan
public import CFSG.Quasithin.ChapterH.Section13To16.Stabilizers.ElementaryFusion
public import CFSG.Quasithin.ChapterH.Section13To16.Stabilizers.TrioAction
public import CFSG.Quasithin.ChapterH.Section13To16.Stabilizers.OctadAction
public import CFSG.Quasithin.ChapterH.Section13To16.Stabilizers.M23Actions
public import CFSG.Quasithin.ChapterH.Section13To16.Stabilizers.M22Classification
public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Fusion
public import Theory.Mathieu.M24.ChapterHStabilizers.SextetAction
public import Theory.Mathieu.M24.ChapterHStabilizers.CommonPlane
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Affine

/-!
# Native H.14 stabilizer classifications

The compatible M23 Sylow group has exactly the intrinsic quintet and heptad
E16 cores, and every native E16 is conjugate to one of them. For M24 the
sextet quotient is the genuine nonsplit threefold extension of S6, and its
conjugation module is the additive hexacode, with the residual preserving
the actual F4 scalar structure. The trio intrinsic quotient retains both
the projective linear and symmetric factors, acting on its core by their
natural tensor product. The octad quotient is the actual PSL4(2), acting
naturally on its intrinsic core. The imported M24 elementary classification
uses these intrinsic cores in a common octad/sextet/trio Sylow marking.
The marked common four is an actual F4 line, with precisely fifteen
conjugates under the native sextet stabilizer.

The M23 local actions and the M22 inner/outer classifications are re-exported
with their actual quotient identifications, conjugation coordinates and
compatible native inclusions. No core-order or module-identification premise
remains in the assembled classification. In particular the former trio-order
input below is discharged by the proved intrinsic tensor-core calculation.
The common-four geometry also discharges the subgroup and fusion inputs of
the H.16.8 fixed-space-span reduction; its independent module dimensions
remain explicit in `m23Code_fixedSpan_bound_of_common_pair_model`.

Source: Aschbacher–Smith H.14.1–3, printed pp.396–397. The native involution
classes and fixed sets of H.14.4 are re-exported through `CommonFour`;
H.14.4's code/cocode fixed-space codimensions belong to the module calculations.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterH.Section13To16
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M23Geometry MathieuCode
open M24ChapterHStabilizers

/-- Both E64 cores, their common Sylow placement and their distinctness,
with the trio-order premise of the earlier interface discharged. -/
theorem standardM24_large_kernel_structure :
    (IsElementaryAbelian 2 (sextetKernel standardSextet) ∧
      Nat.card (sextetKernel standardSextet) = 64 ∧
      sextetKernel standardSextet ≤ ElementaryFusion.standardSylow.toSubgroup) ∧
    (IsElementaryAbelian 2 (trioKernel PairOvergroups.standardTrio) ∧
      Nat.card (trioKernel PairOvergroups.standardTrio) = 64 ∧
      trioKernel PairOvergroups.standardTrio ≤ ElementaryFusion.standardSylow.toSubgroup) ∧
    sextetKernel standardSextet ≠ trioKernel PairOvergroups.standardTrio :=
  standardM24_two_large_kernels (trioKernel_card PairOvergroups.standardTrio)

/-- H.14.1(5) in the source's rank convention for nontrivial elementary actors. -/
theorem lemma_H_14_1_5 (A : Subgroup M24)
    (hA : Representation.BinaryOffender.IsElementaryTwo A)
    (hrank : 5 ≤ Representation.BinaryOffender.rank A) :
    ∃ g : M24,
      A.map (MulAut.conj g).toMonoidHom ≤ sextetKernel standardSextet ∨
      A.map (MulAut.conj g).toMonoidHom ≤ trioKernel PairOvergroups.standardTrio := by
  apply m24_large_elementary_fusion A hA.2
  rw [hA.card_eq_two_pow_rank]
  exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank

/-- The H.13 order bound follows from the actual H.14.1 fusion classification. -/
theorem m24_elementary_card_le_sixty_four (A : Subgroup M24)
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 64 := by
  by_cases hc : 32 ≤ Nat.card A
  · obtain ⟨g, hg | hg⟩ := m24_large_elementary_fusion A hA hc
    · have h := Subgroup.card_le_of_le hg
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        standardM24_large_kernel_structure.1.2.1] at h
      exact h
    · have h := Subgroup.card_le_of_le hg
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        trioKernel_card] at h
      exact h
  · omega

/-- H.14.2(1), including existence as well as uniqueness in the marked Sylow group. -/
theorem standardM23_card16_iff_kernel (A : Subgroup M23) :
    (IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧ A ≤ CommonFour.standardSylow.toSubgroup) ↔
      A = m23QuintetKernel standardSextet ∨ A = m23OctadKernel standardOctad := by
  have h := CommonFour.sylow_card16_iff A
  rw [CommonFour.heptad_core_eq, ← CommonFour.octad_core_comap] at h
  exact h

/-- The two E16 subgroups in the compatible Sylow group really are distinct. -/
theorem standardM23_kernels_distinct :
    m23QuintetKernel standardSextet ≠ m23OctadKernel standardOctad := by
  have h := CommonFour.cores_distinct
  rw [CommonFour.heptad_core_eq, ← CommonFour.octad_core_comap] at h
  exact h

/-- Every native E16 is a conjugate of an intrinsic source kernel. -/
theorem m23_card16_fusion (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) :
    ∃ g : M23,
      A = (m23QuintetKernel standardSextet).map (MulAut.conj g).toMonoidHom ∨
      A = (m23OctadKernel standardOctad).map (MulAut.conj g).toMonoidHom := by
  have h := CommonFour.card16_conjugate_core A hA hc
  rw [CommonFour.heptad_core_eq, ← CommonFour.octad_core_comap] at h
  exact h

/-- H.14.1(2): the intrinsic quotient is the concrete hexacode automorphism group. -/
noncomputable def standardSextet_quotient_equiv :
    (sextetStabilizer standardSextet ⧸ pCore 2 (sextetStabilizer standardSextet)) ≃*
      Atlas.Codes.HexAutomorphisms := SextetCore.coreQuotientEquiv

/-- Its map to S6 is a nonsplit extension with kernel of order three. -/
theorem standardSextet_quotient_cover :
    Function.Surjective SextetAction.quotientColumns ∧
      Nat.card SextetAction.quotientColumns.ker = 3 ∧
      ¬ ∃ s : Equiv.Perm (Fin 6) →* SextetAction.Quotient,
        SextetAction.quotientColumns.comp s = MonoidHom.id _ :=
  ⟨SextetAction.quotientColumns_surjective, SextetAction.quotientColumns_kernel_card,
    SextetAction.quotientColumns_nonsplit⟩

/-- The additive hexacode is identified with the literal ambient sextet kernel. -/
noncomputable def standardSextet_kernel_equiv :
    Multiplicative Atlas.Codes.hexacode ≃* sextetKernel standardSextet :=
  SextetAction.ambientTranslationEquiv

/-- The native conjugation action is the natural hexacode action of the quotient. -/
theorem standardSextet_kernel_action (g : sextetStabilizer standardSextet)
    (v : Atlas.Codes.hexacode) :
    g.val * (standardSextet_kernel_equiv (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (standardSextet_kernel_equiv (Multiplicative.ofAdd
        (Representation.Hexacode.action (SextetCore.quotientHom g) v))).val :=
  SextetAction.ambientTranslationEquiv_conjugation g v

/-- The terminal derived group preserves the three-dimensional F4 structure. -/
theorem standardSextet_residual_field_structure :
    Fintype.card Representation.Hexacode.F = 4 ∧
      Module.finrank Representation.Hexacode.F Atlas.Codes.hexacode = 3 ∧
      ∀ (g : Subgroup.solvableResidual (sextetStabilizer standardSextet))
        (r : Representation.Hexacode.F) (v : Atlas.Codes.hexacode),
        Representation.Hexacode.action (SextetCore.quotientHom g.val) (r • v) =
          r • Representation.Hexacode.action (SextetCore.quotientHom g.val) v :=
  ⟨Representation.Hexacode.field_card, Representation.Hexacode.field_finrank,
    SextetAction.residual_field_linear⟩

/-- H.14.1(6): the literal intersection of the ambient cores is E4. -/
theorem standardM24_common_structure :
    IsElementaryAbelian 2
      (octadKernel standardOctad ⊓ sextetKernel standardSextet : Subgroup M24) ∧
      Nat.card (octadKernel standardOctad ⊓ sextetKernel standardSextet : Subgroup M24) = 4 :=
  ⟨CommonPlane.common_elementary, CommonPlane.common_card⟩

/-- The common four is a field line under the same core coordinates as the natural action. -/
theorem standardM24_common_field_line :
    Module.finrank Representation.Hexacode.F CommonPlane.commonFieldLine = 1 ∧
      ∀ v : Atlas.Codes.hexacode,
        (standardSextet_kernel_equiv (Multiplicative.ofAdd v)).val ∈
          octadKernel standardOctad ⊓ sextetKernel standardSextet ↔
        v ∈ CommonPlane.commonFieldLine :=
  ⟨CommonPlane.commonFieldLine_finrank, CommonPlane.translation_mem_commonFieldLine⟩

/-- Exactly fifteen actual ambient subgroups occur under the source stabilizer's conjugation. -/
theorem standardM24_common_conjugates_card :
    Nat.card {A : Subgroup M24 // ∃ g : sextetStabilizer standardSextet,
      (octadKernel standardOctad ⊓ sextetKernel standardSextet).map
        (MulAut.conj g.val).toMonoidHom = A} = 15 :=
  CommonPlane.conjugates_card

/-- The actual trio quotient by its intrinsic two-core, in source factor order. -/
noncomputable def standardTrio_quotient_equiv :
    (PairOvergroups.trioStabilizer PairOvergroups.standardTrio ⧸
      pCore 2 (PairOvergroups.trioStabilizer PairOvergroups.standardTrio)) ≃*
      (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) × Equiv.Perm (Fin 3)) :=
  TrioCalculation.standardSourceQuotientEquiv

end CFSG.Quasithin.ChapterH.Section13To16
