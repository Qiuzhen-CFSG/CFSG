module

public import CFSG.Quasithin.ChapterH.Section13To16.Stabilizers.Sextet
public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Cores

/-!
# The native common four-group and compatible M23 cores

The literal intersection of the marked octad and sextet cores restricts to
an elementary group of order four in native M23. Every native E16 contains
a conjugate of this subgroup. The two E16 subgroups in the compatible Sylow
group are exactly the intrinsic quintet and heptad cores. That Sylow group
is itself the restriction of an M24 Sylow group stabilizing the marked octad
and sextet, preserving the source's choice of geometry.

Source: Aschbacher–Smith H.14.1(6), H.14.2(1), and the common subgroup used
in H.16.8, printed pp.397,405. This module supplies the unconditional native
common-four contract; it does not assert the remaining module-action clauses.
-/

public section
namespace CFSG.Quasithin.ChapterH.Section13To16
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M23Geometry MathieuCode

/-- All fields of the native common-four contract are now proved from the geometry. -/
theorem nativeM23CommonFourData : NativeM23CommonFourData where
  common_card := CommonFour.commonKernel_card
  coverage := CommonFour.card16_contains_commonKernel_conjugate

/-- The order of the literal marked common kernel. -/
theorem m23CommonKernel_card : Nat.card m23CommonKernel = 4 :=
  CommonFour.commonKernel_card

/-- The literal marked subgroup is E4, with no additional structural premise. -/
theorem standardM23_commonKernel_structure :
    IsElementaryAbelian 2 m23CommonKernel ∧ Nat.card m23CommonKernel = 4 :=
  ⟨m23CommonKernel_elementary, CommonFour.commonKernel_card⟩

/-- Unconditional native E16 coverage by conjugates of the marked common subgroup. -/
theorem standardM23_card16_contains_common_conjugate (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) :
    ∃ g : M23, m23CommonKernel.map (MulAut.conj g).toMonoidHom ≤ A :=
  CommonFour.card16_contains_commonKernel_conjugate A hA hc

/-- The marked common subgroup is exactly the intersection of the two source kernels. -/
theorem m23CommonKernel_eq_quintet_inf_octad :
    m23CommonKernel = m23QuintetKernel standardSextet ⊓ m23OctadKernel standardOctad := by
  change CommonFour.commonKernel = _
  rw [CommonFour.compatible_cores.2.2, CommonFour.heptad_core_eq,
    ← CommonFour.octad_core_comap]
  rfl

/-- The common subgroup belongs to the intrinsic quintet core. -/
theorem m23CommonKernel_le_quintet : m23CommonKernel ≤ m23QuintetKernel standardSextet := by
  change CommonFour.commonKernel ≤ _
  rw [CommonFour.compatible_cores.2.2]
  exact inf_le_left

/-- The actual intrinsic quintet core is elementary of order sixteen. -/
theorem standardM23_quintet_kernel_structure :
    IsElementaryAbelian 2 (m23QuintetKernel standardSextet) ∧
      Nat.card (m23QuintetKernel standardSextet) = 16 := by
  change IsElementaryAbelian 2 ((pCore 2 CommonFour.quintetStabilizer).map
    CommonFour.quintetStabilizer.subtype) ∧
    Nat.card ((pCore 2 CommonFour.quintetStabilizer).map CommonFour.quintetStabilizer.subtype) = 16
  rw [CommonFour.quintet_core_eq]
  exact ⟨CommonFour.standardCandidate_elementary 0,CommonFour.standardCandidate_card 0⟩

/-- The two source kernels are the only E16 subgroups of the compatible native Sylow group. -/
theorem standardM23_card16_eq_kernel (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 16)
    (hAS : A ≤ CommonFour.standardSylow.toSubgroup) :
    A = m23QuintetKernel standardSextet ∨ A = m23OctadKernel standardOctad := by
  have h := CommonFour.card16_eq_core A hA hc hAS
  rw [CommonFour.heptad_core_eq, ← CommonFour.octad_core_comap] at h
  exact h

/-- The marking uses a genuine common ambient Sylow group and the actual point embedding. -/
theorem standardM23_ambient_sylow : ∃ T₀ : Sylow 2 M24,
    T₀.toSubgroup ≤ octadStabilizer standardOctad ∧
    T₀.toSubgroup ≤ sextetStabilizer standardSextet ∧
    T₀.toSubgroup.comap pointEmbedding = CommonFour.standardSylow.toSubgroup :=
  CommonFour.exists_ambient_compatible_sylow

end CFSG.Quasithin.ChapterH.Section13To16
