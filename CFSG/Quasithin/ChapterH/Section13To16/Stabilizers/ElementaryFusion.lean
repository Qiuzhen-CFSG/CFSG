module

public import CFSG.Quasithin.ChapterH.Section13To16.Defs
public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion

/-!
# H.14.1(1,5): elementary subgroup classification and fusion

The new Sylow marking stabilizes the standard octad, sextet and trio at once.
All three chapter kernels are their intrinsic two-cores mapped into native M24.
The sextet and trio kernels are distinct and are exactly the E64 subgroups
of that Sylow subgroup. Every native elementary subgroup of order at least
32 is conjugate into one of these literal kernels. The Theory proof combines
exhaustive Sylow coverage with explicit native fusion, and discharges the
trio-order premise using the intrinsic translation-core calculation.
The earlier conditional placement interfaces are preserved.

Source: Aschbacher–Smith H.14 setup and H.14.1(1,5), printed pp.396–397.
-/

public section
namespace CFSG.Quasithin.ChapterH.Section13To16
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers

/-- This actual Sylow subgroup preserves all three literal standard objects. -/
theorem standardM24_commonSylow_geometry :
    ElementaryFusion.standardSylow.toSubgroup ≤ octadStabilizer standardOctad ∧
    ElementaryFusion.standardSylow.toSubgroup ≤ sextetStabilizer standardSextet ∧
    ElementaryFusion.standardSylow.toSubgroup ≤
      PairOvergroups.trioStabilizer PairOvergroups.standardTrio :=
  ⟨ElementaryFusion.standardSylow_le_octad, ElementaryFusion.standardSylow_le_sextet,
    ElementaryFusion.standardSylow_le_trio⟩

/-- Relative two-cores are all placed in the same native Sylow subgroup. -/
theorem standardM24_kernels_le_commonSylow :
    octadKernel standardOctad ≤ ElementaryFusion.standardSylow.toSubgroup ∧
    sextetKernel standardSextet ≤ ElementaryFusion.standardSylow.toSubgroup ∧
    trioKernel PairOvergroups.standardTrio ≤ ElementaryFusion.standardSylow.toSubgroup :=
  ⟨ElementaryFusion.octadCore_le_sylow,
    ElementaryFusion.core_le_sylow _ ElementaryFusion.standardSylow_le_sextet,
    ElementaryFusion.trioCore_le_sylow⟩

/-- Existence and distinctness clauses of H.14.1(1), on the literal chapter kernels. -/
theorem standardM24_two_large_kernels
    (hKT : Nat.card (trioKernel PairOvergroups.standardTrio) = 64) :
    (IsElementaryAbelian 2 (sextetKernel standardSextet) ∧
      Nat.card (sextetKernel standardSextet) = 64 ∧
      sextetKernel standardSextet ≤ ElementaryFusion.standardSylow.toSubgroup) ∧
    (IsElementaryAbelian 2 (trioKernel PairOvergroups.standardTrio) ∧
      Nat.card (trioKernel PairOvergroups.standardTrio) = 64 ∧
      trioKernel PairOvergroups.standardTrio ≤ ElementaryFusion.standardSylow.toSubgroup) ∧
    sextetKernel standardSextet ≠ trioKernel PairOvergroups.standardTrio :=
  ⟨(ElementaryFusion.intrinsic_core_placement hKT).1,
    (ElementaryFusion.intrinsic_core_placement hKT).2, ElementaryFusion.cores_distinct hKT⟩

/-- The four concrete additional candidates fuse into the source kernels. -/
theorem standardM24_additional_candidate_fusion
    (hKT : Nat.card (trioKernel PairOvergroups.standardTrio) = 64) (i : Fin 4) :
    ∃ g : M24,
      (ElementaryFusion.smallCandidate i).map (MulAut.conj g).toMonoidHom ≤
          sextetKernel standardSextet ∨
      (ElementaryFusion.smallCandidate i).map (MulAut.conj g).toMonoidHom ≤
          trioKernel PairOvergroups.standardTrio :=
  ElementaryFusion.smallCandidate_fused_into_core hKT i

/-- H.14.1(1), including existence and uniqueness for the literal intrinsic kernels. -/
theorem standardM24_card64_iff_kernel (A : Subgroup M24) :
    (IsElementaryAbelian 2 A ∧ Nat.card A = 64 ∧
      A ≤ ElementaryFusion.standardSylow.toSubgroup) ↔
      A = sextetKernel standardSextet ∨ A = trioKernel PairOvergroups.standardTrio :=
  ElementaryFusion.elementary_card64_iff_eq_core A

/-- The two E64 kernels in the compatible Sylow subgroup are distinct. -/
theorem standardM24_kernels_distinct :
    sextetKernel standardSextet ≠ trioKernel PairOvergroups.standardTrio :=
  ElementaryFusion.cores_distinct TrioAction.core_ambient_card

/-- H.14.1(5): every native elementary subgroup of rank at least five fuses into a kernel. -/
theorem m24_large_elementary_fusion (A : Subgroup M24)
    (hA : IsElementaryAbelian 2 A) (hcard : 32 ≤ Nat.card A) :
    ∃ g : M24,
      A.map (MulAut.conj g).toMonoidHom ≤ sextetKernel standardSextet ∨
      A.map (MulAut.conj g).toMonoidHom ≤ trioKernel PairOvergroups.standardTrio :=
  ElementaryFusion.large_elementary_fused_into_core A hcard

end CFSG.Quasithin.ChapterH.Section13To16
