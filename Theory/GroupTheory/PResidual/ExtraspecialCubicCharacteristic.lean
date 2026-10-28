module
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.PGroup.NormalPrimeImage

/-!
# Characteristic cubic lifts in extraspecial three-group quotients

For a normal two-perfect subgroup A of a finite group D, if D/O₂(D) is
extraspecial at three and A/O₂(A) has order three, the actual image of A
is the center. The full central preimage is characteristic. Taking its
two-residual recovers A: two-perfectness gives one containment, and the
normalizing two-kernel gives the reverse containment. Thus A is
characteristic without identifying either intrinsic two-core with the other.

Source application: Aschbacher–Smith, 14.7.15(1,3), printed p.1047,
refs/quasithin.pdf. LocalReduction.SolvableHeisenbergPoint applies this to
the actual point residual in the possibly proper local Heisenberg lift.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {D : Type*} [Group D] [Finite D]

/-- A normal two-perfect cubic lift in an extraspecial three-core quotient
is the characteristic two-residual of the full central preimage. -/
theorem characteristic_of_normal_twoPerfect_cubic
    [IsExtraspecial 3 (D ⧸ pCore 2 D)] (A : Subgroup D) [A.Normal]
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
    A.Characteristic := by
  let q := QuotientGroup.mk' (pCore 2 D)
  let C := A.map q
  let : C.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hcC : Nat.card C = 3 :=
    (Nat.card_congr (coreQuotientEquivImage 2 A).toEquiv).symm.trans hc
  have he : C = center (D ⧸ pCore 2 D) := eq_of_le_of_card_ge
    ((IsExtraspecial.isPGroup 3 (D ⧸ pCore 2 D)).normal_le_center_of_card_dvd_prime C
      (by rw [hcC]))
    (by rw [hcC,IsExtraspecial.center_order_p 3 (D ⧸ pCore 2 D)])
  let B := (center (D ⧸ pCore 2 D)).comap q
  let : B.Characteristic := Characteristic.comap_quotient_mk inferInstance
  let R := (pResidual 2 B).map B.subtype
  have hAB : A ≤ B := by
    rw [show B = (center (D ⧸ pCore 2 D)).comap q from rfl,←he]
    exact le_comap_map q A
  have hAR : A ≤ R := by
    have hh := embedded_pResidual_mono 2 hAB
    rwa [(pResidual_eq_top_iff 2 A).mpr hp,←MonoidHom.range_eq_map,range_subtype] at hh
  have hRA : R ≤ A := by
    apply isPPerfect_le_of_map_le_of_kernel_normalizes q R A
      (isPPerfect_embedded_pResidual 2 B)
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
      le_normalizer_of_normal
    apply (map_mono (map_subtype_le (pResidual 2 B))).trans
    change B.map q ≤ C
    rw [he]
    exact map_comap_le _ _
  have hEq : A = R := le_antisymm hAR hRA
  rw [hEq]
  infer_instance

end Subgroup
