module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreCentralFour

/-!
# Commutation of central-four actors at distinct original points

Each opposite-point centralizer can only fix or invert the cyclic-four
center of the other point core. Noncommutation would therefore identify
their commutator with both distinct marked involutions, which is impossible.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G]

/-- Central cyclic-four actors at distinct original points commute whenever
each centralizes the opposite point. Both point-core centers remain literal. -/
theorem distinct_point_central_four_commute
    {x y : G} {X Y : Subgroup G} (hx : TypeAt x X) (hy : TypeAt y Y)
    (hxy : x≠y) (c d : G) (hc4 : orderOf c=4) (hd4 : orderOf d=4)
    (hc2 : c^2=x) (hd2 : d^2=y)
    (hcZ : c∈(center ((involutionCentralizer x).pCoreIn 2)).map
      ((involutionCentralizer x).pCoreIn 2).subtype)
    (hdZ : d∈(center ((involutionCentralizer y).pCoreIn 2)).map
      ((involutionCentralizer y).pCoreIn 2).subtype)
    (hcy : c∈involutionCentralizer y) (hdx : d∈involutionCentralizer x) :
    Commute c d := by
  by_contra hn
  have hdc : d*c*d⁻¹=c⁻¹ :=
    hx.point_core_central_four_inverted c hc4 hcZ d hdx (fun hh => hn hh.symm)
  have hcd : c*d*c⁻¹=d⁻¹ :=
    hy.point_core_central_four_inverted d hd4 hdZ c hcy hn
  have hdc' : d*c⁻¹*d⁻¹=c := by
    have hh := congrArg Inv.inv hdc
    simpa only [mul_inv_rev,inv_inv,mul_assoc] using hh
  have he : c^2=(d^2)⁻¹ := calc
    c^2=c*(d*c⁻¹*d⁻¹) := by rw [hdc',pow_two]
    _=(c*d*c⁻¹)*d⁻¹ := by group
    _=(d^2)⁻¹ := by rw [hcd,pow_two,mul_inv_rev]
  have hy2 : y^2=1 := hy.involution ▸ pow_orderOf_eq_one y
  have hyinv : y⁻¹=y := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hy2)
  rw [hc2,hd2,hyinv] at he
  exact hxy he

end CFSG.Quasithin.HigmanSims
