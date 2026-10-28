module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Index
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary

/-!
# Applying the positive-subgroup index to the three-primary transfer

The index of the prescribed projective positive subgroup is prime to three.
This discharges the index premise of the existing degree-27 cover reduction.
The cubic root-lift construction remains an explicit, independent input;
the full multiplier assertion is not claimed here.

Source: Aschbacher--Smith I.1.4(5), printed p.408, and GLS3 §6.1.
-/

public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary
open PerfectCentralCovering

universe u

/-- The literal positive subgroup now supplies the index premise; only the
independent degree-27 cubic-defect lifts remain to bound the kernel. -/
theorem not_twentySeven_dvd_kernel_of_order27_cubic_lifts
    (hlifts : ∀ (D : Type u) [Group D] [Finite D] (g : Cover D S),
      Nat.card g.toMonoidHom.ker = 27 → Nonempty (CubicDefectLift g positive))
    {E : Type u} [Group E] [Finite E] (f : Cover E S) :
    ¬ 27 ∣ Nat.card f.toMonoidHom.ker :=
  not_twentySeven_dvd_kernel_of_order27_lifts positive_not_three_dvd_index hlifts f

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary
