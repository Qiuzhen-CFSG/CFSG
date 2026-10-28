module

public import Theory.Mathieu.M23.QuasithinGeometry.FourNormalizers.Sylow
public import Theory.Mathieu.M23.QuasithinGeometry.FourNormalizers.Geometry
public import Theory.GroupTheory.FourGroupNormalizerOvergroup

/-!
# Strict characteristic-two overgroups of M23 four-group normalizers

Every elementary normal four-group of the certified Sylow two-subgroup is its
common four-group. Its full normalizer lies strictly in the stabilizer of its
fixed heptad, whose generalized Fitting subgroup is its two-core. Sylow conjugacy
transports this actual overgroup to every Sylow-normal four-group in native M23.

This is the native M23 normalizer calculation for the sporadic inspection in
Aschbacher--Smith 15.3.43, printed p.1140, using the Mathieu alternative in
1.1.5(3)(f), printed p.502, and the geometry of GLS3 Table 5.3d. The ambient
almost-simple transport and the maximality contradiction belong to the consumer.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry

/-- Every Sylow-normal elementary four-group of native M23 has its full normalizer
strictly contained in a subgroup with generalized Fitting subgroup equal to O₂. -/
theorem fourNormalizerOvergroups : FourNormalizerOvergroups M23 := by
  apply FourNormalizerOvergroups.of_fixed_sylow FusionCertificate.sylow
  intro V hVS hSV hV hc
  have he := FourNormalizers.normal_four_eq_common V hVS hSV hV hc
  subst V
  exact ⟨MulAction.stabilizer M23 FourNormalizers.fixedSet,
    FourNormalizers.normalizer_lt_stabilizer, FourNormalizers.stabilizer_characteristicTwo⟩

end Sporadic.Mathieu.M23Geometry
