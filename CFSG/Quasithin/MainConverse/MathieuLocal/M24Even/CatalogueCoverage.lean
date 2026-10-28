module

public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even.LocalData
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.Coverage

/-!
# The complete normal elementary catalogue for the M₂₄ converse

Every nontrivial elementary abelian subgroup normal inside the fixed Sylow
carrier equals one of the 22 concrete generator rows. The lower-layer theorem
proves this by finite conjugate-product and row-pair certificates, using only
intrinsic normality and exponent two.

This discharges the catalogue premise of the condition E assembly. The ambient
normalizer premise remains independent. Source: Aschbacher–Smith, condition E
and Theorem 0.1.2(5), printed pp.3–4; GLS3, Table 5.3e.
-/

namespace CFSG.Quasithin.MainConverse.M24Even
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry

public theorem normalElementaryCatalogue : NormalElementaryCatalogue := by
  intro R hR hn he
  let : IsElementaryAbelian 2 R := he
  apply EvenCatalogue.Coverage.catalogue_of_normal_exponent_two R hR hn
  intro x hx
  simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx

end CFSG.Quasithin.MainConverse.M24Even
