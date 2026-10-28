module
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Steinberg.CertificateSoundness
import Mathlib.Tactic.FinCases

/-!
# The three central words in the published marking

All identities are checked in bounded blocks on the original 4060-point model.
Explicit map compositions avoid repeatedly reducing group powers and list products.
Source and original ATLAS attribution: Max4Geometry.Words and SylowOvergroups.
-/

open Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open CatalogueCertificate Max4Normalizers Max4Normalizers.GeneratorMaps
namespace Rudvalis.CoveringIncidence.Max4Steinberg.WordCertificates
set_option maxRecDepth 30000
set_option Elab.async false

private theorem central0 : permWord 8 = elementaryPermutation 2 := by
  apply Equiv.ext
  change ∀ x, pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))) = c2Map x
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem central1 : permWord 9 = elementaryPermutation 1 := by
  apply Equiv.ext
  change ∀ x, pc13Map (x) = c1Map x
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem central2 : permWord 10 = elementaryPermutation 0 := by
  apply Equiv.ext
  change ∀ x, pc12Map (pc13Map (x)) = c0Map x
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

public theorem centralWordIdentities : CentralWordIdentities := by
  intro i
  apply modelSubgroup.subtype_injective
  fin_cases i
  · exact (permWord_eq 8).symm.trans (central0.trans (elementaryPermutation_eq 2))
  · exact (permWord_eq 9).symm.trans (central1.trans (elementaryPermutation_eq 1))
  · exact (permWord_eq 10).symm.trans (central2.trans (elementaryPermutation_eq 0))

end Rudvalis.CoveringIncidence.Max4Steinberg.WordCertificates
