module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.Cases
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.Certificates
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ProductCertificates.Rows000
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ProductCertificates.Rows016
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ProductCertificates.Rows032
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ProductCertificates.Rows048
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ProductCertificates.Rows064
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ProductCertificates.Rows080
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ProductCertificates.Rows096
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ProductCertificates.Rows112

/-!
# Product witnesses for all exceptional representatives

A checked catalogue of 475 shared two-factor products covers all 11,952
candidates selected by the existing `.product` mask. Every candidate has
positive words in the literal seed generators, both recovery identities use
the same right transversal, and the order tests use the certified Atlas base.
Consequently the product of the recovered seed multiples belongs to the
actual extension and has order thirteen. No seed-exhaustiveness, Sylow
factorization, or placement-family hypothesis enters this branch.

Source: Parrott (1972), section 5, p.683; `ProductCertificates/source/README.md`.
-/

public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates
open ProductCertificates

/-- All cases of the fixed product selector have actual extension witnesses. -/
theorem productWitnesses : ∀ (i : Fin 122) (a b : Fin 32) (c : Fin 15),
    witnessCase i a b c = .product → RepresentativeWitness i a b ⟨c.val + 3, by omega⟩ := by
  intro i
  fin_cases i
  · exact row000
  · exact row001
  · exact row002
  · exact row003
  · exact row004
  · exact row005
  · exact row006
  · exact row007
  · exact row008
  · exact row009
  · exact row010
  · exact row011
  · exact row012
  · exact row013
  · exact row014
  · exact row015
  · exact row016
  · exact row017
  · exact row018
  · exact row019
  · exact row020
  · exact row021
  · exact row022
  · exact row023
  · exact row024
  · exact row025
  · exact row026
  · exact row027
  · exact row028
  · exact row029
  · exact row030
  · exact row031
  · exact row032
  · exact row033
  · exact row034
  · exact row035
  · exact row036
  · exact row037
  · exact row038
  · exact row039
  · exact row040
  · exact row041
  · exact row042
  · exact row043
  · exact row044
  · exact row045
  · exact row046
  · exact row047
  · exact row048
  · exact row049
  · exact row050
  · exact row051
  · exact row052
  · exact row053
  · exact row054
  · exact row055
  · exact row056
  · exact row057
  · exact row058
  · exact row059
  · exact row060
  · exact row061
  · exact row062
  · exact row063
  · exact row064
  · exact row065
  · exact row066
  · exact row067
  · exact row068
  · exact row069
  · exact row070
  · exact row071
  · exact row072
  · exact row073
  · exact row074
  · exact row075
  · exact row076
  · exact row077
  · exact row078
  · exact row079
  · exact row080
  · exact row081
  · exact row082
  · exact row083
  · exact row084
  · exact row085
  · exact row086
  · exact row087
  · exact row088
  · exact row089
  · exact row090
  · exact row091
  · exact row092
  · exact row093
  · exact row094
  · exact row095
  · exact row096
  · exact row097
  · exact row098
  · exact row099
  · exact row100
  · exact row101
  · exact row102
  · exact row103
  · exact row104
  · exact row105
  · exact row106
  · exact row107
  · exact row108
  · exact row109
  · exact row110
  · exact row111
  · exact row112
  · exact row113
  · exact row114
  · exact row115
  · exact row116
  · exact row117
  · exact row118
  · exact row119
  · exact row120
  · exact row121

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates
