module

public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationContracts
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationLastRelator11
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationLastRelator12
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationLastRelator13
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationLastRelator14
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationLastRelator15
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationLastRelator16
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationLastRelator17
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationLastRelator18
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationLastRelator19
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationLastRelator20
public import Theory.SpecificGroups.Lyons.Atlas111LocalRelationLastRelator21

/-!
# Matrix identities for local relators 11–21

The 121 products in `lastSpec` are certified by packed-row kernel checks in
one supporting module per relator. Finite case elimination assembles their
ordinary matrix identities into the exact universal contract `LastIdentities`.
No seed or other relation certificate is needed.

Source matrices, relators, and reproducible product checks:
`Atlas111LocalRelationSource/` and the source directories referenced there.
-/

namespace Lyons.RelationCertificate

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- All fixed matrix products used by local relators 11–21. -/
public theorem lastIdentities : LastIdentities :=
  (Fin.cases last_product0
  (Fin.cases last_product1
  (Fin.cases last_product2
  (Fin.cases last_product3
  (Fin.cases last_product4
  (Fin.cases last_product5
  (Fin.cases last_product6
  (Fin.cases last_product7
  (Fin.cases last_product8
  (Fin.cases last_product9
  (Fin.cases last_product10
  (Fin.cases last_product11
  (Fin.cases last_product12
  (Fin.cases last_product13
  (Fin.cases last_product14
  (Fin.cases last_product15
  (Fin.cases last_product16
  (Fin.cases last_product17
  (Fin.cases last_product18
  (Fin.cases last_product19
  (Fin.cases last_product20
  (Fin.cases last_product21
  (Fin.cases last_product22
  (Fin.cases last_product23
  (Fin.cases last_product24
  (Fin.cases last_product25
  (Fin.cases last_product26
  (Fin.cases last_product27
  (Fin.cases last_product28
  (Fin.cases last_product29
  (Fin.cases last_product30
  (Fin.cases last_product31
  (Fin.cases last_product32
  (Fin.cases last_product33
  (Fin.cases last_product34
  (Fin.cases last_product35
  (Fin.cases last_product36
  (Fin.cases last_product37
  (Fin.cases last_product38
  (Fin.cases last_product39
  (Fin.cases last_product40
  (Fin.cases last_product41
  (Fin.cases last_product42
  (Fin.cases last_product43
  (Fin.cases last_product44
  (Fin.cases last_product45
  (Fin.cases last_product46
  (Fin.cases last_product47
  (Fin.cases last_product48
  (Fin.cases last_product49
  (Fin.cases last_product50
  (Fin.cases last_product51
  (Fin.cases last_product52
  (Fin.cases last_product53
  (Fin.cases last_product54
  (Fin.cases last_product55
  (Fin.cases last_product56
  (Fin.cases last_product57
  (Fin.cases last_product58
  (Fin.cases last_product59
  (Fin.cases last_product60
  (Fin.cases last_product61
  (Fin.cases last_product62
  (Fin.cases last_product63
  (Fin.cases last_product64
  (Fin.cases last_product65
  (Fin.cases last_product66
  (Fin.cases last_product67
  (Fin.cases last_product68
  (Fin.cases last_product69
  (Fin.cases last_product70
  (Fin.cases last_product71
  (Fin.cases last_product72
  (Fin.cases last_product73
  (Fin.cases last_product74
  (Fin.cases last_product75
  (Fin.cases last_product76
  (Fin.cases last_product77
  (Fin.cases last_product78
  (Fin.cases last_product79
  (Fin.cases last_product80
  (Fin.cases last_product81
  (Fin.cases last_product82
  (Fin.cases last_product83
  (Fin.cases last_product84
  (Fin.cases last_product85
  (Fin.cases last_product86
  (Fin.cases last_product87
  (Fin.cases last_product88
  (Fin.cases last_product89
  (Fin.cases last_product90
  (Fin.cases last_product91
  (Fin.cases last_product92
  (Fin.cases last_product93
  (Fin.cases last_product94
  (Fin.cases last_product95
  (Fin.cases last_product96
  (Fin.cases last_product97
  (Fin.cases last_product98
  (Fin.cases last_product99
  (Fin.cases last_product100
  (Fin.cases last_product101
  (Fin.cases last_product102
  (Fin.cases last_product103
  (Fin.cases last_product104
  (Fin.cases last_product105
  (Fin.cases last_product106
  (Fin.cases last_product107
  (Fin.cases last_product108
  (Fin.cases last_product109
  (Fin.cases last_product110
  (Fin.cases last_product111
  (Fin.cases last_product112
  (Fin.cases last_product113
  (Fin.cases last_product114
  (Fin.cases last_product115
  (Fin.cases last_product116
  (Fin.cases last_product117
  (Fin.cases last_product118
  (Fin.cases last_product119
  (Fin.cases last_product120
  (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end Lyons.RelationCertificate
