module

public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Table
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Ranges

/-!
# Max8 transition checks 10752–11263

Each kernel check compares the supplied transition at the certified
three-point base. Range boundaries limit the size of individual reductions.
Source: primary ATLAS Tits max4/max8 programs and the fixed words in
`FiveOvergroups/Representatives`. See `DoubleCosetCover/source/` for generation.
-/

namespace Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate.Max8

open Atlas1600OrderCertificate
set_option Elab.async false
set_option maxRecDepth 20000

set_option maxHeartbeats 1600000 in
public theorem check84 : ∀ r : Fin 128, ∀ g : Fin 2,
    test genMaps repMaps nodes steps (rangeIndex 14976 10752 r) g = true := by
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check85 : ∀ r : Fin 128, ∀ g : Fin 2,
    test genMaps repMaps nodes steps (rangeIndex 14976 10880 r) g = true := by
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check86 : ∀ r : Fin 128, ∀ g : Fin 2,
    test genMaps repMaps nodes steps (rangeIndex 14976 11008 r) g = true := by
  apply allFin₂
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check87 : ∀ r : Fin 128, ∀ g : Fin 2,
    test genMaps repMaps nodes steps (rangeIndex 14976 11136 r) g = true := by
  apply allFin₂
  decide +kernel

end Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate.Max8
