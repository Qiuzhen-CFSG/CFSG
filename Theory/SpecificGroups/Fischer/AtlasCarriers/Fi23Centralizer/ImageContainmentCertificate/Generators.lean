module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators.G0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators.G1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators.G2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators.G3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators.G4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators.G5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators.G6
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.ImageContainmentCertificate.Generators.G7

/-!
# Shared witnesses for Fi23 centralizer containment

Eight saved GAP permutations define a subgroup of the actual symmetric group
on 31671 letters. They are candidates for a generating family of the centralizer,
not an assumed centralizer description. Coverage of the actual centralizer and
their eight actions on `ImageData.point` are independent certificate obligations.
The former needs only an upper inclusion, not ambient membership of the witnesses.

See `ImageContainmentCertificate/source/README.md` for the unchanged discovery
data and generator. Source motivation: GLS3 Table 5.3u and the Fischer paragraph
around line 1042 of `refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

@[expose] public section

namespace Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate

def witnessGenerator : Fin 8 → Equiv.Perm (Fin 31671)
  | 0 => generator0
  | 1 => generator1
  | 2 => generator2
  | 3 => generator3
  | 4 => generator4
  | 5 => generator5
  | 6 => generator6
  | 7 => generator7

/-- An explicit group of proposed centralizer witnesses. No identification is
part of this definition. -/
def witnessGroup : Subgroup (Equiv.Perm (Fin 31671)) :=
  Subgroup.closure (Set.range witnessGenerator)

end Sporadic.Fischer.Fi23.CentralizerSection.ImageContainmentCertificate
