module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.Dihedral

/-!
# Two additional words for the local A₅ groups

The extra edge word, together with the fixed rotation, generates the candidate
edge A₅. The involution candidate, together with x and y, generates the local
A₅ candidate. These are literal subgroups of the unchanged ATLAS carrier.
The definitions assert no identification or coverage of a full normalizer or
centralizer. Source: Aschbacher, *Sporadic Groups*, 47.5 and 47.10, pp.263,
266–267; retained ATLAS J2G1-p100B0 words in `source/words.json`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
open Subgroup Theory.GroupTheory GeneratorPair

def edgeExtraWord : List (Fin 3) := [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2]
def inverterWord : List (Fin 3) := [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0]
def edgeExtra : Carrier := evalWord ![a, b, b⁻¹] edgeExtraWord
def inverter : Carrier := evalWord ![a, b, b⁻¹] inverterWord

def edgeCandidate : Subgroup Carrier := zpowers rotation ⊔ zpowers edgeExtra
def localCandidate : Subgroup Carrier := (X ⊔ Y) ⊔ zpowers inverter
def vertexCandidate : Subgroup Carrier := X ⊔ zpowers inverter

end Sporadic.LeechRelated.J2.RecognitionGeometry.LocalA5
