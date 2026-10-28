/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryGolayLocalColumnData.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TernaryGolayDiagonal

/-!
# TernaryGolayLocalColumnData

Explicit column data encode ternary coordinate permutations fixing three positions.
Finite calculations classify admissible information triples.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryGolayLocalColumnData.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


namespace Atlas.Codes

abbrev TernaryInformationTriple := Fin 3 → Fin 12

def ternaryInformationMap (t : TernaryInformationTriple) (p : TernaryParameters) :
    TernaryParameters := ![p 0,p 1,p 2,ternaryEncoder p (t 0),
      ternaryEncoder p (t 1),ternaryEncoder p (t 2)]

def ternaryBasisColumn (i : Fin 12) : Fin 6 → ZMod 3 :=
  fun k => ternaryEncoder (Pi.single k 1) i

def ternaryInformationColumn (t : TernaryInformationTriple) (i : Fin 12) :
    Fin 6 → ZMod 3 := fun k => ternaryEncoder (ternaryInformationMap t (Pi.single k 1)) i

def TernaryAdmissibleTriple (t : TernaryInformationTriple) : Prop :=
  (∀ k, 3 ≤ (t k).val) ∧ Function.Injective t ∧
    ∀ k : Fin 3, ternaryInformationColumn t ⟨k.val+5,by omega⟩ ∈
      Finset.univ.image ternaryBasisColumn

instance (t : TernaryInformationTriple) : Decidable (TernaryAdmissibleTriple t) :=
  inferInstanceAs (Decidable ((∀ k, 3 ≤ (t k).val) ∧ Function.Injective t ∧
    ∀ k : Fin 3, ternaryInformationColumn t ⟨k.val+5,by omega⟩ ∈
      Finset.univ.image ternaryBasisColumn))

theorem ternaryBasisColumn_injective : Function.Injective ternaryBasisColumn := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Only 12^3 information-coordinate triples are tested, not a permutation group.
theorem ternaryAdmissibleTriple_count :
    (Finset.univ.filter TernaryAdmissibleTriple).card = 6 := by
  decide +kernel

end Atlas.Codes
