module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.CandidateTables.NumericalTests

/-!
# A strict numerical checker for the full ambient stages

This checker verifies the four auxiliary right inverses, the seven steps of
candidate A, and the five steps of candidate B, including its full conjugation.
It evaluates each intermediate natural-number index before looking up a packed
block. The two case splits change only kernel evaluation cost; `stageMap_eq`
proves agreement with the unchanged packed maps. `stageTest_sound` recovers the
three existing numerical tests, with modular padding beyond the ambient degree.

Source: the exact `WordSetup` formulas and retained ATLAS F24G1-p306936B0 data;
GLS3 Table 5.3v. The exhaustive certificates are in `NumericalChecks.Certificate`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables.NumericalChecks
open Certificate

def strictBlocks (t : Ambient.PackedBlocks) : Nat → Nat
  | 0 => t.get 0
  | i + 1 => t.get (i + 1)

def stageMap (t : Ambient.PackedBlocks) : Nat → Nat
  | 0 => lookup (strictBlocks t) 19 0 % 306936
  | i + 1 => lookup (strictBlocks t) 19 (i + 1) % 306936

theorem strictBlocks_eq (t : Ambient.PackedBlocks) (i : Nat) :
    strictBlocks t i = t.get i := by cases i <;> rfl

theorem stageMap_eq (t : Ambient.PackedBlocks) (i : Nat) :
    stageMap t i = lookup t.get 19 i % 306936 := by
  cases i <;> simp only [stageMap, lookup, strictBlocks_eq]

def stageTest (i : Nat) : Bool :=
  let x := i % 306936
  (stageMap uMapData (stageMap uInvMapData x) == x) &&
  (stageMap vMapData (stageMap vInvMapData x) == x) &&
  (stageMap wMapData (stageMap wInvMapData x) == x) &&
  (stageMap sMapData (stageMap sInvMapData x) == x) &&
  (stageMap a1MapData x == stageMap wInvMapData (stageMap rMapData (stageMap vInvMapData x))) &&
  (stageMap a2MapData x == stageMap a1MapData (stageMap a1MapData x)) &&
  (stageMap a3MapData x == stageMap a2MapData (stageMap a1MapData x)) &&
  (stageMap a5MapData x == stageMap a3MapData (stageMap a2MapData x)) &&
  (stageMap a10MapData x == stageMap a5MapData (stageMap a5MapData x)) &&
  (stageMap a15MapData x == stageMap a10MapData (stageMap a5MapData x)) &&
  (FirstFourModel.rawA x == stageMap a15MapData (stageMap a15MapData x)) &&
  (stageMap b1MapData x == stageMap uInvMapData (stageMap vMapData (stageMap vMapData x))) &&
  (stageMap b2MapData x == stageMap b1MapData (stageMap b1MapData x)) &&
  (stageMap b3MapData x == stageMap b2MapData (stageMap b1MapData x)) &&
  (stageMap b6MapData x == stageMap b3MapData (stageMap b3MapData x)) &&
  (FirstFourModel.rawB x == stageMap uMapData (stageMap sMapData (stageMap wMapData
    (stageMap b6MapData (stageMap wInvMapData (stageMap sInvMapData (stageMap uInvMapData x)))))))

theorem stageTest_sound (i : Nat) (h : stageTest i = true) :
    inverseTest i = true ∧ powerTestA i = true ∧ powerTestB i = true := by
  simp only [stageTest, Bool.and_eq_true, beq_iff_eq] at h
  simp only [inverseTest, powerTestA, powerTestB, decide_eq_true_eq, Fin.ext_iff]
  simp only [stageMap_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu, hv⟩, hw⟩, hs⟩, ha1⟩, ha2⟩, ha3⟩, ha5⟩,
    ha10⟩, ha15⟩, ha⟩, hb1⟩, hb2⟩, hb3⟩, hb6⟩, hb⟩
  exact ⟨⟨hu, hv, hw, hs⟩, ⟨ha1, ha2, ha3, ha5, ha10, ha15, ha⟩,
    ⟨hb1, hb2, hb3, hb6, hb⟩⟩

end Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables.NumericalChecks
