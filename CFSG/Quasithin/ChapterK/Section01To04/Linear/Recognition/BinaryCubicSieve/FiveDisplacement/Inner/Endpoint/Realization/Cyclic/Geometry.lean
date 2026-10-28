module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Realization.Cyclic.Certificates
public import Mathlib.Tactic.Abel

/-!
# Additivity and generator actions for the endpoint orbit vectors

An incident pair (x, φ), with φ(x) = 0, represents the rank-one matrix xφ.
The 41 checked triangles in `Certificates` are translates of the two active root relations;
root words fixing the highest vector identify their three orbit vectors.
Summing those triangles checks conjugation by each adjacent exchange and
by the transvection I + E₀₁ on the twenty root and four diagonal vectors.
Every finite matrix identity is checked by kernel reduction. The Python
search in `source/` only selects witnesses; it is not part of the proof.

Source: GM, *Classification of 2F-modules, II*, Lemma 4.5 step 2, pp.23–24.
The final cyclic-map module consumes `image_action` with the literal
trace-zero matrix coordinates.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Representation
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Cyclic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {σ : Representation (ZMod 2) Group V} {v : V}

private theorem image_action0_0 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 0) = ((actionIndices 0 0).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 0) = _
  simp only [transport0_0 h]
  change orbit σ v 5 = ((orbit σ v 5) + 0)
  abel

private theorem image_action0_1 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 1) = ((actionIndices 0 1).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 1) = _
  simp only [transport0_1 h]
  change orbit σ v 6 = ((orbit σ v 6) + 0)
  abel

private theorem image_action0_2 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 2) = ((actionIndices 0 2).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 2) = _
  simp only [transport0_2 h]
  change orbit σ v 7 = ((orbit σ v 7) + 0)
  abel

private theorem image_action0_3 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 3) = ((actionIndices 0 3).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 3) = _
  simp only [transport0_3 h]
  change orbit σ v 8 = ((orbit σ v 8) + 0)
  abel

private theorem image_action0_4 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 4) = ((actionIndices 0 4).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 5) = _
  simp only [transport0_5 h]
  change orbit σ v 0 = ((orbit σ v 0) + 0)
  abel

private theorem image_action0_5 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 5) = ((actionIndices 0 5).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 6) = _
  simp only [transport0_6 h]
  change orbit σ v 1 = ((orbit σ v 1) + 0)
  abel

private theorem image_action0_6 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 6) = ((actionIndices 0 6).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 7) = _
  simp only [transport0_7 h]
  change orbit σ v 2 = ((orbit σ v 2) + 0)
  abel

private theorem image_action0_7 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 7) = ((actionIndices 0 7).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 8) = _
  simp only [transport0_8 h]
  change orbit σ v 3 = ((orbit σ v 3) + 0)
  abel

private theorem image_action0_8 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 8) = ((actionIndices 0 8).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 15) = _
  simp only [transport0_15 h]
  change orbit σ v 16 = ((orbit σ v 16) + 0)
  abel

private theorem image_action0_9 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 9) = ((actionIndices 0 9).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 16) = _
  simp only [transport0_16 h]
  change orbit σ v 15 = ((orbit σ v 15) + 0)
  abel

private theorem image_action0_10 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 10) = ((actionIndices 0 10).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 18) = _
  simp only [transport0_18 h]
  change orbit σ v 18 = ((orbit σ v 18) + 0)
  abel

private theorem image_action0_11 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 11) = ((actionIndices 0 11).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 19) = _
  simp only [transport0_19 h]
  change orbit σ v 19 = ((orbit σ v 19) + 0)
  abel

private theorem image_action0_12 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 12) = ((actionIndices 0 12).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 25) = _
  simp only [transport0_25 h]
  change orbit σ v 26 = ((orbit σ v 26) + 0)
  abel

private theorem image_action0_13 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 13) = ((actionIndices 0 13).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 26) = _
  simp only [transport0_26 h]
  change orbit σ v 25 = ((orbit σ v 25) + 0)
  abel

private theorem image_action0_14 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 14) = ((actionIndices 0 14).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 28) = _
  simp only [transport0_28 h]
  change orbit σ v 28 = ((orbit σ v 28) + 0)
  abel

private theorem image_action0_15 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 15) = ((actionIndices 0 15).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 29) = _
  simp only [transport0_29 h]
  change orbit σ v 29 = ((orbit σ v 29) + 0)
  abel

private theorem image_action0_16 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 16) = ((actionIndices 0 16).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 43) = _
  simp only [transport0_43 h]
  change orbit σ v 44 = ((orbit σ v 44) + 0)
  abel

private theorem image_action0_17 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 17) = ((actionIndices 0 17).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 44) = _
  simp only [transport0_44 h]
  change orbit σ v 43 = ((orbit σ v 43) + 0)
  abel

private theorem image_action0_18 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 18) = ((actionIndices 0 18).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 46) = _
  simp only [transport0_46 h]
  change orbit σ v 46 = ((orbit σ v 46) + 0)
  abel

private theorem image_action0_19 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 19) = ((actionIndices 0 19).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 47) = _
  simp only [transport0_47 h]
  change orbit σ v 47 = ((orbit σ v 47) + 0)
  abel

private theorem image_action0_20 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 20) = ((actionIndices 0 20).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 51 + orbit σ v 3 + orbit σ v 43) = _
  simp only [map_add, transport0_51 h, transport0_3 h, transport0_43 h]
  change orbit σ v 56 + orbit σ v 8 + orbit σ v 44 = ((orbit σ v 56 + orbit σ v 8 + orbit σ v 44) + 0)
  abel

private theorem image_action0_21 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 21) = ((actionIndices 0 21).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 56 + orbit σ v 8 + orbit σ v 44) = _
  simp only [map_add, transport0_56 h, transport0_8 h, transport0_44 h]
  change orbit σ v 51 + orbit σ v 3 + orbit σ v 43 = ((orbit σ v 51 + orbit σ v 3 + orbit σ v 43) + 0)
  abel

private theorem image_action0_22 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 22) = ((actionIndices 0 22).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 60 + orbit σ v 19 + orbit σ v 46) = _
  simp only [map_add, transport0_60 h, transport0_19 h, transport0_46 h]
  change orbit σ v 60 + orbit σ v 19 + orbit σ v 46 = ((orbit σ v 60 + orbit σ v 19 + orbit σ v 46) + 0)
  abel

private theorem image_action0_23 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 0) (imageVector σ v 23) = ((actionIndices 0 23).map (imageVector σ v)).sum := by
  change σ (generator 0) (orbit σ v 63 + orbit σ v 29 + orbit σ v 47) = _
  simp only [map_add, transport0_63 h, transport0_29 h, transport0_47 h]
  change orbit σ v 63 + orbit σ v 29 + orbit σ v 47 = ((orbit σ v 63 + orbit σ v 29 + orbit σ v 47) + 0)
  abel

private theorem image_action1_0 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 0) = ((actionIndices 1 0).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 0) = _
  simp only [transport1_0 h]
  change orbit σ v 1 = ((orbit σ v 1) + 0)
  abel

private theorem image_action1_1 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 1) = ((actionIndices 1 1).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 1) = _
  simp only [transport1_1 h]
  change orbit σ v 0 = ((orbit σ v 0) + 0)
  abel

private theorem image_action1_2 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 2) = ((actionIndices 1 2).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 2) = _
  simp only [transport1_2 h]
  change orbit σ v 2 = ((orbit σ v 2) + 0)
  abel

private theorem image_action1_3 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 3) = ((actionIndices 1 3).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 3) = _
  simp only [transport1_3 h]
  change orbit σ v 3 = ((orbit σ v 3) + 0)
  abel

private theorem image_action1_4 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 4) = ((actionIndices 1 4).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 5) = _
  simp only [transport1_5 h]
  change orbit σ v 15 = ((orbit σ v 15) + 0)
  abel

private theorem image_action1_5 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 5) = ((actionIndices 1 5).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 6) = _
  simp only [transport1_6 h]
  change orbit σ v 16 = ((orbit σ v 16) + 0)
  abel

private theorem image_action1_6 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 6) = ((actionIndices 1 6).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 7) = _
  simp only [transport1_7 h]
  change orbit σ v 18 = ((orbit σ v 18) + 0)
  abel

private theorem image_action1_7 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 7) = ((actionIndices 1 7).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 8) = _
  simp only [transport1_8 h]
  change orbit σ v 19 = ((orbit σ v 19) + 0)
  abel

private theorem image_action1_8 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 8) = ((actionIndices 1 8).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 15) = _
  simp only [transport1_15 h]
  change orbit σ v 5 = ((orbit σ v 5) + 0)
  abel

private theorem image_action1_9 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 9) = ((actionIndices 1 9).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 16) = _
  simp only [transport1_16 h]
  change orbit σ v 6 = ((orbit σ v 6) + 0)
  abel

private theorem image_action1_10 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 10) = ((actionIndices 1 10).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 18) = _
  simp only [transport1_18 h]
  change orbit σ v 7 = ((orbit σ v 7) + 0)
  abel

private theorem image_action1_11 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 11) = ((actionIndices 1 11).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 19) = _
  simp only [transport1_19 h]
  change orbit σ v 8 = ((orbit σ v 8) + 0)
  abel

private theorem image_action1_12 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 12) = ((actionIndices 1 12).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 25) = _
  simp only [transport1_25 h]
  change orbit σ v 25 = ((orbit σ v 25) + 0)
  abel

private theorem image_action1_13 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 13) = ((actionIndices 1 13).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 26) = _
  simp only [transport1_26 h]
  change orbit σ v 28 = ((orbit σ v 28) + 0)
  abel

private theorem image_action1_14 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 14) = ((actionIndices 1 14).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 28) = _
  simp only [transport1_28 h]
  change orbit σ v 26 = ((orbit σ v 26) + 0)
  abel

private theorem image_action1_15 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 15) = ((actionIndices 1 15).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 29) = _
  simp only [transport1_29 h]
  change orbit σ v 29 = ((orbit σ v 29) + 0)
  abel

private theorem image_action1_16 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 16) = ((actionIndices 1 16).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 43) = _
  simp only [transport1_43 h]
  change orbit σ v 43 = ((orbit σ v 43) + 0)
  abel

private theorem image_action1_17 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 17) = ((actionIndices 1 17).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 44) = _
  simp only [transport1_44 h]
  change orbit σ v 46 = ((orbit σ v 46) + 0)
  abel

private theorem image_action1_18 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 18) = ((actionIndices 1 18).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 46) = _
  simp only [transport1_46 h]
  change orbit σ v 44 = ((orbit σ v 44) + 0)
  abel

private theorem image_action1_19 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 19) = ((actionIndices 1 19).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 47) = _
  simp only [transport1_47 h]
  change orbit σ v 47 = ((orbit σ v 47) + 0)
  abel

private theorem image_action1_20 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 20) = ((actionIndices 1 20).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 51 + orbit σ v 3 + orbit σ v 43) = _
  simp only [map_add, transport1_51 h, transport1_3 h, transport1_43 h]
  change orbit σ v 51 + orbit σ v 3 + orbit σ v 43 = ((orbit σ v 51 + orbit σ v 3 + orbit σ v 43) + 0)
  abel

private theorem image_action1_21 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 21) = ((actionIndices 1 21).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 56 + orbit σ v 8 + orbit σ v 44) = _
  simp only [map_add, transport1_56 h, transport1_8 h, transport1_44 h]
  change orbit σ v 60 + orbit σ v 19 + orbit σ v 46 = ((orbit σ v 60 + orbit σ v 19 + orbit σ v 46) + 0)
  abel

private theorem image_action1_22 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 22) = ((actionIndices 1 22).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 60 + orbit σ v 19 + orbit σ v 46) = _
  simp only [map_add, transport1_60 h, transport1_19 h, transport1_46 h]
  change orbit σ v 56 + orbit σ v 8 + orbit σ v 44 = ((orbit σ v 56 + orbit σ v 8 + orbit σ v 44) + 0)
  abel

private theorem image_action1_23 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 1) (imageVector σ v 23) = ((actionIndices 1 23).map (imageVector σ v)).sum := by
  change σ (generator 1) (orbit σ v 63 + orbit σ v 29 + orbit σ v 47) = _
  simp only [map_add, transport1_63 h, transport1_29 h, transport1_47 h]
  change orbit σ v 63 + orbit σ v 29 + orbit σ v 47 = ((orbit σ v 63 + orbit σ v 29 + orbit σ v 47) + 0)
  abel

private theorem image_action2_0 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 0) = ((actionIndices 2 0).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 0) = _
  simp only [transport2_0 h]
  change orbit σ v 0 = ((orbit σ v 0) + 0)
  abel

private theorem image_action2_1 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 1) = ((actionIndices 2 1).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 1) = _
  simp only [transport2_1 h]
  change orbit σ v 2 = ((orbit σ v 2) + 0)
  abel

private theorem image_action2_2 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 2) = ((actionIndices 2 2).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 2) = _
  simp only [transport2_2 h]
  change orbit σ v 1 = ((orbit σ v 1) + 0)
  abel

private theorem image_action2_3 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 3) = ((actionIndices 2 3).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 3) = _
  simp only [transport2_3 h]
  change orbit σ v 3 = ((orbit σ v 3) + 0)
  abel

private theorem image_action2_4 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 4) = ((actionIndices 2 4).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 5) = _
  simp only [transport2_5 h]
  change orbit σ v 5 = ((orbit σ v 5) + 0)
  abel

private theorem image_action2_5 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 5) = ((actionIndices 2 5).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 6) = _
  simp only [transport2_6 h]
  change orbit σ v 7 = ((orbit σ v 7) + 0)
  abel

private theorem image_action2_6 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 6) = ((actionIndices 2 6).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 7) = _
  simp only [transport2_7 h]
  change orbit σ v 6 = ((orbit σ v 6) + 0)
  abel

private theorem image_action2_7 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 7) = ((actionIndices 2 7).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 8) = _
  simp only [transport2_8 h]
  change orbit σ v 8 = ((orbit σ v 8) + 0)
  abel

private theorem image_action2_8 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 8) = ((actionIndices 2 8).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 15) = _
  simp only [transport2_15 h]
  change orbit σ v 25 = ((orbit σ v 25) + 0)
  abel

private theorem image_action2_9 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 9) = ((actionIndices 2 9).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 16) = _
  simp only [transport2_16 h]
  change orbit σ v 26 = ((orbit σ v 26) + 0)
  abel

private theorem image_action2_10 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 10) = ((actionIndices 2 10).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 18) = _
  simp only [transport2_18 h]
  change orbit σ v 28 = ((orbit σ v 28) + 0)
  abel

private theorem image_action2_11 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 11) = ((actionIndices 2 11).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 19) = _
  simp only [transport2_19 h]
  change orbit σ v 29 = ((orbit σ v 29) + 0)
  abel

private theorem image_action2_12 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 12) = ((actionIndices 2 12).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 25) = _
  simp only [transport2_25 h]
  change orbit σ v 15 = ((orbit σ v 15) + 0)
  abel

private theorem image_action2_13 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 13) = ((actionIndices 2 13).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 26) = _
  simp only [transport2_26 h]
  change orbit σ v 16 = ((orbit σ v 16) + 0)
  abel

private theorem image_action2_14 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 14) = ((actionIndices 2 14).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 28) = _
  simp only [transport2_28 h]
  change orbit σ v 18 = ((orbit σ v 18) + 0)
  abel

private theorem image_action2_15 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 15) = ((actionIndices 2 15).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 29) = _
  simp only [transport2_29 h]
  change orbit σ v 19 = ((orbit σ v 19) + 0)
  abel

private theorem image_action2_16 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 16) = ((actionIndices 2 16).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 43) = _
  simp only [transport2_43 h]
  change orbit σ v 43 = ((orbit σ v 43) + 0)
  abel

private theorem image_action2_17 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 17) = ((actionIndices 2 17).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 44) = _
  simp only [transport2_44 h]
  change orbit σ v 44 = ((orbit σ v 44) + 0)
  abel

private theorem image_action2_18 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 18) = ((actionIndices 2 18).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 46) = _
  simp only [transport2_46 h]
  change orbit σ v 47 = ((orbit σ v 47) + 0)
  abel

private theorem image_action2_19 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 19) = ((actionIndices 2 19).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 47) = _
  simp only [transport2_47 h]
  change orbit σ v 46 = ((orbit σ v 46) + 0)
  abel

private theorem image_action2_20 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 20) = ((actionIndices 2 20).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 51 + orbit σ v 3 + orbit σ v 43) = _
  simp only [map_add, transport2_51 h, transport2_3 h, transport2_43 h]
  change orbit σ v 51 + orbit σ v 3 + orbit σ v 43 = ((orbit σ v 51 + orbit σ v 3 + orbit σ v 43) + 0)
  abel

private theorem image_action2_21 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 21) = ((actionIndices 2 21).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 56 + orbit σ v 8 + orbit σ v 44) = _
  simp only [map_add, transport2_56 h, transport2_8 h, transport2_44 h]
  change orbit σ v 56 + orbit σ v 8 + orbit σ v 44 = ((orbit σ v 56 + orbit σ v 8 + orbit σ v 44) + 0)
  abel

private theorem image_action2_22 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 22) = ((actionIndices 2 22).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 60 + orbit σ v 19 + orbit σ v 46) = _
  simp only [map_add, transport2_60 h, transport2_19 h, transport2_46 h]
  change orbit σ v 63 + orbit σ v 29 + orbit σ v 47 = ((orbit σ v 63 + orbit σ v 29 + orbit σ v 47) + 0)
  abel

private theorem image_action2_23 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 2) (imageVector σ v 23) = ((actionIndices 2 23).map (imageVector σ v)).sum := by
  change σ (generator 2) (orbit σ v 63 + orbit σ v 29 + orbit σ v 47) = _
  simp only [map_add, transport2_63 h, transport2_29 h, transport2_47 h]
  change orbit σ v 60 + orbit σ v 19 + orbit σ v 46 = ((orbit σ v 60 + orbit σ v 19 + orbit σ v 46) + 0)
  abel

private theorem image_action3_0 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 0) = ((actionIndices 3 0).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 0) = _
  simp only [transport3_0 h]
  change orbit σ v 0 = ((orbit σ v 0) + 0)
  abel

private theorem image_action3_1 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 1) = ((actionIndices 3 1).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 1) = _
  simp only [transport3_1 h]
  change orbit σ v 1 = ((orbit σ v 1) + 0)
  abel

private theorem image_action3_2 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 2) = ((actionIndices 3 2).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 2) = _
  simp only [transport3_2 h]
  change orbit σ v 3 = ((orbit σ v 3) + 0)
  abel

private theorem image_action3_3 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 3) = ((actionIndices 3 3).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 3) = _
  simp only [transport3_3 h]
  change orbit σ v 2 = ((orbit σ v 2) + 0)
  abel

private theorem image_action3_4 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 4) = ((actionIndices 3 4).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 5) = _
  simp only [transport3_5 h]
  change orbit σ v 5 = ((orbit σ v 5) + 0)
  abel

private theorem image_action3_5 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 5) = ((actionIndices 3 5).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 6) = _
  simp only [transport3_6 h]
  change orbit σ v 6 = ((orbit σ v 6) + 0)
  abel

private theorem image_action3_6 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 6) = ((actionIndices 3 6).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 7) = _
  simp only [transport3_7 h]
  change orbit σ v 8 = ((orbit σ v 8) + 0)
  abel

private theorem image_action3_7 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 7) = ((actionIndices 3 7).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 8) = _
  simp only [transport3_8 h]
  change orbit σ v 7 = ((orbit σ v 7) + 0)
  abel

private theorem image_action3_8 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 8) = ((actionIndices 3 8).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 15) = _
  simp only [transport3_15 h]
  change orbit σ v 15 = ((orbit σ v 15) + 0)
  abel

private theorem image_action3_9 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 9) = ((actionIndices 3 9).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 16) = _
  simp only [transport3_16 h]
  change orbit σ v 16 = ((orbit σ v 16) + 0)
  abel

private theorem image_action3_10 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 10) = ((actionIndices 3 10).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 18) = _
  simp only [transport3_18 h]
  change orbit σ v 19 = ((orbit σ v 19) + 0)
  abel

private theorem image_action3_11 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 11) = ((actionIndices 3 11).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 19) = _
  simp only [transport3_19 h]
  change orbit σ v 18 = ((orbit σ v 18) + 0)
  abel

private theorem image_action3_12 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 12) = ((actionIndices 3 12).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 25) = _
  simp only [transport3_25 h]
  change orbit σ v 43 = ((orbit σ v 43) + 0)
  abel

private theorem image_action3_13 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 13) = ((actionIndices 3 13).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 26) = _
  simp only [transport3_26 h]
  change orbit σ v 44 = ((orbit σ v 44) + 0)
  abel

private theorem image_action3_14 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 14) = ((actionIndices 3 14).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 28) = _
  simp only [transport3_28 h]
  change orbit σ v 46 = ((orbit σ v 46) + 0)
  abel

private theorem image_action3_15 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 15) = ((actionIndices 3 15).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 29) = _
  simp only [transport3_29 h]
  change orbit σ v 47 = ((orbit σ v 47) + 0)
  abel

private theorem image_action3_16 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 16) = ((actionIndices 3 16).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 43) = _
  simp only [transport3_43 h]
  change orbit σ v 25 = ((orbit σ v 25) + 0)
  abel

private theorem image_action3_17 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 17) = ((actionIndices 3 17).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 44) = _
  simp only [transport3_44 h]
  change orbit σ v 26 = ((orbit σ v 26) + 0)
  abel

private theorem image_action3_18 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 18) = ((actionIndices 3 18).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 46) = _
  simp only [transport3_46 h]
  change orbit σ v 28 = ((orbit σ v 28) + 0)
  abel

private theorem image_action3_19 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 19) = ((actionIndices 3 19).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 47) = _
  simp only [transport3_47 h]
  change orbit σ v 29 = ((orbit σ v 29) + 0)
  abel

private theorem image_action3_20 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 20) = ((actionIndices 3 20).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 51 + orbit σ v 3 + orbit σ v 43) = _
  simp only [map_add, transport3_51 h, transport3_3 h, transport3_43 h]
  change orbit σ v 32 + orbit σ v 2 + orbit σ v 25 = ((orbit σ v 51 + orbit σ v 3 + orbit σ v 43) + ((orbit σ v 63 + orbit σ v 29 + orbit σ v 47) + 0))
  calc
    _ = (orbit σ v 25 + orbit σ v 43 + orbit σ v 62) + (orbit σ v 2 + orbit σ v 47 + orbit σ v 50) + (orbit σ v 3 + orbit σ v 29 + orbit σ v 35) + (orbit σ v 32 + orbit σ v 35 + orbit σ v 36) + (orbit σ v 50 + orbit σ v 51 + orbit σ v 54) + (orbit σ v 62 + orbit σ v 63 + orbit σ v 64) + (orbit σ v 36 + orbit σ v 54 + orbit σ v 64) + (((orbit σ v 51 + orbit σ v 3 + orbit σ v 43) + ((orbit σ v 63 + orbit σ v 29 + orbit σ v 47) + 0))) := by
      abel_nf
      simp [binary_two_zsmul]
    _ = _ := by rw [triangle10 h, triangle40 h, triangle52 h, triangle465 h, triangle507 h, triangle539 h, triangle920 h]; simp

private theorem image_action3_21 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 21) = ((actionIndices 3 21).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 56 + orbit σ v 8 + orbit σ v 44) = _
  simp only [map_add, transport3_56 h, transport3_8 h, transport3_44 h]
  change orbit σ v 38 + orbit σ v 7 + orbit σ v 26 = ((orbit σ v 56 + orbit σ v 8 + orbit σ v 44) + ((orbit σ v 63 + orbit σ v 29 + orbit σ v 47) + 0))
  calc
    _ = (orbit σ v 5 + orbit σ v 25 + orbit σ v 37) + (orbit σ v 5 + orbit σ v 43 + orbit σ v 55) + (orbit σ v 25 + orbit σ v 43 + orbit σ v 62) + (orbit σ v 0 + orbit σ v 26 + orbit σ v 30) + (orbit σ v 0 + orbit σ v 44 + orbit σ v 48) + (orbit σ v 2 + orbit σ v 7 + orbit σ v 11) + (orbit σ v 2 + orbit σ v 47 + orbit σ v 50) + (orbit σ v 3 + orbit σ v 8 + orbit σ v 13) + (orbit σ v 3 + orbit σ v 29 + orbit σ v 35) + (orbit σ v 9 + orbit σ v 11 + orbit σ v 12) + (orbit σ v 9 + orbit σ v 13 + orbit σ v 14) + (orbit σ v 30 + orbit σ v 32 + orbit σ v 33) + (orbit σ v 32 + orbit σ v 35 + orbit σ v 36) + (orbit σ v 37 + orbit σ v 38 + orbit σ v 39) + (orbit σ v 48 + orbit σ v 51 + orbit σ v 52) + (orbit σ v 50 + orbit σ v 51 + orbit σ v 54) + (orbit σ v 55 + orbit σ v 56 + orbit σ v 57) + (orbit σ v 62 + orbit σ v 63 + orbit σ v 64) + (orbit σ v 12 + orbit σ v 33 + orbit σ v 39) + (orbit σ v 14 + orbit σ v 52 + orbit σ v 57) + (orbit σ v 36 + orbit σ v 54 + orbit σ v 64) + (((orbit σ v 56 + orbit σ v 8 + orbit σ v 44) + ((orbit σ v 63 + orbit σ v 29 + orbit σ v 47) + 0))) := by
      abel_nf
      simp [binary_two_zsmul]
    _ = _ := by rw [triangle2 h, triangle4 h, triangle10 h, triangle14 h, triangle16 h, triangle36 h, triangle40 h, triangle48 h, triangle52 h, triangle413 h, triangle415 h, triangle453 h, triangle465 h, triangle467 h, triangle497 h, triangle507 h, triangle511 h, triangle539 h, triangle826 h, triangle870 h, triangle920 h]; simp

private theorem image_action3_22 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 22) = ((actionIndices 3 22).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 60 + orbit σ v 19 + orbit σ v 46) = _
  simp only [map_add, transport3_60 h, transport3_19 h, transport3_46 h]
  change orbit σ v 41 + orbit σ v 18 + orbit σ v 28 = ((orbit σ v 60 + orbit σ v 19 + orbit σ v 46) + ((orbit σ v 63 + orbit σ v 29 + orbit σ v 47) + 0))
  calc
    _ = (orbit σ v 15 + orbit σ v 25 + orbit σ v 40) + (orbit σ v 15 + orbit σ v 43 + orbit σ v 59) + (orbit σ v 25 + orbit σ v 43 + orbit σ v 62) + (orbit σ v 1 + orbit σ v 28 + orbit σ v 31) + (orbit σ v 1 + orbit σ v 46 + orbit σ v 49) + (orbit σ v 2 + orbit σ v 18 + orbit σ v 21) + (orbit σ v 2 + orbit σ v 47 + orbit σ v 50) + (orbit σ v 3 + orbit σ v 19 + orbit σ v 23) + (orbit σ v 3 + orbit σ v 29 + orbit σ v 35) + (orbit σ v 20 + orbit σ v 21 + orbit σ v 22) + (orbit σ v 20 + orbit σ v 23 + orbit σ v 24) + (orbit σ v 31 + orbit σ v 32 + orbit σ v 34) + (orbit σ v 32 + orbit σ v 35 + orbit σ v 36) + (orbit σ v 40 + orbit σ v 41 + orbit σ v 42) + (orbit σ v 49 + orbit σ v 51 + orbit σ v 53) + (orbit σ v 50 + orbit σ v 51 + orbit σ v 54) + (orbit σ v 59 + orbit σ v 60 + orbit σ v 61) + (orbit σ v 62 + orbit σ v 63 + orbit σ v 64) + (orbit σ v 22 + orbit σ v 34 + orbit σ v 42) + (orbit σ v 24 + orbit σ v 53 + orbit σ v 61) + (orbit σ v 36 + orbit σ v 54 + orbit σ v 64) + (((orbit σ v 60 + orbit σ v 19 + orbit σ v 46) + ((orbit σ v 63 + orbit σ v 29 + orbit σ v 47) + 0))) := by
      abel_nf
      simp [binary_two_zsmul]
    _ = _ := by rw [triangle6 h, triangle8 h, triangle10 h, triangle26 h, triangle28 h, triangle38 h, triangle40 h, triangle50 h, triangle52 h, triangle429 h, triangle431 h, triangle457 h, triangle465 h, triangle481 h, triangle501 h, triangle507 h, triangle525 h, triangle539 h, triangle844 h, triangle888 h, triangle920 h]; simp

private theorem image_action3_23 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 3) (imageVector σ v 23) = ((actionIndices 3 23).map (imageVector σ v)).sum := by
  change σ (generator 3) (orbit σ v 63 + orbit σ v 29 + orbit σ v 47) = _
  simp only [map_add, transport3_63 h, transport3_29 h, transport3_47 h]
  change orbit σ v 63 + orbit σ v 47 + orbit σ v 29 = ((orbit σ v 63 + orbit σ v 29 + orbit σ v 47) + 0)
  abel

private theorem image_action4_0 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 0) = ((actionIndices 4 0).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 0) = _
  simp only [transport4_0 h]
  change orbit σ v 0 = ((orbit σ v 0) + 0)
  abel

private theorem image_action4_1 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 1) = ((actionIndices 4 1).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 1) = _
  simp only [transport4_1 h]
  change orbit σ v 1 = ((orbit σ v 1) + 0)
  abel

private theorem image_action4_2 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 2) = ((actionIndices 4 2).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 2) = _
  simp only [transport4_2 h]
  change orbit σ v 2 = ((orbit σ v 2) + 0)
  abel

private theorem image_action4_3 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 3) = ((actionIndices 4 3).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 3) = _
  simp only [transport4_3 h]
  change orbit σ v 3 = ((orbit σ v 3) + 0)
  abel

private theorem image_action4_4 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 4) = ((actionIndices 4 4).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 5) = _
  simp only [transport4_5 h]
  change orbit σ v 9 = ((orbit σ v 0) + ((orbit σ v 5) + ((orbit σ v 51 + orbit σ v 3 + orbit σ v 43) + ((orbit σ v 56 + orbit σ v 8 + orbit σ v 44) + 0))))
  calc
    _ = (orbit σ v 5 + orbit σ v 43 + orbit σ v 55) + (orbit σ v 0 + orbit σ v 44 + orbit σ v 48) + (orbit σ v 3 + orbit σ v 8 + orbit σ v 13) + (orbit σ v 9 + orbit σ v 13 + orbit σ v 14) + (orbit σ v 48 + orbit σ v 51 + orbit σ v 52) + (orbit σ v 55 + orbit σ v 56 + orbit σ v 57) + (orbit σ v 14 + orbit σ v 52 + orbit σ v 57) + (((orbit σ v 0) + ((orbit σ v 5) + ((orbit σ v 51 + orbit σ v 3 + orbit σ v 43) + ((orbit σ v 56 + orbit σ v 8 + orbit σ v 44) + 0))))) := by
      abel_nf
      simp [binary_two_zsmul]
    _ = _ := by rw [triangle4 h, triangle16 h, triangle48 h, triangle415 h, triangle497 h, triangle511 h, triangle870 h]; simp

private theorem image_action4_5 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 5) = ((actionIndices 4 5).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 6) = _
  simp only [transport4_6 h]
  change orbit σ v 10 = ((orbit σ v 1) + ((orbit σ v 6) + 0))
  calc
    _ = (orbit σ v 1 + orbit σ v 6 + orbit σ v 10) + (((orbit σ v 1) + ((orbit σ v 6) + 0))) := by
      abel_nf
      simp [binary_two_zsmul]
    _ = _ := by rw [triangle24 h]; simp

private theorem image_action4_6 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 6) = ((actionIndices 4 6).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 7) = _
  simp only [transport4_7 h]
  change orbit σ v 11 = ((orbit σ v 2) + ((orbit σ v 7) + 0))
  calc
    _ = (orbit σ v 2 + orbit σ v 7 + orbit σ v 11) + (((orbit σ v 2) + ((orbit σ v 7) + 0))) := by
      abel_nf
      simp [binary_two_zsmul]
    _ = _ := by rw [triangle36 h]; simp

private theorem image_action4_7 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 7) = ((actionIndices 4 7).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 8) = _
  simp only [transport4_8 h]
  change orbit σ v 13 = ((orbit σ v 3) + ((orbit σ v 8) + 0))
  calc
    _ = (orbit σ v 3 + orbit σ v 8 + orbit σ v 13) + (((orbit σ v 3) + ((orbit σ v 8) + 0))) := by
      abel_nf
      simp [binary_two_zsmul]
    _ = _ := by rw [triangle48 h]; simp

private theorem image_action4_8 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 8) = ((actionIndices 4 8).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 15) = _
  simp only [transport4_15 h]
  change orbit σ v 17 = ((orbit σ v 15) + ((orbit σ v 16) + 0))
  calc
    _ = (orbit σ v 15 + orbit σ v 16 + orbit σ v 17) + (((orbit σ v 15) + ((orbit σ v 16) + 0))) := by
      abel_nf
      simp [binary_two_zsmul]
    _ = _ := by rw [triangle25 h]; simp

private theorem image_action4_9 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 9) = ((actionIndices 4 9).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 16) = _
  simp only [transport4_16 h]
  change orbit σ v 16 = ((orbit σ v 16) + 0)
  abel

private theorem image_action4_10 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 10) = ((actionIndices 4 10).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 18) = _
  simp only [transport4_18 h]
  change orbit σ v 18 = ((orbit σ v 18) + 0)
  abel

private theorem image_action4_11 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 11) = ((actionIndices 4 11).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 19) = _
  simp only [transport4_19 h]
  change orbit σ v 19 = ((orbit σ v 19) + 0)
  abel

private theorem image_action4_12 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 12) = ((actionIndices 4 12).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 25) = _
  simp only [transport4_25 h]
  change orbit σ v 27 = ((orbit σ v 25) + ((orbit σ v 26) + 0))
  calc
    _ = (orbit σ v 25 + orbit σ v 26 + orbit σ v 27) + (((orbit σ v 25) + ((orbit σ v 26) + 0))) := by
      abel_nf
      simp [binary_two_zsmul]
    _ = _ := by rw [triangle37 h]; simp

private theorem image_action4_13 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 13) = ((actionIndices 4 13).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 26) = _
  simp only [transport4_26 h]
  change orbit σ v 26 = ((orbit σ v 26) + 0)
  abel

private theorem image_action4_14 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 14) = ((actionIndices 4 14).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 28) = _
  simp only [transport4_28 h]
  change orbit σ v 28 = ((orbit σ v 28) + 0)
  abel

private theorem image_action4_15 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 15) = ((actionIndices 4 15).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 29) = _
  simp only [transport4_29 h]
  change orbit σ v 29 = ((orbit σ v 29) + 0)
  abel

private theorem image_action4_16 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 16) = ((actionIndices 4 16).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 43) = _
  simp only [transport4_43 h]
  change orbit σ v 45 = ((orbit σ v 43) + ((orbit σ v 44) + 0))
  calc
    _ = (orbit σ v 43 + orbit σ v 44 + orbit σ v 45) + (((orbit σ v 43) + ((orbit σ v 44) + 0))) := by
      abel_nf
      simp [binary_two_zsmul]
    _ = _ := by rw [triangle49 h]; simp

private theorem image_action4_17 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 17) = ((actionIndices 4 17).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 44) = _
  simp only [transport4_44 h]
  change orbit σ v 44 = ((orbit σ v 44) + 0)
  abel

private theorem image_action4_18 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 18) = ((actionIndices 4 18).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 46) = _
  simp only [transport4_46 h]
  change orbit σ v 46 = ((orbit σ v 46) + 0)
  abel

private theorem image_action4_19 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 19) = ((actionIndices 4 19).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 47) = _
  simp only [transport4_47 h]
  change orbit σ v 47 = ((orbit σ v 47) + 0)
  abel

private theorem image_action4_20 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 20) = ((actionIndices 4 20).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 51 + orbit σ v 3 + orbit σ v 43) = _
  simp only [map_add, transport4_51 h, transport4_3 h, transport4_43 h]
  change orbit σ v 52 + orbit σ v 3 + orbit σ v 45 = ((orbit σ v 0) + ((orbit σ v 51 + orbit σ v 3 + orbit σ v 43) + 0))
  calc
    _ = (orbit σ v 0 + orbit σ v 44 + orbit σ v 48) + (orbit σ v 43 + orbit σ v 44 + orbit σ v 45) + (orbit σ v 48 + orbit σ v 51 + orbit σ v 52) + (((orbit σ v 0) + ((orbit σ v 51 + orbit σ v 3 + orbit σ v 43) + 0))) := by
      abel_nf
      simp [binary_two_zsmul]
    _ = _ := by rw [triangle16 h, triangle49 h, triangle497 h]; simp

private theorem image_action4_21 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 21) = ((actionIndices 4 21).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 56 + orbit σ v 8 + orbit σ v 44) = _
  simp only [map_add, transport4_56 h, transport4_8 h, transport4_44 h]
  change orbit σ v 58 + orbit σ v 13 + orbit σ v 44 = ((orbit σ v 0) + ((orbit σ v 56 + orbit σ v 8 + orbit σ v 44) + 0))
  calc
    _ = (orbit σ v 0 + orbit σ v 3 + orbit σ v 4) + (orbit σ v 3 + orbit σ v 8 + orbit σ v 13) + (orbit σ v 4 + orbit σ v 56 + orbit σ v 58) + (((orbit σ v 0) + ((orbit σ v 56 + orbit σ v 8 + orbit σ v 44) + 0))) := by
      abel_nf
      simp [binary_two_zsmul]
    _ = _ := by rw [triangle5 h, triangle48 h, triangle510 h]; simp

private theorem image_action4_22 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 22) = ((actionIndices 4 22).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 60 + orbit σ v 19 + orbit σ v 46) = _
  simp only [map_add, transport4_60 h, transport4_19 h, transport4_46 h]
  change orbit σ v 60 + orbit σ v 19 + orbit σ v 46 = ((orbit σ v 60 + orbit σ v 19 + orbit σ v 46) + 0)
  abel

private theorem image_action4_23 (h : LocalHighestVector σ {0, 3} v) :
    σ (generator 4) (imageVector σ v 23) = ((actionIndices 4 23).map (imageVector σ v)).sum := by
  change σ (generator 4) (orbit σ v 63 + orbit σ v 29 + orbit σ v 47) = _
  simp only [map_add, transport4_63 h, transport4_29 h, transport4_47 h]
  change orbit σ v 63 + orbit σ v 29 + orbit σ v 47 = ((orbit σ v 63 + orbit σ v 29 + orbit σ v 47) + 0)
  abel

theorem image_action (h : LocalHighestVector σ {0, 3} v) (k : Fin 5) (b : Fin 24) :
    σ (generator k) (imageVector σ v b) = ((actionIndices k b).map (imageVector σ v)).sum := by
  fin_cases k <;> fin_cases b
  · exact image_action0_0 h
  · exact image_action0_1 h
  · exact image_action0_2 h
  · exact image_action0_3 h
  · exact image_action0_4 h
  · exact image_action0_5 h
  · exact image_action0_6 h
  · exact image_action0_7 h
  · exact image_action0_8 h
  · exact image_action0_9 h
  · exact image_action0_10 h
  · exact image_action0_11 h
  · exact image_action0_12 h
  · exact image_action0_13 h
  · exact image_action0_14 h
  · exact image_action0_15 h
  · exact image_action0_16 h
  · exact image_action0_17 h
  · exact image_action0_18 h
  · exact image_action0_19 h
  · exact image_action0_20 h
  · exact image_action0_21 h
  · exact image_action0_22 h
  · exact image_action0_23 h
  · exact image_action1_0 h
  · exact image_action1_1 h
  · exact image_action1_2 h
  · exact image_action1_3 h
  · exact image_action1_4 h
  · exact image_action1_5 h
  · exact image_action1_6 h
  · exact image_action1_7 h
  · exact image_action1_8 h
  · exact image_action1_9 h
  · exact image_action1_10 h
  · exact image_action1_11 h
  · exact image_action1_12 h
  · exact image_action1_13 h
  · exact image_action1_14 h
  · exact image_action1_15 h
  · exact image_action1_16 h
  · exact image_action1_17 h
  · exact image_action1_18 h
  · exact image_action1_19 h
  · exact image_action1_20 h
  · exact image_action1_21 h
  · exact image_action1_22 h
  · exact image_action1_23 h
  · exact image_action2_0 h
  · exact image_action2_1 h
  · exact image_action2_2 h
  · exact image_action2_3 h
  · exact image_action2_4 h
  · exact image_action2_5 h
  · exact image_action2_6 h
  · exact image_action2_7 h
  · exact image_action2_8 h
  · exact image_action2_9 h
  · exact image_action2_10 h
  · exact image_action2_11 h
  · exact image_action2_12 h
  · exact image_action2_13 h
  · exact image_action2_14 h
  · exact image_action2_15 h
  · exact image_action2_16 h
  · exact image_action2_17 h
  · exact image_action2_18 h
  · exact image_action2_19 h
  · exact image_action2_20 h
  · exact image_action2_21 h
  · exact image_action2_22 h
  · exact image_action2_23 h
  · exact image_action3_0 h
  · exact image_action3_1 h
  · exact image_action3_2 h
  · exact image_action3_3 h
  · exact image_action3_4 h
  · exact image_action3_5 h
  · exact image_action3_6 h
  · exact image_action3_7 h
  · exact image_action3_8 h
  · exact image_action3_9 h
  · exact image_action3_10 h
  · exact image_action3_11 h
  · exact image_action3_12 h
  · exact image_action3_13 h
  · exact image_action3_14 h
  · exact image_action3_15 h
  · exact image_action3_16 h
  · exact image_action3_17 h
  · exact image_action3_18 h
  · exact image_action3_19 h
  · exact image_action3_20 h
  · exact image_action3_21 h
  · exact image_action3_22 h
  · exact image_action3_23 h
  · exact image_action4_0 h
  · exact image_action4_1 h
  · exact image_action4_2 h
  · exact image_action4_3 h
  · exact image_action4_4 h
  · exact image_action4_5 h
  · exact image_action4_6 h
  · exact image_action4_7 h
  · exact image_action4_8 h
  · exact image_action4_9 h
  · exact image_action4_10 h
  · exact image_action4_11 h
  · exact image_action4_12 h
  · exact image_action4_13 h
  · exact image_action4_14 h
  · exact image_action4_15 h
  · exact image_action4_16 h
  · exact image_action4_17 h
  · exact image_action4_18 h
  · exact image_action4_19 h
  · exact image_action4_20 h
  · exact image_action4_21 h
  · exact image_action4_22 h
  · exact image_action4_23 h
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Cyclic
