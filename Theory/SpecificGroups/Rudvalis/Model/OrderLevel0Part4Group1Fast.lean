module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Checks0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Checks1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Checks2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Checks3
import Mathlib.Tactic.FinCases
/-!
# Compressed factor evaluation for Rudvalis part 4, group 1

Repeated adjacent subwords of the fixed level-1 factor words are named and
represented by small lookup tables. Each table is checked against the
composition of two previously certified tables. Word expansion then transfers
checks on compressed factors to the original permutation identities.

Source: the ATLAS witnesses in `OrderChainData` and `OrderLevel0Data`.
The tables and compression are untrusted witnesses; Lean checks all equations.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Group1Fast
open Theory.GroupTheory
set_option maxRecDepth 30000
set_option Elab.async false

private theorem map0_eq (x : Fin 4060) :
    map0 x.val = (evalWord L1Gen word0 x).val := by
  have hm : map0 x.val = (Part6Tables.gen1 0 x).val := by rfl
  rw [hm]
  simpa only [word0, evalWord, mul_one] using
    congrArg Fin.val (Part6Tables.gen1_eq 0 x)


private theorem map1_eq (x : Fin 4060) :
    map1 x.val = (evalWord L1Gen word1 x).val := by
  have hm : map1 x.val = (Part6Tables.gen1 1 x).val := by rfl
  rw [hm]
  simpa only [word1, evalWord, mul_one] using
    congrArg Fin.val (Part6Tables.gen1_eq 1 x)


private theorem map2_eq (x : Fin 4060) :
    map2 x.val = (evalWord L1Gen word2 x).val := by
  have hm : map2 x.val = (Part6Tables.gen1 2 x).val := by rfl
  rw [hm]
  simpa only [word2, evalWord, mul_one] using
    congrArg Fin.val (Part6Tables.gen1_eq 2 x)


private theorem map3_eq (x : Fin 4060) :
    map3 x.val = (evalWord L1Gen word3 x).val := by
  have hm : map3 x.val = (Part6Tables.gen1 3 x).val := by rfl
  rw [hm]
  simpa only [word3, evalWord, mul_one] using
    congrArg Fin.val (Part6Tables.gen1_eq 3 x)


private theorem map4_eq (x : Fin 4060) :
    map4 x.val = (evalWord L1Gen word4 x).val := by
  have h := allFin _ check4 x
  rw [map2_eq, map1_eq] at h
  simpa only [word4, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map5_eq (x : Fin 4060) :
    map5 x.val = (evalWord L1Gen word5 x).val := by
  have h := allFin _ check5 x
  rw [map0_eq, map3_eq] at h
  simpa only [word5, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map6_eq (x : Fin 4060) :
    map6 x.val = (evalWord L1Gen word6 x).val := by
  have h := allFin _ check6 x
  rw [map2_eq, map3_eq] at h
  simpa only [word6, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map7_eq (x : Fin 4060) :
    map7 x.val = (evalWord L1Gen word7 x).val := by
  have h := allFin _ check7 x
  rw [map0_eq, map1_eq] at h
  simpa only [word7, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map8_eq (x : Fin 4060) :
    map8 x.val = (evalWord L1Gen word8 x).val := by
  have h := allFin _ check8 x
  rw [map4_eq, map4_eq] at h
  simpa only [word8, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map9_eq (x : Fin 4060) :
    map9 x.val = (evalWord L1Gen word9 x).val := by
  have h := allFin _ check9 x
  rw [map8_eq, map6_eq] at h
  simpa only [word9, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map10_eq (x : Fin 4060) :
    map10 x.val = (evalWord L1Gen word10 x).val := by
  have h := allFin _ check10 x
  rw [map9_eq, map6_eq] at h
  simpa only [word10, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map11_eq (x : Fin 4060) :
    map11 x.val = (evalWord L1Gen word11 x).val := by
  have h := allFin _ check11 x
  rw [map7_eq, map5_eq] at h
  simpa only [word11, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map12_eq (x : Fin 4060) :
    map12 x.val = (evalWord L1Gen word12 x).val := by
  have h := allFin _ check12 x
  rw [map11_eq, map5_eq] at h
  simpa only [word12, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map13_eq (x : Fin 4060) :
    map13 x.val = (evalWord L1Gen word13 x).val := by
  have h := allFin _ check13 x
  rw [map2_eq, map10_eq] at h
  simpa only [word13, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map14_eq (x : Fin 4060) :
    map14 x.val = (evalWord L1Gen word14 x).val := by
  have h := allFin _ check14 x
  rw [map12_eq, map7_eq] at h
  simpa only [word14, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map15_eq (x : Fin 4060) :
    map15 x.val = (evalWord L1Gen word15 x).val := by
  have h := allFin _ check15 x
  rw [map6_eq, map3_eq] at h
  simpa only [word15, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map16_eq (x : Fin 4060) :
    map16 x.val = (evalWord L1Gen word16 x).val := by
  have h := allFin _ check16 x
  rw [map0_eq, map5_eq] at h
  simpa only [word16, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map17_eq (x : Fin 4060) :
    map17 x.val = (evalWord L1Gen word17 x).val := by
  have h := allFin _ check17 x
  rw [map5_eq, map8_eq] at h
  simpa only [word17, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map18_eq (x : Fin 4060) :
    map18 x.val = (evalWord L1Gen word18 x).val := by
  have h := allFin _ check18 x
  rw [map12_eq, map16_eq] at h
  simpa only [word18, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map19_eq (x : Fin 4060) :
    map19 x.val = (evalWord L1Gen word19 x).val := by
  have h := allFin _ check19 x
  rw [map4_eq, map13_eq] at h
  simpa only [word19, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map20_eq (x : Fin 4060) :
    map20 x.val = (evalWord L1Gen word20 x).val := by
  have h := allFin _ check20 x
  rw [map5_eq, map3_eq] at h
  simpa only [word20, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map21_eq (x : Fin 4060) :
    map21 x.val = (evalWord L1Gen word21 x).val := by
  have h := allFin _ check21 x
  rw [map14_eq, map18_eq] at h
  simpa only [word21, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map22_eq (x : Fin 4060) :
    map22 x.val = (evalWord L1Gen word22 x).val := by
  have h := allFin _ check22 x
  rw [map5_eq, map19_eq] at h
  simpa only [word22, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map23_eq (x : Fin 4060) :
    map23 x.val = (evalWord L1Gen word23 x).val := by
  have h := allFin _ check23 x
  rw [map7_eq, map4_eq] at h
  simpa only [word23, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map24_eq (x : Fin 4060) :
    map24 x.val = (evalWord L1Gen word24 x).val := by
  have h := allFin _ check24 x
  rw [map17_eq, map1_eq] at h
  simpa only [word24, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map25_eq (x : Fin 4060) :
    map25 x.val = (evalWord L1Gen word25 x).val := by
  have h := allFin _ check25 x
  rw [map7_eq, map1_eq] at h
  simpa only [word25, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map26_eq (x : Fin 4060) :
    map26 x.val = (evalWord L1Gen word26 x).val := by
  have h := allFin _ check26 x
  rw [map7_eq, map13_eq] at h
  simpa only [word26, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map27_eq (x : Fin 4060) :
    map27 x.val = (evalWord L1Gen word27 x).val := by
  have h := allFin _ check27 x
  rw [map20_eq, map15_eq] at h
  simpa only [word27, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map28_eq (x : Fin 4060) :
    map28 x.val = (evalWord L1Gen word28 x).val := by
  have h := allFin _ check28 x
  rw [map22_eq, map24_eq] at h
  simpa only [word28, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map29_eq (x : Fin 4060) :
    map29 x.val = (evalWord L1Gen word29 x).val := by
  have h := allFin _ check29 x
  rw [map25_eq, map15_eq] at h
  simpa only [word29, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map30_eq (x : Fin 4060) :
    map30 x.val = (evalWord L1Gen word30 x).val := by
  have h := allFin _ check30 x
  rw [map28_eq, map29_eq] at h
  simpa only [word30, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map31_eq (x : Fin 4060) :
    map31 x.val = (evalWord L1Gen word31 x).val := by
  have h := allFin _ check31 x
  rw [map10_eq, map10_eq] at h
  simpa only [word31, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map32_eq (x : Fin 4060) :
    map32 x.val = (evalWord L1Gen word32 x).val := by
  have h := allFin _ check32 x
  rw [map21_eq, map0_eq] at h
  simpa only [word32, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map33_eq (x : Fin 4060) :
    map33 x.val = (evalWord L1Gen word33 x).val := by
  have h := allFin _ check33 x
  rw [map32_eq, map26_eq] at h
  simpa only [word33, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map34_eq (x : Fin 4060) :
    map34 x.val = (evalWord L1Gen word34 x).val := by
  have h := allFin _ check34 x
  rw [map5_eq, map23_eq] at h
  simpa only [word34, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map35_eq (x : Fin 4060) :
    map35 x.val = (evalWord L1Gen word35 x).val := by
  have h := allFin _ check35 x
  rw [map31_eq, map30_eq] at h
  simpa only [word35, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map36_eq (x : Fin 4060) :
    map36 x.val = (evalWord L1Gen word36 x).val := by
  have h := allFin _ check36 x
  rw [map33_eq, map35_eq] at h
  simpa only [word36, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map37_eq (x : Fin 4060) :
    map37 x.val = (evalWord L1Gen word37 x).val := by
  have h := allFin _ check37 x
  rw [map9_eq, map4_eq] at h
  simpa only [word37, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map38_eq (x : Fin 4060) :
    map38 x.val = (evalWord L1Gen word38 x).val := by
  have h := allFin _ check38 x
  rw [map1_eq, map27_eq] at h
  simpa only [word38, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map39_eq (x : Fin 4060) :
    map39 x.val = (evalWord L1Gen word39 x).val := by
  have h := allFin _ check39 x
  rw [map36_eq, map17_eq] at h
  simpa only [word39, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map40_eq (x : Fin 4060) :
    map40 x.val = (evalWord L1Gen word40 x).val := by
  have h := allFin _ check40 x
  rw [map20_eq, map6_eq] at h
  simpa only [word40, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map41_eq (x : Fin 4060) :
    map41 x.val = (evalWord L1Gen word41 x).val := by
  have h := allFin _ check41 x
  rw [map34_eq, map38_eq] at h
  simpa only [word41, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map42_eq (x : Fin 4060) :
    map42 x.val = (evalWord L1Gen word42 x).val := by
  have h := allFin _ check42 x
  rw [map37_eq, map27_eq] at h
  simpa only [word42, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map43_eq (x : Fin 4060) :
    map43 x.val = (evalWord L1Gen word43 x).val := by
  have h := allFin _ check43 x
  rw [map21_eq, map19_eq] at h
  simpa only [word43, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map44_eq (x : Fin 4060) :
    map44 x.val = (evalWord L1Gen word44 x).val := by
  have h := allFin _ check44 x
  rw [map5_eq, map4_eq] at h
  simpa only [word44, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map45_eq (x : Fin 4060) :
    map45 x.val = (evalWord L1Gen word45 x).val := by
  have h := allFin _ check45 x
  rw [map18_eq, map23_eq] at h
  simpa only [word45, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map46_eq (x : Fin 4060) :
    map46 x.val = (evalWord L1Gen word46 x).val := by
  have h := allFin _ check46 x
  rw [map41_eq, map34_eq] at h
  simpa only [word46, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map47_eq (x : Fin 4060) :
    map47 x.val = (evalWord L1Gen word47 x).val := by
  have h := allFin _ check47 x
  rw [map40_eq, map14_eq] at h
  simpa only [word47, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map48_eq (x : Fin 4060) :
    map48 x.val = (evalWord L1Gen word48 x).val := by
  have h := allFin _ check48 x
  rw [map45_eq, map14_eq] at h
  simpa only [word48, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map49_eq (x : Fin 4060) :
    map49 x.val = (evalWord L1Gen word49 x).val := by
  have h := allFin _ check49 x
  rw [map46_eq, map48_eq] at h
  simpa only [word49, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map50_eq (x : Fin 4060) :
    map50 x.val = (evalWord L1Gen word50 x).val := by
  have h := allFin _ check50 x
  rw [map44_eq, map2_eq] at h
  simpa only [word50, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map51_eq (x : Fin 4060) :
    map51 x.val = (evalWord L1Gen word51 x).val := by
  have h := allFin _ check51 x
  rw [map5_eq, map0_eq] at h
  simpa only [word51, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map52_eq (x : Fin 4060) :
    map52 x.val = (evalWord L1Gen word52 x).val := by
  have h := allFin _ check52 x
  rw [map36_eq, map22_eq] at h
  simpa only [word52, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map53_eq (x : Fin 4060) :
    map53 x.val = (evalWord L1Gen word53 x).val := by
  have h := allFin _ check53 x
  rw [map3_eq, map49_eq] at h
  simpa only [word53, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map54_eq (x : Fin 4060) :
    map54 x.val = (evalWord L1Gen word54 x).val := by
  have h := allFin _ check54 x
  rw [map7_eq, map2_eq] at h
  simpa only [word54, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map55_eq (x : Fin 4060) :
    map55 x.val = (evalWord L1Gen word55 x).val := by
  have h := allFin _ check55 x
  rw [map52_eq, map30_eq] at h
  simpa only [word55, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map56_eq (x : Fin 4060) :
    map56 x.val = (evalWord L1Gen word56 x).val := by
  have h := allFin _ check56 x
  rw [map1_eq, map40_eq] at h
  simpa only [word56, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map57_eq (x : Fin 4060) :
    map57 x.val = (evalWord L1Gen word57 x).val := by
  have h := allFin _ check57 x
  rw [map43_eq, map10_eq] at h
  simpa only [word57, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map58_eq (x : Fin 4060) :
    map58 x.val = (evalWord L1Gen word58 x).val := by
  have h := allFin _ check58 x
  rw [map37_eq, map47_eq] at h
  simpa only [word58, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map59_eq (x : Fin 4060) :
    map59 x.val = (evalWord L1Gen word59 x).val := by
  have h := allFin _ check59 x
  rw [map2_eq, map19_eq] at h
  simpa only [word59, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map60_eq (x : Fin 4060) :
    map60 x.val = (evalWord L1Gen word60 x).val := by
  have h := allFin _ check60 x
  rw [map39_eq, map39_eq] at h
  simpa only [word60, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map61_eq (x : Fin 4060) :
    map61 x.val = (evalWord L1Gen word61 x).val := by
  have h := allFin _ check61 x
  rw [map1_eq, map4_eq] at h
  simpa only [word61, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map62_eq (x : Fin 4060) :
    map62 x.val = (evalWord L1Gen word62 x).val := by
  have h := allFin _ check62 x
  rw [map53_eq, map21_eq] at h
  simpa only [word62, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map63_eq (x : Fin 4060) :
    map63 x.val = (evalWord L1Gen word63 x).val := by
  have h := allFin _ check63 x
  rw [map7_eq, map0_eq] at h
  simpa only [word63, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map64_eq (x : Fin 4060) :
    map64 x.val = (evalWord L1Gen word64 x).val := by
  have h := allFin _ check64 x
  rw [map5_eq, map2_eq] at h
  simpa only [word64, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map65_eq (x : Fin 4060) :
    map65 x.val = (evalWord L1Gen word65 x).val := by
  have h := allFin _ check65 x
  rw [map17_eq, map14_eq] at h
  simpa only [word65, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map66_eq (x : Fin 4060) :
    map66 x.val = (evalWord L1Gen word66 x).val := by
  have h := allFin _ check66 x
  rw [map24_eq, map27_eq] at h
  simpa only [word66, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map67_eq (x : Fin 4060) :
    map67 x.val = (evalWord L1Gen word67 x).val := by
  have h := allFin _ check67 x
  rw [map21_eq, map26_eq] at h
  simpa only [word67, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map68_eq (x : Fin 4060) :
    map68 x.val = (evalWord L1Gen word68 x).val := by
  have h := allFin _ check68 x
  rw [map5_eq, map26_eq] at h
  simpa only [word68, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map69_eq (x : Fin 4060) :
    map69 x.val = (evalWord L1Gen word69 x).val := by
  have h := allFin _ check69 x
  rw [map62_eq, map59_eq] at h
  simpa only [word69, evalWord_append, Equiv.Perm.mul_apply] using h


private theorem map70_eq (x : Fin 4060) :
    map70 x.val = (evalWord L1Gen word70 x).val := by
  have h := allFin _ check70 x
  rw [map39_eq, map33_eq] at h
  simpa only [word70, evalWord_append, Equiv.Perm.mul_apply] using h

public theorem gen_eq (i : Fin 71) (x : Fin 4060) :
    gen i x.val = (evalWord L1Gen (word i) x).val := by
  fin_cases i
  · exact map0_eq x
  · exact map1_eq x
  · exact map2_eq x
  · exact map3_eq x
  · exact map4_eq x
  · exact map5_eq x
  · exact map6_eq x
  · exact map7_eq x
  · exact map8_eq x
  · exact map9_eq x
  · exact map10_eq x
  · exact map11_eq x
  · exact map12_eq x
  · exact map13_eq x
  · exact map14_eq x
  · exact map15_eq x
  · exact map16_eq x
  · exact map17_eq x
  · exact map18_eq x
  · exact map19_eq x
  · exact map20_eq x
  · exact map21_eq x
  · exact map22_eq x
  · exact map23_eq x
  · exact map24_eq x
  · exact map25_eq x
  · exact map26_eq x
  · exact map27_eq x
  · exact map28_eq x
  · exact map29_eq x
  · exact map30_eq x
  · exact map31_eq x
  · exact map32_eq x
  · exact map33_eq x
  · exact map34_eq x
  · exact map35_eq x
  · exact map36_eq x
  · exact map37_eq x
  · exact map38_eq x
  · exact map39_eq x
  · exact map40_eq x
  · exact map41_eq x
  · exact map42_eq x
  · exact map43_eq x
  · exact map44_eq x
  · exact map45_eq x
  · exact map46_eq x
  · exact map47_eq x
  · exact map48_eq x
  · exact map49_eq x
  · exact map50_eq x
  · exact map51_eq x
  · exact map52_eq x
  · exact map53_eq x
  · exact map54_eq x
  · exact map55_eq x
  · exact map56_eq x
  · exact map57_eq x
  · exact map58_eq x
  · exact map59_eq x
  · exact map60_eq x
  · exact map61_eq x
  · exact map62_eq x
  · exact map63_eq x
  · exact map64_eq x
  · exact map65_eq x
  · exact map66_eq x
  · exact map67_eq x
  · exact map68_eq x
  · exact map69_eq x
  · exact map70_eq x

@[expose] public def eval {n : Nat} (g : Fin n → Nat → Nat) : List (Fin n) → Nat → Nat
  | [], x => x
  | i :: w, x => Part6Nat.force (g i) (eval g w x)

private theorem force_eq (f : Nat → Nat) (x : Nat) : Part6Nat.force f x = f x := by
  cases x <;> rfl

private theorem eval_eq {n : Nat} (g : Fin n → Nat → Nat)
    (G : Fin n → Equiv.Perm (Fin 4060))
    (h : ∀ i (x : Fin 4060), g i x.val = (G i x).val)
    (w : List (Fin n)) (x : Fin 4060) :
    eval g w x.val = (evalWord G w x).val := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simpa only [eval, force_eq, ih, evalWord, Equiv.Perm.mul_apply] using h i (evalWord G w x)

private theorem gen0_eq (i : Fin 4) (x : Fin 4060) :
    Part6Nat.gen0 i x.val = (L0Gen i x).val := by
  have h := congrArg Fin.val (Part6Tables.gen0_eq i x)
  fin_cases i <;> exact h

private theorem expanded_eval (w : List (Fin 71)) :
    evalWord (fun i => evalWord L1Gen (word i)) w =
      evalWord L1Gen (w.flatMap word) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.flatMap_cons, evalWord_append, evalWord, ih]

@[expose] public def point (i : Fin 2) (r : Fin 4060) (w : List (Fin 71)) (x : Nat) : Bool :=
  decide (Part6Nat.gen0 (i.castLE (by decide)) (eval Part6Nat.gen0 (L0RepWord r) x) =
    eval Part6Nat.gen0 (L0RepWord (L0Act (i.castLE (by decide)) r)) (eval gen w x))

@[expose] public def check (i : Fin 2) (r : Fin 4060) (w : List (Fin 71)) : Bool :=
  checkFin (fun x : Fin 4060 => point i r w x.val)

public theorem ofCheck (i : Fin 2) (r : Fin 4060) (w : List (Fin 71))
    (hw : w.flatMap word = L0Factor (i.castLE (by decide)) r)
    (h : check i r w = true) : stepCheck i r := by
  right
  apply (checkFin_spec _).mpr
  intro x
  have hx := (checkFin_spec _).mp h x
  simp only [point, decide_eq_true_eq] at hx
  have hgen := eval_eq gen (fun i => evalWord L1Gen (word i)) gen_eq w x
  rw [expanded_eval, hw] at hgen
  rw [hgen, eval_eq _ _ gen0_eq, eval_eq _ _ gen0_eq, gen0_eq] at hx
  apply decide_eq_true
  apply Fin.ext
  simpa only [Equiv.Perm.mul_apply, L0Rep] using hx

end Rudvalis.OrderCertificate.ForwardReduction.Part4Group1Fast
