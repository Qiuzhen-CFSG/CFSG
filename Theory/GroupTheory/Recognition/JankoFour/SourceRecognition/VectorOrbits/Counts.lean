module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits.Native

/-!
# Exact sizes of the two singular vector orbits

The checked native orbit labels have fibers of sizes 693 and 1386. Each
32-vector row is counted by kernel reduction; a separate small certificate
adds the row totals. The generic conversion from subtype cardinality to an
indicator sum avoids reducing the full 4096-element finite-type instance
inside each numerical certificate. These counts feed the literal H/Q
stabilizers in `CoreStabilizers`.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.2), printed p.597, DOI 10.1007/BF01232280. The native
matrix provenance and existing orbit forest are retained unchanged.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits

private def counts : Fin 128 → Nat × Nat := fun i =>
  (![ ![(7,8),(8,8),(3,13),(7,9),(4,12),(2,6),(3,13),(7,9),(4,12),(4,12),(5,11),(3,13),(4,12),(8,16),(7,9),(9,7)], ![(1,15),(7,9),(6,10),(2,6),(5,11),(7,9),(8,8),(8,8),(5,11),(5,11),(6,10),(4,4),(3,13),(3,13),(6,10),(4,12)], ![(8,8),(4,12),(7,9),(5,11),(4,12),(4,4),(5,11),(7,9),(6,10),(4,12),(5,11),(5,11),(8,8),(14,10),(5,11),(5,11)], ![(3,13),(3,13),(6,10),(8,16),(5,11),(5,11),(2,14),(4,12),(3,13),(5,11),(10,6),(6,18),(7,9),(5,11),(4,12),(4,12)], ![(8,8),(8,16),(5,11),(3,13),(6,10),(6,10),(5,11),(3,13),(4,12),(2,6),(5,11),(9,7),(4,12),(6,10),(3,13),(3,13)], ![(7,9),(3,13),(4,12),(6,10),(7,9),(7,9),(6,10),(12,12),(5,11),(7,9),(10,6),(2,14),(3,13),(5,11),(6,10),(6,18)], ![(4,12),(2,6),(3,13),(3,13),(4,12),(6,10),(9,7),(5,11),(4,12),(8,16),(7,9),(5,11),(6,10),(10,6),(3,13),(1,15)], ![(7,9),(5,11),(6,10),(6,10),(5,11),(3,13),(2,14),(10,14),(9,7),(5,11),(8,8),(6,10),(5,11),(5,11),(6,10),(8,16)] ] : Fin 8 → Fin 16 → Nat × Nat)
    ⟨i.val / 16, by omega⟩ ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩

set_option Elab.async false

private theorem count000 :
    (∑ j : Fin 32, if (rows000 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows000 j).root = 7 then 1 else 0 : Nat) = 8 := by
  decide +kernel

private theorem count001 :
    (∑ j : Fin 32, if (rows001 j).root = 4 then 1 else 0 : Nat) = 8 ∧
    (∑ j : Fin 32, if (rows001 j).root = 7 then 1 else 0 : Nat) = 8 := by
  decide +kernel

private theorem count002 :
    (∑ j : Fin 32, if (rows002 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows002 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count003 :
    (∑ j : Fin 32, if (rows003 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows003 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count004 :
    (∑ j : Fin 32, if (rows004 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows004 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count005 :
    (∑ j : Fin 32, if (rows005 j).root = 4 then 1 else 0 : Nat) = 2 ∧
    (∑ j : Fin 32, if (rows005 j).root = 7 then 1 else 0 : Nat) = 6 := by
  decide +kernel

private theorem count006 :
    (∑ j : Fin 32, if (rows006 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows006 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count007 :
    (∑ j : Fin 32, if (rows007 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows007 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count008 :
    (∑ j : Fin 32, if (rows008 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows008 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count009 :
    (∑ j : Fin 32, if (rows009 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows009 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count010 :
    (∑ j : Fin 32, if (rows010 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows010 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count011 :
    (∑ j : Fin 32, if (rows011 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows011 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count012 :
    (∑ j : Fin 32, if (rows012 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows012 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count013 :
    (∑ j : Fin 32, if (rows013 j).root = 4 then 1 else 0 : Nat) = 8 ∧
    (∑ j : Fin 32, if (rows013 j).root = 7 then 1 else 0 : Nat) = 16 := by
  decide +kernel

private theorem count014 :
    (∑ j : Fin 32, if (rows014 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows014 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count015 :
    (∑ j : Fin 32, if (rows015 j).root = 4 then 1 else 0 : Nat) = 9 ∧
    (∑ j : Fin 32, if (rows015 j).root = 7 then 1 else 0 : Nat) = 7 := by
  decide +kernel

private theorem count016 :
    (∑ j : Fin 32, if (rows016 j).root = 4 then 1 else 0 : Nat) = 1 ∧
    (∑ j : Fin 32, if (rows016 j).root = 7 then 1 else 0 : Nat) = 15 := by
  decide +kernel

private theorem count017 :
    (∑ j : Fin 32, if (rows017 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows017 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count018 :
    (∑ j : Fin 32, if (rows018 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows018 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count019 :
    (∑ j : Fin 32, if (rows019 j).root = 4 then 1 else 0 : Nat) = 2 ∧
    (∑ j : Fin 32, if (rows019 j).root = 7 then 1 else 0 : Nat) = 6 := by
  decide +kernel

private theorem count020 :
    (∑ j : Fin 32, if (rows020 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows020 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count021 :
    (∑ j : Fin 32, if (rows021 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows021 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count022 :
    (∑ j : Fin 32, if (rows022 j).root = 4 then 1 else 0 : Nat) = 8 ∧
    (∑ j : Fin 32, if (rows022 j).root = 7 then 1 else 0 : Nat) = 8 := by
  decide +kernel

private theorem count023 :
    (∑ j : Fin 32, if (rows023 j).root = 4 then 1 else 0 : Nat) = 8 ∧
    (∑ j : Fin 32, if (rows023 j).root = 7 then 1 else 0 : Nat) = 8 := by
  decide +kernel

private theorem count024 :
    (∑ j : Fin 32, if (rows024 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows024 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count025 :
    (∑ j : Fin 32, if (rows025 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows025 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count026 :
    (∑ j : Fin 32, if (rows026 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows026 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count027 :
    (∑ j : Fin 32, if (rows027 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows027 j).root = 7 then 1 else 0 : Nat) = 4 := by
  decide +kernel

private theorem count028 :
    (∑ j : Fin 32, if (rows028 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows028 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count029 :
    (∑ j : Fin 32, if (rows029 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows029 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count030 :
    (∑ j : Fin 32, if (rows030 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows030 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count031 :
    (∑ j : Fin 32, if (rows031 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows031 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count032 :
    (∑ j : Fin 32, if (rows032 j).root = 4 then 1 else 0 : Nat) = 8 ∧
    (∑ j : Fin 32, if (rows032 j).root = 7 then 1 else 0 : Nat) = 8 := by
  decide +kernel

private theorem count033 :
    (∑ j : Fin 32, if (rows033 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows033 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count034 :
    (∑ j : Fin 32, if (rows034 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows034 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count035 :
    (∑ j : Fin 32, if (rows035 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows035 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count036 :
    (∑ j : Fin 32, if (rows036 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows036 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count037 :
    (∑ j : Fin 32, if (rows037 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows037 j).root = 7 then 1 else 0 : Nat) = 4 := by
  decide +kernel

private theorem count038 :
    (∑ j : Fin 32, if (rows038 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows038 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count039 :
    (∑ j : Fin 32, if (rows039 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows039 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count040 :
    (∑ j : Fin 32, if (rows040 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows040 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count041 :
    (∑ j : Fin 32, if (rows041 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows041 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count042 :
    (∑ j : Fin 32, if (rows042 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows042 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count043 :
    (∑ j : Fin 32, if (rows043 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows043 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count044 :
    (∑ j : Fin 32, if (rows044 j).root = 4 then 1 else 0 : Nat) = 8 ∧
    (∑ j : Fin 32, if (rows044 j).root = 7 then 1 else 0 : Nat) = 8 := by
  decide +kernel

private theorem count045 :
    (∑ j : Fin 32, if (rows045 j).root = 4 then 1 else 0 : Nat) = 14 ∧
    (∑ j : Fin 32, if (rows045 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count046 :
    (∑ j : Fin 32, if (rows046 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows046 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count047 :
    (∑ j : Fin 32, if (rows047 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows047 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count048 :
    (∑ j : Fin 32, if (rows048 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows048 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count049 :
    (∑ j : Fin 32, if (rows049 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows049 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count050 :
    (∑ j : Fin 32, if (rows050 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows050 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count051 :
    (∑ j : Fin 32, if (rows051 j).root = 4 then 1 else 0 : Nat) = 8 ∧
    (∑ j : Fin 32, if (rows051 j).root = 7 then 1 else 0 : Nat) = 16 := by
  decide +kernel

private theorem count052 :
    (∑ j : Fin 32, if (rows052 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows052 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count053 :
    (∑ j : Fin 32, if (rows053 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows053 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count054 :
    (∑ j : Fin 32, if (rows054 j).root = 4 then 1 else 0 : Nat) = 2 ∧
    (∑ j : Fin 32, if (rows054 j).root = 7 then 1 else 0 : Nat) = 14 := by
  decide +kernel

private theorem count055 :
    (∑ j : Fin 32, if (rows055 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows055 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count056 :
    (∑ j : Fin 32, if (rows056 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows056 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count057 :
    (∑ j : Fin 32, if (rows057 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows057 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count058 :
    (∑ j : Fin 32, if (rows058 j).root = 4 then 1 else 0 : Nat) = 10 ∧
    (∑ j : Fin 32, if (rows058 j).root = 7 then 1 else 0 : Nat) = 6 := by
  decide +kernel

private theorem count059 :
    (∑ j : Fin 32, if (rows059 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows059 j).root = 7 then 1 else 0 : Nat) = 18 := by
  decide +kernel

private theorem count060 :
    (∑ j : Fin 32, if (rows060 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows060 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count061 :
    (∑ j : Fin 32, if (rows061 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows061 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count062 :
    (∑ j : Fin 32, if (rows062 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows062 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count063 :
    (∑ j : Fin 32, if (rows063 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows063 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count064 :
    (∑ j : Fin 32, if (rows064 j).root = 4 then 1 else 0 : Nat) = 8 ∧
    (∑ j : Fin 32, if (rows064 j).root = 7 then 1 else 0 : Nat) = 8 := by
  decide +kernel

private theorem count065 :
    (∑ j : Fin 32, if (rows065 j).root = 4 then 1 else 0 : Nat) = 8 ∧
    (∑ j : Fin 32, if (rows065 j).root = 7 then 1 else 0 : Nat) = 16 := by
  decide +kernel

private theorem count066 :
    (∑ j : Fin 32, if (rows066 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows066 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count067 :
    (∑ j : Fin 32, if (rows067 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows067 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count068 :
    (∑ j : Fin 32, if (rows068 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows068 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count069 :
    (∑ j : Fin 32, if (rows069 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows069 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count070 :
    (∑ j : Fin 32, if (rows070 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows070 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count071 :
    (∑ j : Fin 32, if (rows071 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows071 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count072 :
    (∑ j : Fin 32, if (rows072 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows072 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count073 :
    (∑ j : Fin 32, if (rows073 j).root = 4 then 1 else 0 : Nat) = 2 ∧
    (∑ j : Fin 32, if (rows073 j).root = 7 then 1 else 0 : Nat) = 6 := by
  decide +kernel

private theorem count074 :
    (∑ j : Fin 32, if (rows074 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows074 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count075 :
    (∑ j : Fin 32, if (rows075 j).root = 4 then 1 else 0 : Nat) = 9 ∧
    (∑ j : Fin 32, if (rows075 j).root = 7 then 1 else 0 : Nat) = 7 := by
  decide +kernel

private theorem count076 :
    (∑ j : Fin 32, if (rows076 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows076 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count077 :
    (∑ j : Fin 32, if (rows077 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows077 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count078 :
    (∑ j : Fin 32, if (rows078 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows078 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count079 :
    (∑ j : Fin 32, if (rows079 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows079 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count080 :
    (∑ j : Fin 32, if (rows080 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows080 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count081 :
    (∑ j : Fin 32, if (rows081 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows081 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count082 :
    (∑ j : Fin 32, if (rows082 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows082 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count083 :
    (∑ j : Fin 32, if (rows083 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows083 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count084 :
    (∑ j : Fin 32, if (rows084 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows084 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count085 :
    (∑ j : Fin 32, if (rows085 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows085 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count086 :
    (∑ j : Fin 32, if (rows086 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows086 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count087 :
    (∑ j : Fin 32, if (rows087 j).root = 4 then 1 else 0 : Nat) = 12 ∧
    (∑ j : Fin 32, if (rows087 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count088 :
    (∑ j : Fin 32, if (rows088 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows088 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count089 :
    (∑ j : Fin 32, if (rows089 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows089 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count090 :
    (∑ j : Fin 32, if (rows090 j).root = 4 then 1 else 0 : Nat) = 10 ∧
    (∑ j : Fin 32, if (rows090 j).root = 7 then 1 else 0 : Nat) = 6 := by
  decide +kernel

private theorem count091 :
    (∑ j : Fin 32, if (rows091 j).root = 4 then 1 else 0 : Nat) = 2 ∧
    (∑ j : Fin 32, if (rows091 j).root = 7 then 1 else 0 : Nat) = 14 := by
  decide +kernel

private theorem count092 :
    (∑ j : Fin 32, if (rows092 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows092 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count093 :
    (∑ j : Fin 32, if (rows093 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows093 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count094 :
    (∑ j : Fin 32, if (rows094 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows094 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count095 :
    (∑ j : Fin 32, if (rows095 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows095 j).root = 7 then 1 else 0 : Nat) = 18 := by
  decide +kernel

private theorem count096 :
    (∑ j : Fin 32, if (rows096 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows096 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count097 :
    (∑ j : Fin 32, if (rows097 j).root = 4 then 1 else 0 : Nat) = 2 ∧
    (∑ j : Fin 32, if (rows097 j).root = 7 then 1 else 0 : Nat) = 6 := by
  decide +kernel

private theorem count098 :
    (∑ j : Fin 32, if (rows098 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows098 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count099 :
    (∑ j : Fin 32, if (rows099 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows099 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count100 :
    (∑ j : Fin 32, if (rows100 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows100 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count101 :
    (∑ j : Fin 32, if (rows101 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows101 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count102 :
    (∑ j : Fin 32, if (rows102 j).root = 4 then 1 else 0 : Nat) = 9 ∧
    (∑ j : Fin 32, if (rows102 j).root = 7 then 1 else 0 : Nat) = 7 := by
  decide +kernel

private theorem count103 :
    (∑ j : Fin 32, if (rows103 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows103 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count104 :
    (∑ j : Fin 32, if (rows104 j).root = 4 then 1 else 0 : Nat) = 4 ∧
    (∑ j : Fin 32, if (rows104 j).root = 7 then 1 else 0 : Nat) = 12 := by
  decide +kernel

private theorem count105 :
    (∑ j : Fin 32, if (rows105 j).root = 4 then 1 else 0 : Nat) = 8 ∧
    (∑ j : Fin 32, if (rows105 j).root = 7 then 1 else 0 : Nat) = 16 := by
  decide +kernel

private theorem count106 :
    (∑ j : Fin 32, if (rows106 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows106 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count107 :
    (∑ j : Fin 32, if (rows107 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows107 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count108 :
    (∑ j : Fin 32, if (rows108 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows108 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count109 :
    (∑ j : Fin 32, if (rows109 j).root = 4 then 1 else 0 : Nat) = 10 ∧
    (∑ j : Fin 32, if (rows109 j).root = 7 then 1 else 0 : Nat) = 6 := by
  decide +kernel

private theorem count110 :
    (∑ j : Fin 32, if (rows110 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows110 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count111 :
    (∑ j : Fin 32, if (rows111 j).root = 4 then 1 else 0 : Nat) = 1 ∧
    (∑ j : Fin 32, if (rows111 j).root = 7 then 1 else 0 : Nat) = 15 := by
  decide +kernel

private theorem count112 :
    (∑ j : Fin 32, if (rows112 j).root = 4 then 1 else 0 : Nat) = 7 ∧
    (∑ j : Fin 32, if (rows112 j).root = 7 then 1 else 0 : Nat) = 9 := by
  decide +kernel

private theorem count113 :
    (∑ j : Fin 32, if (rows113 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows113 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count114 :
    (∑ j : Fin 32, if (rows114 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows114 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count115 :
    (∑ j : Fin 32, if (rows115 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows115 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count116 :
    (∑ j : Fin 32, if (rows116 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows116 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count117 :
    (∑ j : Fin 32, if (rows117 j).root = 4 then 1 else 0 : Nat) = 3 ∧
    (∑ j : Fin 32, if (rows117 j).root = 7 then 1 else 0 : Nat) = 13 := by
  decide +kernel

private theorem count118 :
    (∑ j : Fin 32, if (rows118 j).root = 4 then 1 else 0 : Nat) = 2 ∧
    (∑ j : Fin 32, if (rows118 j).root = 7 then 1 else 0 : Nat) = 14 := by
  decide +kernel

private theorem count119 :
    (∑ j : Fin 32, if (rows119 j).root = 4 then 1 else 0 : Nat) = 10 ∧
    (∑ j : Fin 32, if (rows119 j).root = 7 then 1 else 0 : Nat) = 14 := by
  decide +kernel

private theorem count120 :
    (∑ j : Fin 32, if (rows120 j).root = 4 then 1 else 0 : Nat) = 9 ∧
    (∑ j : Fin 32, if (rows120 j).root = 7 then 1 else 0 : Nat) = 7 := by
  decide +kernel

private theorem count121 :
    (∑ j : Fin 32, if (rows121 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows121 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count122 :
    (∑ j : Fin 32, if (rows122 j).root = 4 then 1 else 0 : Nat) = 8 ∧
    (∑ j : Fin 32, if (rows122 j).root = 7 then 1 else 0 : Nat) = 8 := by
  decide +kernel

private theorem count123 :
    (∑ j : Fin 32, if (rows123 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows123 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count124 :
    (∑ j : Fin 32, if (rows124 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows124 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count125 :
    (∑ j : Fin 32, if (rows125 j).root = 4 then 1 else 0 : Nat) = 5 ∧
    (∑ j : Fin 32, if (rows125 j).root = 7 then 1 else 0 : Nat) = 11 := by
  decide +kernel

private theorem count126 :
    (∑ j : Fin 32, if (rows126 j).root = 4 then 1 else 0 : Nat) = 6 ∧
    (∑ j : Fin 32, if (rows126 j).root = 7 then 1 else 0 : Nat) = 10 := by
  decide +kernel

private theorem count127 :
    (∑ j : Fin 32, if (rows127 j).root = 4 then 1 else 0 : Nat) = 8 ∧
    (∑ j : Fin 32, if (rows127 j).root = 7 then 1 else 0 : Nat) = 16 := by
  decide +kernel

private theorem forall_blocks (P : Fin 128 → Prop)
    (h000 : P 0)
    (h001 : P 1)
    (h002 : P 2)
    (h003 : P 3)
    (h004 : P 4)
    (h005 : P 5)
    (h006 : P 6)
    (h007 : P 7)
    (h008 : P 8)
    (h009 : P 9)
    (h010 : P 10)
    (h011 : P 11)
    (h012 : P 12)
    (h013 : P 13)
    (h014 : P 14)
    (h015 : P 15)
    (h016 : P 16)
    (h017 : P 17)
    (h018 : P 18)
    (h019 : P 19)
    (h020 : P 20)
    (h021 : P 21)
    (h022 : P 22)
    (h023 : P 23)
    (h024 : P 24)
    (h025 : P 25)
    (h026 : P 26)
    (h027 : P 27)
    (h028 : P 28)
    (h029 : P 29)
    (h030 : P 30)
    (h031 : P 31)
    (h032 : P 32)
    (h033 : P 33)
    (h034 : P 34)
    (h035 : P 35)
    (h036 : P 36)
    (h037 : P 37)
    (h038 : P 38)
    (h039 : P 39)
    (h040 : P 40)
    (h041 : P 41)
    (h042 : P 42)
    (h043 : P 43)
    (h044 : P 44)
    (h045 : P 45)
    (h046 : P 46)
    (h047 : P 47)
    (h048 : P 48)
    (h049 : P 49)
    (h050 : P 50)
    (h051 : P 51)
    (h052 : P 52)
    (h053 : P 53)
    (h054 : P 54)
    (h055 : P 55)
    (h056 : P 56)
    (h057 : P 57)
    (h058 : P 58)
    (h059 : P 59)
    (h060 : P 60)
    (h061 : P 61)
    (h062 : P 62)
    (h063 : P 63)
    (h064 : P 64)
    (h065 : P 65)
    (h066 : P 66)
    (h067 : P 67)
    (h068 : P 68)
    (h069 : P 69)
    (h070 : P 70)
    (h071 : P 71)
    (h072 : P 72)
    (h073 : P 73)
    (h074 : P 74)
    (h075 : P 75)
    (h076 : P 76)
    (h077 : P 77)
    (h078 : P 78)
    (h079 : P 79)
    (h080 : P 80)
    (h081 : P 81)
    (h082 : P 82)
    (h083 : P 83)
    (h084 : P 84)
    (h085 : P 85)
    (h086 : P 86)
    (h087 : P 87)
    (h088 : P 88)
    (h089 : P 89)
    (h090 : P 90)
    (h091 : P 91)
    (h092 : P 92)
    (h093 : P 93)
    (h094 : P 94)
    (h095 : P 95)
    (h096 : P 96)
    (h097 : P 97)
    (h098 : P 98)
    (h099 : P 99)
    (h100 : P 100)
    (h101 : P 101)
    (h102 : P 102)
    (h103 : P 103)
    (h104 : P 104)
    (h105 : P 105)
    (h106 : P 106)
    (h107 : P 107)
    (h108 : P 108)
    (h109 : P 109)
    (h110 : P 110)
    (h111 : P 111)
    (h112 : P 112)
    (h113 : P 113)
    (h114 : P 114)
    (h115 : P 115)
    (h116 : P 116)
    (h117 : P 117)
    (h118 : P 118)
    (h119 : P 119)
    (h120 : P 120)
    (h121 : P 121)
    (h122 : P 122)
    (h123 : P 123)
    (h124 : P 124)
    (h125 : P 125)
    (h126 : P 126)
    (h127 : P 127)
    : ∀ i, P i := by
  intro i
  fin_cases i
  · exact h000
  · exact h001
  · exact h002
  · exact h003
  · exact h004
  · exact h005
  · exact h006
  · exact h007
  · exact h008
  · exact h009
  · exact h010
  · exact h011
  · exact h012
  · exact h013
  · exact h014
  · exact h015
  · exact h016
  · exact h017
  · exact h018
  · exact h019
  · exact h020
  · exact h021
  · exact h022
  · exact h023
  · exact h024
  · exact h025
  · exact h026
  · exact h027
  · exact h028
  · exact h029
  · exact h030
  · exact h031
  · exact h032
  · exact h033
  · exact h034
  · exact h035
  · exact h036
  · exact h037
  · exact h038
  · exact h039
  · exact h040
  · exact h041
  · exact h042
  · exact h043
  · exact h044
  · exact h045
  · exact h046
  · exact h047
  · exact h048
  · exact h049
  · exact h050
  · exact h051
  · exact h052
  · exact h053
  · exact h054
  · exact h055
  · exact h056
  · exact h057
  · exact h058
  · exact h059
  · exact h060
  · exact h061
  · exact h062
  · exact h063
  · exact h064
  · exact h065
  · exact h066
  · exact h067
  · exact h068
  · exact h069
  · exact h070
  · exact h071
  · exact h072
  · exact h073
  · exact h074
  · exact h075
  · exact h076
  · exact h077
  · exact h078
  · exact h079
  · exact h080
  · exact h081
  · exact h082
  · exact h083
  · exact h084
  · exact h085
  · exact h086
  · exact h087
  · exact h088
  · exact h089
  · exact h090
  · exact h091
  · exact h092
  · exact h093
  · exact h094
  · exact h095
  · exact h096
  · exact h097
  · exact h098
  · exact h099
  · exact h100
  · exact h101
  · exact h102
  · exact h103
  · exact h104
  · exact h105
  · exact h106
  · exact h107
  · exact h108
  · exact h109
  · exact h110
  · exact h111
  · exact h112
  · exact h113
  · exact h114
  · exact h115
  · exact h116
  · exact h117
  · exact h118
  · exact h119
  · exact h120
  · exact h121
  · exact h122
  · exact h123
  · exact h124
  · exact h125
  · exact h126
  · exact h127

private theorem counts_eq (i : Fin 128) :
    (∑ j : Fin 32, if (treeRows i j).root = 4 then 1 else 0 : Nat) = (counts i).1 ∧
    (∑ j : Fin 32, if (treeRows i j).root = 7 then 1 else 0 : Nat) = (counts i).2 := by
  exact forall_blocks (fun i =>
    (∑ j : Fin 32, if (treeRows i j).root = 4 then 1 else 0 : Nat) = (counts i).1 ∧
    (∑ j : Fin 32, if (treeRows i j).root = 7 then 1 else 0 : Nat) = (counts i).2)
    count000 count001 count002 count003 count004 count005 count006 count007 count008 count009 count010 count011 count012 count013 count014 count015 count016 count017 count018 count019 count020 count021 count022 count023 count024 count025 count026 count027 count028 count029 count030 count031 count032 count033 count034 count035 count036 count037 count038 count039 count040 count041 count042 count043 count044 count045 count046 count047 count048 count049 count050 count051 count052 count053 count054 count055 count056 count057 count058 count059 count060 count061 count062 count063 count064 count065 count066 count067 count068 count069 count070 count071 count072 count073 count074 count075 count076 count077 count078 count079 count080 count081 count082 count083 count084 count085 count086 count087 count088 count089 count090 count091 count092 count093 count094 count095 count096 count097 count098 count099 count100 count101 count102 count103 count104 count105 count106 count107 count108 count109 count110 count111 count112 count113 count114 count115 count116 count117 count118 count119 count120 count121 count122 count123 count124 count125 count126 count127 i

private theorem treeRow_product (i : Fin 128) (j : Fin 32) :
    treeRow (finProdFinEquiv (i,j)) = treeRows i j := by
  unfold treeRow
  congr 1 <;> apply Fin.ext
  · simp [finProdFinEquiv]
    omega
  · simp [finProdFinEquiv]

private theorem sum_by_blocks (r : Word) :
    (∑ n : Word, if (treeRow n).root = r then 1 else 0 : Nat) =
      ∑ i : Fin 128, ∑ j : Fin 32, if (treeRows i j).root = r then 1 else 0 := by
  rw [← (finProdFinEquiv : Fin 128 × Fin 32 ≃ Word).sum_comp, Fintype.sum_prod_type]
  simp only [treeRow_product]

private theorem fiber_card_eq_sum {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P] :
    Nat.card {a : A // P a} = ∑ a : A, if P a then 1 else 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (Finset.sum_boole (R := Nat) P Finset.univ).symm

private theorem counts_sum :
    (∑ i : Fin 128, (counts i).1) = 693 ∧
    (∑ i : Fin 128, (counts i).2) = 1386 := by
  decide +kernel

theorem word_fiber_four_card : Nat.card {n : Word // (treeRow n).root = 4} = 693 := by
  rw [fiber_card_eq_sum, sum_by_blocks]
  simp only [(counts_eq _).1]
  exact counts_sum.1

theorem word_fiber_seven_card : Nat.card {n : Word // (treeRow n).root = 7} = 1386 := by
  rw [fiber_card_eq_sum, sum_by_blocks]
  simp only [(counts_eq _).2]
  exact counts_sum.2

theorem label_four_card :
    Nat.card {v : Sporadic.Mathieu.M22TripleCover.BinarySpace // label v = 4} = 693 := by
  rw [← Nat.card_congr (decodeEquiv.subtypeEquiv (p := fun n => (treeRow n).root = 4)
    (q := fun v => label v = 4) (fun n => by rw [show decodeEquiv n = decode n from rfl, label_decode]))]
  exact word_fiber_four_card

theorem label_seven_card :
    Nat.card {v : Sporadic.Mathieu.M22TripleCover.BinarySpace // label v = 7} = 1386 := by
  rw [← Nat.card_congr (decodeEquiv.subtypeEquiv (p := fun n => (treeRow n).root = 7)
    (q := fun v => label v = 7) (fun n => by rw [show decodeEquiv n = decode n from rfl, label_decode]))]
  exact word_fiber_seven_card

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits
end
