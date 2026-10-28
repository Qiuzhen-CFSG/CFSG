module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.NormalForms

/-!
# Membership and separation witnesses for the existing Hall--Janko normal forms

The thirteen strong generators are words in the original ATLAS pair. Each
transversal is a word in its own alphabet, and these alphabets are contained
in the first. The later transversals fix the earlier base points; evaluation
at each new base point distinguishes the representatives. These checks are
the membership and uniqueness inputs used in `Order.lean`.

Source: retained ATLAS J2G1-p100B0 data and SecondOrbits/source/witnesses.json.
The additional signed words and reproduction script are in FirstParabolic/source.
Every asserted finite identity is checked by Lean's kernel.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.OrderData
open Theory.GroupTheory GeneratorPair GeneratorPair.SecondOrbitCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

def strongWord (i : Fin 13) : List (Fin 3) :=
  match i.val with
  | 0 => [0]
  | 1 => [1]
  | 2 => [2]
  | 3 => [0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1]
  | 4 => [2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0]
  | 5 => [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1]
  | 6 => [2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0]
  | 7 => [2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0]
  | 8 => [0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1]
  | 9 => [1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2]
  | 10 => [1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2]
  | 11 => [0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2]
  | _ => [1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0]

theorem strongWord_check : ∀ i x,
    evalWord ![tableA, tableB, tableB⁻¹] (strongWord i) x = gen0Map i x := by
  apply allFin
  decide +kernel

theorem rep0_eq_word (i : Fin 100) :
    rep0 i = evalWord gen0 (repWord0 i) := by
  have h : ∀ j x, rep0Map j x = evalWord gen0 (repWord0 j) x := by
    apply allFin
    decide +kernel
  exact Equiv.ext (h i)

def decode0 (x : Fin 100) : Fin 100 :=
  match x.val with
  | 0 => 0
  | 83 => 1
  | 21 => 2
  | 79 => 3
  | 26 => 4
  | 59 => 5
  | 61 => 6
  | 4 => 7
  | 68 => 8
  | 20 => 9
  | 84 => 10
  | 33 => 11
  | 51 => 12
  | 78 => 13
  | 36 => 14
  | 80 => 15
  | 5 => 16
  | 71 => 17
  | 7 => 18
  | 63 => 19
  | 18 => 20
  | 65 => 21
  | 46 => 22
  | 62 => 23
  | 50 => 24
  | 11 => 25
  | 82 => 26
  | 9 => 27
  | 60 => 28
  | 53 => 29
  | 87 => 30
  | 81 => 31
  | 17 => 32
  | 55 => 33
  | 48 => 34
  | 32 => 35
  | 29 => 36
  | 44 => 37
  | 92 => 38
  | 10 => 39
  | 66 => 40
  | 95 => 41
  | 16 => 42
  | 38 => 43
  | 45 => 44
  | 88 => 45
  | 85 => 46
  | 13 => 47
  | 54 => 48
  | 99 => 49
  | 23 => 50
  | 91 => 51
  | 52 => 52
  | 69 => 53
  | 74 => 54
  | 73 => 55
  | 40 => 56
  | 12 => 57
  | 70 => 58
  | 76 => 59
  | 3 => 60
  | 64 => 61
  | 49 => 62
  | 86 => 63
  | 30 => 64
  | 41 => 65
  | 8 => 66
  | 14 => 67
  | 39 => 68
  | 28 => 69
  | 56 => 70
  | 22 => 71
  | 27 => 72
  | 57 => 73
  | 24 => 74
  | 94 => 75
  | 25 => 76
  | 43 => 77
  | 96 => 78
  | 89 => 79
  | 42 => 80
  | 35 => 81
  | 98 => 82
  | 77 => 83
  | 1 => 84
  | 58 => 85
  | 93 => 86
  | 75 => 87
  | 2 => 88
  | 34 => 89
  | 67 => 90
  | 31 => 91
  | 72 => 92
  | 90 => 93
  | 37 => 94
  | 15 => 95
  | 6 => 96
  | 97 => 97
  | 19 => 98
  | 47 => 99
  | _ => 0

theorem decode0_spec : ∀ i, decode0 (rep0 i 0) = i := by
  apply allFin
  decide +kernel

def gen1Index (i : Fin 10) : Fin 13 :=
  match i.val with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 9
  | 7 => 10
  | 8 => 11
  | _ => 12

theorem gen1_eq_gen0 (i : Fin 10) :
    gen1 i = gen0 (gen1Index i) := by
  have h : ∀ j x, gen1Map j x = gen0Map (gen1Index j) x := by
    apply allFin
    decide +kernel
  exact Equiv.ext (h i)

theorem rep1_eq_word (i : Fin 63) :
    rep1 i = evalWord gen1 (repWord1 i) := by
  have h : ∀ j x, rep1Map j x = evalWord gen1 (repWord1 j) x := by
    apply allFin
    decide +kernel
  exact Equiv.ext (h i)

def decode1 (x : Fin 100) : Fin 63 :=
  match x.val with
  | 1 => 0
  | 99 => 1
  | 28 => 2
  | 39 => 3
  | 49 => 4
  | 96 => 5
  | 17 => 6
  | 98 => 7
  | 29 => 8
  | 93 => 9
  | 56 => 10
  | 9 => 11
  | 47 => 12
  | 89 => 13
  | 76 => 14
  | 69 => 15
  | 19 => 16
  | 35 => 17
  | 23 => 18
  | 64 => 19
  | 85 => 20
  | 97 => 21
  | 31 => 22
  | 3 => 23
  | 94 => 24
  | 43 => 25
  | 40 => 26
  | 42 => 27
  | 95 => 28
  | 45 => 29
  | 81 => 30
  | 41 => 31
  | 75 => 32
  | 34 => 33
  | 22 => 34
  | 32 => 35
  | 2 => 36
  | 13 => 37
  | 27 => 38
  | 57 => 39
  | 24 => 40
  | 73 => 41
  | 25 => 42
  | 14 => 43
  | 86 => 44
  | 63 => 45
  | 37 => 46
  | 58 => 47
  | 70 => 48
  | 74 => 49
  | 90 => 50
  | 8 => 51
  | 15 => 52
  | 30 => 53
  | 62 => 54
  | 77 => 55
  | 72 => 56
  | 67 => 57
  | 88 => 58
  | 6 => 59
  | 66 => 60
  | 12 => 61
  | 82 => 62
  | _ => 0

theorem decode1_spec : ∀ i, decode1 (rep1 i 1) = i := by
  apply allFin
  decide +kernel

theorem rep1_fix0 : ∀ i, rep1 i 0 = 0 := by
  apply allFin
  decide +kernel

def gen2Index (i : Fin 6) : Fin 13 :=
  match i.val with
  | 0 => 7
  | 1 => 8
  | 2 => 9
  | 3 => 10
  | 4 => 11
  | _ => 12

theorem gen2_eq_gen0 (i : Fin 6) :
    gen2 i = gen0 (gen2Index i) := by
  have h : ∀ j x, gen2Map j x = gen0Map (gen2Index j) x := by
    apply allFin
    decide +kernel
  exact Equiv.ext (h i)

theorem rep2_eq_word (i : Fin 24) :
    rep2 i = evalWord gen2 (repWord2 i) := by
  have h : ∀ j x, rep2Map j x = evalWord gen2 (repWord2 j) x := by
    apply allFin
    decide +kernel
  exact Equiv.ext (h i)

def decode2 (x : Fin 100) : Fin 24 :=
  match x.val with
  | 2 => 0
  | 56 => 1
  | 97 => 2
  | 95 => 3
  | 19 => 4
  | 32 => 5
  | 41 => 6
  | 3 => 7
  | 76 => 8
  | 23 => 9
  | 49 => 10
  | 74 => 11
  | 63 => 12
  | 30 => 13
  | 90 => 14
  | 39 => 15
  | 35 => 16
  | 69 => 17
  | 85 => 18
  | 6 => 19
  | 15 => 20
  | 64 => 21
  | 37 => 22
  | 31 => 23
  | _ => 0

theorem decode2_spec : ∀ i, decode2 (rep2 i 2) = i := by
  apply allFin
  decide +kernel

theorem rep2_fix0 : ∀ i, rep2 i 0 = 0 := by
  apply allFin
  decide +kernel

theorem rep2_fix1 : ∀ i, rep2 i 1 = 1 := by
  apply allFin
  decide +kernel

def gen3Index (i : Fin 2) : Fin 13 :=
  match i.val with
  | 0 => 11
  | _ => 12

theorem gen3_eq_gen0 (i : Fin 2) :
    gen3 i = gen0 (gen3Index i) := by
  have h : ∀ j x, gen3Map j x = gen0Map (gen3Index j) x := by
    apply allFin
    decide +kernel
  exact Equiv.ext (h i)

theorem rep3_eq_word (i : Fin 4) :
    rep3 i = evalWord gen3 (repWord3 i) := by
  have h : ∀ j x, rep3Map j x = evalWord gen3 (repWord3 j) x := by
    apply allFin
    decide +kernel
  exact Equiv.ext (h i)

def decode3 (x : Fin 100) : Fin 4 :=
  match x.val with
  | 3 => 0
  | 56 => 1
  | 6 => 2
  | 41 => 3
  | _ => 0

theorem decode3_spec : ∀ i, decode3 (rep3 i 3) = i := by
  apply allFin
  decide +kernel

theorem rep3_fix0 : ∀ i, rep3 i 0 = 0 := by
  apply allFin
  decide +kernel

theorem rep3_fix1 : ∀ i, rep3 i 1 = 1 := by
  apply allFin
  decide +kernel

theorem rep3_fix2 : ∀ i, rep3 i 2 = 2 := by
  apply allFin
  decide +kernel


end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.OrderData
