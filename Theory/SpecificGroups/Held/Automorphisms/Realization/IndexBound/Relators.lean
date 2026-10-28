module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.RotatedRelators
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed00
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed01
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed02
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed03
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed04
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed05
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed06
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed07
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed08
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed09
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed10
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed11
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed12
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed13
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed14
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed15
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Seed16

/-!
Relator checks for the marked Held coset certificate. The seven source
relations, the definitions of the marked involutions, and cyclic rotations
are algebraic. The seventeen additional identities are checked against the
literal degree-2058 ATLAS permutations in bounded kernel computations.
Reproduce with `IndexBound/Source/generate_relators.py`.
-/

public section
namespace Held.Realization.IndexCertificate
open Subgroup.CosetWordCertificate

theorem relator_ok (r : Nat) : eval generator (relatorWords r) = 1 := by
  by_cases h : r < 98
  · simp only [relatorWords, dif_pos h]
    have hall : ∀ i : Fin 98, eval generator (relatorFin i) = 1 := fun i => match i with
      | 0 => relator_0
      | 1 => relator_1
      | 2 => relator_2
      | 3 => relator_3
      | 4 => relator_4
      | 5 => relator_5
      | 6 => relator_6
      | 7 => relator_7
      | 8 => relator_8
      | 9 => relator_9
      | 10 => relator_10
      | 11 => relator_11
      | 12 => relator_12
      | 13 => relator_13
      | 14 => relator_14
      | 15 => relator_15
      | 16 => relator_16
      | 17 => relator_17
      | 18 => relator_18
      | 19 => relator_19
      | 20 => relator_20
      | 21 => relator_21
      | 22 => relator_22
      | 23 => relator_23
      | 24 => relator_24
      | 25 => relator_25
      | 26 => relator_26
      | 27 => relator_27
      | 28 => relator_28
      | 29 => relator_29
      | 30 => relator_30
      | 31 => relator_31
      | 32 => relator_32
      | 33 => relator_33
      | 34 => relator_34
      | 35 => relator_35
      | 36 => relator_36
      | 37 => relator_37
      | 38 => relator_38
      | 39 => relator_39
      | 40 => relator_40
      | 41 => relator_41
      | 42 => relator_42
      | 43 => relator_43
      | 44 => relator_44
      | 45 => relator_45
      | 46 => relator_46
      | 47 => relator_47
      | 48 => relator_48
      | 49 => relator_49
      | 50 => relator_50
      | 51 => relator_51
      | 52 => relator_52
      | 53 => relator_53
      | 54 => relator_54
      | 55 => relator_55
      | 56 => relator_56
      | 57 => relator_57
      | 58 => relator_58
      | 59 => relator_59
      | 60 => relator_60
      | 61 => relator_61
      | 62 => relator_62
      | 63 => relator_63
      | 64 => relator_64
      | 65 => relator_65
      | 66 => relator_66
      | 67 => relator_67
      | 68 => relator_68
      | 69 => relator_69
      | 70 => relator_70
      | 71 => relator_71
      | 72 => relator_72
      | 73 => relator_73
      | 74 => relator_74
      | 75 => relator_75
      | 76 => relator_76
      | 77 => relator_77
      | 78 => relator_78
      | 79 => relator_79
      | 80 => relator_80
      | 81 => relator_81
      | 82 => relator_82
      | 83 => relator_83
      | 84 => relator_84
      | 85 => relator_85
      | 86 => relator_86
      | 87 => relator_87
      | 88 => relator_88
      | 89 => relator_89
      | 90 => relator_90
      | 91 => relator_91
      | 92 => relator_92
      | 93 => relator_93
      | 94 => relator_94
      | 95 => relator_95
      | 96 => relator_96
      | 97 => relator_97
      | ⟨n + 98, hn⟩ => by omega
    exact hall ⟨r, h⟩
  · simp [relatorWords, h]

theorem valid : Valid context markedSubgroup generator (definitions.repr generator) :=
  definitions.valid relatorWords context.allowed allowed_ok relator_ok

end Held.Realization.IndexCertificate
