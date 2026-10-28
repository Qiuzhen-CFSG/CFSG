module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.SourceRelators

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

theorem relator_11 : eval generator (relatorFin 11) = 1 :=
  rotated_relator [(0, true)] [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)] relator_2

theorem relator_12 : eval generator (relatorFin 12) = 1 :=
  rotated_relator [(0, false)] [(1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_13 : eval generator (relatorFin 13) = 1 :=
  rotated_relator [(0, false), (1, false)] [(0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_14 : eval generator (relatorFin 14) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false)] [(1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_15 : eval generator (relatorFin 15) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false)] [(0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_16 : eval generator (relatorFin 16) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false)] [(1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_17 : eval generator (relatorFin 17) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true)] [(0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_18 : eval generator (relatorFin 18) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false)] [(1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_19 : eval generator (relatorFin 19) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false)] [(0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_20 : eval generator (relatorFin 20) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false)] [(1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_21 : eval generator (relatorFin 21) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false)] [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_22 : eval generator (relatorFin 22) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true)] [(1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_23 : eval generator (relatorFin 23) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true)] [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_24 : eval generator (relatorFin 24) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true)] [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_25 : eval generator (relatorFin 25) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true)] [(0, true), (1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_26 : eval generator (relatorFin 26) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true)] [(1, false), (0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_27 : eval generator (relatorFin 27) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false)] [(0, true), (1, true), (0, true), (1, true)] relator_3

theorem relator_28 : eval generator (relatorFin 28) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true)] [(1, true), (0, true), (1, true)] relator_3

theorem relator_29 : eval generator (relatorFin 29) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true)] [(0, true), (1, true)] relator_3

theorem relator_30 : eval generator (relatorFin 30) = 1 :=
  rotated_relator [(0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true)] [(1, true)] relator_3

theorem relator_31 : eval generator (relatorFin 31) = 1 :=
  rotated_relator [(0, false)] [(1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true)] relator_4

theorem relator_32 : eval generator (relatorFin 32) = 1 :=
  rotated_relator [(0, false), (1, false)] [(1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true)] relator_4

theorem relator_33 : eval generator (relatorFin 33) = 1 :=
  rotated_relator [(0, false), (1, false), (1, false)] [(1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true)] relator_4

theorem relator_34 : eval generator (relatorFin 34) = 1 :=
  rotated_relator [(0, false), (1, false), (1, false), (1, false)] [(0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true)] relator_4

theorem relator_35 : eval generator (relatorFin 35) = 1 :=
  rotated_relator [(0, false), (1, false), (1, false), (1, false), (0, true)] [(1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true)] relator_4

theorem relator_36 : eval generator (relatorFin 36) = 1 :=
  rotated_relator [(0, false), (1, false), (1, false), (1, false), (0, true), (1, true)] [(1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true)] relator_4

theorem relator_37 : eval generator (relatorFin 37) = 1 :=
  rotated_relator [(0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true)] [(1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false), (1, false), (0, true), (1, true), (1, true), (1, true)] relator_4

theorem relator_38 : eval generator (relatorFin 38) = 1 :=
  rotated_relator [(0, false)] [(1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)] relator_5

theorem relator_39 : eval generator (relatorFin 39) = 1 :=
  rotated_relator [(0, false), (1, false)] [(0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)] relator_5

theorem relator_40 : eval generator (relatorFin 40) = 1 :=
  rotated_relator [(0, false), (1, false), (0, true)] [(1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)] relator_5

theorem relator_41 : eval generator (relatorFin 41) = 1 :=
  rotated_relator [(0, true)] [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_42 : eval generator (relatorFin 42) = 1 :=
  rotated_relator [(0, true), (1, true)] [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_43 : eval generator (relatorFin 43) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true)] [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_44 : eval generator (relatorFin 44) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true)] [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_45 : eval generator (relatorFin 45) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true)] [(1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_46 : eval generator (relatorFin 46) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)] [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_47 : eval generator (relatorFin 47) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true)] [(1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_48 : eval generator (relatorFin 48) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)] [(0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_49 : eval generator (relatorFin 49) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true)] [(1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_50 : eval generator (relatorFin 50) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)] [(1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_51 : eval generator (relatorFin 51) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true)] [(0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_52 : eval generator (relatorFin 52) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true)] [(1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_53 : eval generator (relatorFin 53) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false)] [(1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_54 : eval generator (relatorFin 54) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false)] [(1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_55 : eval generator (relatorFin 55) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false)] [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_56 : eval generator (relatorFin 56) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true)] [(1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_57 : eval generator (relatorFin 57) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true)] [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_58 : eval generator (relatorFin 58) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true)] [(1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_59 : eval generator (relatorFin 59) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true)] [(0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_60 : eval generator (relatorFin 60) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true)] [(1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_61 : eval generator (relatorFin 61) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false)] [(0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_62 : eval generator (relatorFin 62) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true)] [(1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_63 : eval generator (relatorFin 63) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true)] [(1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_64 : eval generator (relatorFin 64) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true)] [(1, true), (0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_65 : eval generator (relatorFin 65) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true)] [(0, true), (1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_66 : eval generator (relatorFin 66) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true)] [(1, false), (1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_67 : eval generator (relatorFin 67) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false)] [(1, false), (0, true), (1, true), (1, true)] relator_6

theorem relator_68 : eval generator (relatorFin 68) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false)] [(0, true), (1, true), (1, true)] relator_6

theorem relator_69 : eval generator (relatorFin 69) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true)] [(1, true), (1, true)] relator_6

theorem relator_70 : eval generator (relatorFin 70) = 1 :=
  rotated_relator [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, true)] [(1, true)] relator_6

theorem relator_71 : eval generator (relatorFin 71) = 1 :=
  rotated_relator [(2, false)] [(1, false), (1, false), (0, true), (1, true), (1, true)] relator_7

theorem relator_72 : eval generator (relatorFin 72) = 1 :=
  rotated_relator [(2, false), (1, false)] [(1, false), (0, true), (1, true), (1, true)] relator_7

theorem relator_73 : eval generator (relatorFin 73) = 1 :=
  rotated_relator [(2, false), (1, false), (1, false)] [(0, true), (1, true), (1, true)] relator_7

theorem relator_74 : eval generator (relatorFin 74) = 1 :=
  rotated_relator [(2, false), (1, false), (1, false), (0, true)] [(1, true), (1, true)] relator_7

theorem relator_75 : eval generator (relatorFin 75) = 1 :=
  rotated_relator [(2, false), (1, false), (1, false), (0, true), (1, true)] [(1, true)] relator_7

theorem relator_76 : eval generator (relatorFin 76) = 1 :=
  rotated_relator [(3, false)] [(1, true), (1, true), (0, true), (1, false), (1, false)] relator_8

theorem relator_77 : eval generator (relatorFin 77) = 1 :=
  rotated_relator [(3, false), (1, true)] [(1, true), (0, true), (1, false), (1, false)] relator_8

theorem relator_78 : eval generator (relatorFin 78) = 1 :=
  rotated_relator [(3, false), (1, true), (1, true)] [(0, true), (1, false), (1, false)] relator_8

theorem relator_79 : eval generator (relatorFin 79) = 1 :=
  rotated_relator [(3, false), (1, true), (1, true), (0, true)] [(1, false), (1, false)] relator_8

theorem relator_80 : eval generator (relatorFin 80) = 1 :=
  rotated_relator [(3, false), (1, true), (1, true), (0, true), (1, false)] [(1, false)] relator_8


end Held.Realization.IndexCertificate
