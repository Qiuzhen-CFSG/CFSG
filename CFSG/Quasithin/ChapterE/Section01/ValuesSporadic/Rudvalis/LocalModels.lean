module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Definitions
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.PGroupCore

/-!
# The two intrinsic Rudvalis local quotient calculations

The preserved ATLAS max4 and max6 word subgroups have advertised structures
2^(3+8):L₃(2) and 2^(1+4+6).S₅, respectively. The proposition below requests
actual multiplicative equivalences from their intrinsic two-core quotients
to the projective binary matrix group and the five-letter permutation group.
The ATLAS labels alone do not prove this proposition.

These calculations and the compatible generating-cover calculation can be
proved independently. The cover may take this proposition as an explicit
input; the E.1.14(5) assembly owner must supply it before completing that
source theorem. For ambient two-extensions, the actual quotient action must
still be checked: a local quotient need not equal its simple-case quotient.

Source: GLS3 Table 5.3r, printed p.279; Aschbacher--Smith E.1.14(5), printed
p.214, citing Asc82a, Lemma 4.9. The exact carriers, word conventions and
ATLAS source attribution are retained in SylowOvergroups.Definitions.
-/

namespace CFSG.Quasithin.ChapterE.Rudvalis

open _root_.Rudvalis.SylowOvergroups

/-- Actual quotient identifications for the two fixed ATLAS word subgroups.
No witness is asserted by this definition. -/
@[expose] public def LocalQuotientModels : Prop :=
  Nonempty ((max4 ⧸ pCore 2 max4) ≃* Matrix.PSL3Two.PSL) ∧
    Nonempty ((max6 ⧸ pCore 2 max6) ≃* Equiv.Perm (Fin 5))

end CFSG.Quasithin.ChapterE.Rudvalis
