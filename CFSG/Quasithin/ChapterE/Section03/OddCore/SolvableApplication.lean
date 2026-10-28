module

public import CFSG.Quasithin.ChapterE.Section03.OddCore
public import CFSG.Quasithin.ChapterE.Section04.Solvable

/-!
# Applying E.3.40 to the solvable parameter bound

The E.3.40 centralization theorem discharges the explicit earlier-source
premise in the solvable E.4.1 reduction. Thus a faithful finite binary module
for a finite solvable group with trivial two-core has parameter at most one.
For even-order groups the parameter equals one; in odd order E.3.9 instead
sets it to zero.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.3.40 and
E.4.1, printed pp.240–241. The section owners retain their assembly modules.
-/

namespace CFSG.Quasithin.ChapterE.OddCore

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- E.3.40 supplies the odd-core centralization premise of the solvable bound. -/
public theorem moduleA_le_one_of_solvable
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥) : moduleA ρ ≤ 1 :=
  moduleA_le_one_of_oddCore_centralization ρ hsolv hcore
    (fun _ hA => lemma_E_3_40 ρ hρ hA)

/-- The equality in the solvable even-order case, with E.3.40 discharged. -/
public theorem moduleA_eq_one_of_solvable_of_even
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (hsolv : Group.IsSolvable G) (hcore : pCore 2 G = ⊥)
    (heven : Even (Nat.card G)) : moduleA ρ = 1 :=
  moduleA_eq_one_of_even_of_oddCore_centralization ρ hsolv hcore heven
    (fun _ hA => lemma_E_3_40 ρ hρ hA)

end CFSG.Quasithin.ChapterE.OddCore
