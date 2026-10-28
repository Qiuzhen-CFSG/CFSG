module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularInput
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The cyclic Sylow-eleven input

The given source order has exactly one factor of eleven. Thus the actual Sylow
eleven-subgroups have order eleven and are cyclic, as required by the cyclic
defect calculation. In contrast, the ambient order is zero in the coefficient
field: Maschke's theorem for the whole group is unavailable. These facts use
the order already supplied to the representation consumer, without repeating
the preceding order argument.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters

variable {G : Type*} [Group G] [Finite G]

/-- The supplied group order gives Sylow eleven-subgroups of order eleven. -/
public theorem sylow_eleven_card (horder : Nat.card G = 175560) (P : Sylow 11 G) :
    Nat.card P = 11 := by
  rw [P.card_eq_multiplicity, horder]
  decide +kernel

/-- The source application's actual Sylow subgroup is cyclic. -/
public theorem sylow_eleven_isCyclic (horder : Nat.card G = 175560) (P : Sylow 11 G) :
    IsCyclic P :=
  isCyclic_of_prime_card (sylow_eleven_card horder P)

omit [Group G] [Finite G] in
/-- Eleven divides the group order, so it is zero in the modular coefficient field. -/
public theorem group_card_cast_eq_zero (horder : Nat.card G = 175560) :
    (Nat.card G : ElevenClosure) = 0 := by
  rw [horder]
  exact (CharP.cast_eq_zero_iff ElevenClosure 11 175560).mpr (by decide)

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
