module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.KnownOrders
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Tables

/-!
# Sporadic cases of the E.6.18 inspection

The M₁₁, M₁₂, M₂₃ and J₁ cases are proved for the actual carriers and
transport through genuine multiplicative equivalences. The separate J₁
constructor of Theorem C is assembled below, without any additional premise.

The M₂₂, M₂₄ and J₂ reductions retain their earlier involution tables as
explicit inputs. Those inputs, and the HS, He, J₄ and Ru cases, remain
obligations of the full sporadic assembly. In particular no catalogue entry
has been removed, and the conditional reductions are not assertions that
the source inspection is complete.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252, and the complete sporadic list in Theorem C, printed p.33.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
variable {S : Type*} [Group S]

/-- The separate J₁ constructor of Theorem C satisfies the full inspection. -/
theorem sevenActionInspection_of_janko_one (e : S ≃* Janko1.Model) :
    SevenActionInspection S :=
  SporadicInspection.of_equiv e SporadicInspection.janko_one

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
