module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Reduction
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.Quotient

/-!
# M₂₄ inspection from the literal second centralizer

Every involutory automorphism is inner and its fixed group is one of two
marked centralizers. The first has proved order 21504. Thus only the
nondivisibility by nine of the second actual centralizer remains; full
kernel shapes are unnecessary for E.6.18. This input is still explicit.

Source: Aschbacher–Smith E.6.18 and 16.1.5(7), printed pp.252,1171.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
open Sporadic.Mathieu Sporadic.Mathieu.M24InvolutionCentralizers

/-- Actual automorphism coverage and the full 2A order leave just a marked
2B cardinal bound, rather than either complete centralizer-shape theorem. -/
theorem m24_of_second_centralizer (hsecond : ¬ 9 ∣ Nat.card centralizer2B) :
    SevenActionInspection M24 := by
  apply of_involution_fixed_card
  intro r hr
  rcases (fixedSubgroup_alternative r hr).2 with he | he
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv,TwoA.centralizer_card]
    decide
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv]
    exact fun hd => hsecond ((by decide : 9 ∣ 2520).trans hd)
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
