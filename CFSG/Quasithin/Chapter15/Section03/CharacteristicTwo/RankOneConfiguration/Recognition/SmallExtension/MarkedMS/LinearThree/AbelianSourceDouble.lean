module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSourceDouble.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.AbelianSourceDouble.Action

/-!
# The doubled-natural radical inequality of C.1.34(2)

For an abelian commutator core of order 64, the original small MS hypotheses
construct the doubled-natural action of the literal join L ∨ R. One component
conjugator marks both its component Sylow and the unique common-axis offender,
which lies in the image of R. Odd-index averaging supplies the correction from
the Sylow fixed space to its actual omega-center. The common-axis obstruction
then excludes equality of R with the two-core of that omega-center centralizer.

The public inequality discharges the order-64 premise of
`SmallMSPair.abelian_source_of_geometry`. The second theorem also combines it
with the actual doubled section model, using a single marking. No action,
offender, splitting or radical-inequality premise remains.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.34(2),
printed pp.136–137, especially the common-axis versus common-center argument.
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R S : Subgroup G}

/-- The radical inequality in C.1.34(2), on the original join and Sylow
omega-center, from the small MS hypotheses alone in the doubled-natural branch. -/
theorem SmallMSPair.abelian_source_double_not_centralizer_core (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 64)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    MSNotCentralizerCore L R S := by
  obtain ⟨a⟩ := h.exists_doubledSourceAction e hc hcard hS hRS
  exact h.abelian_source_double_of_action e hc hcard hS hRS a

/-- The full doubled-natural source alternative, retaining the actual section
model and the radical inequality for the same original subgroups. -/
theorem SmallMSPair.abelian_source_of_card_sixty_four (h : SmallMSPair κ L R)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hc : IsMulCommutative (msQ L R)) (hcard : Nat.card (msQ L R) = 64)
    (hS : Chapter1.IsSylowIn 2 S (L ⊔ R)) (hRS : R ≤ S) :
    ∃ e', MSModuleAlternatives L R S 1 (ZMod 2) e' := by
  obtain ⟨e', h8 | h64 | h16⟩ := h.abelian_source_sections e hc
  · omega
  · exact ⟨e', Or.inr (Or.inl
      ⟨h64.2, h.abelian_source_double_not_centralizer_core e hc hcard hS hRS⟩)⟩
  · omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
