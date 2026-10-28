module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationCoveredAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# The two genuine fixed-core quotient rows

The augmentation marking identifies the central quotient of L/O2(L)
with A6. The two-core quotient has odd center, so the alternating central
cover theorem leaves center order one or three. The first alternative
constructs the ordinary A6 isomorphism; the second retains the full
quasisimple triple cover. Thus the action quotient is never substituted
silently for the original two-core quotient.

FixedModuleAt applies this dichotomy to the marking constructed from
13.3.2 at the original nonzero fixed part.
Source: Aschbacher--Smith 13.4.4(2), printed p.897; GLS3 5.2.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual quotient by O2(L) is ordinary A6 or the quasisimple triple cover. -/
theorem original_quotient_rows
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) := by
  let := hq
  let e := Nonsolvable.augmentationCentralQuotient D m
  have hn : ¬ 2 ∣ Nat.card (center (L ⧸ pCore 2 L)) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center (L ⧸ pCore 2 L)) le_rfl
  have ho : Odd (Nat.card (center (L ⧸ pCore 2 L))) :=
    Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide) e ho with
    hc | ⟨_,hc⟩
  · exact Or.inl ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6 e hc⟩
  · exact Or.inr ⟨hq,hc,⟨e⟩⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
