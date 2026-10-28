module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.AlternatingFiveAction.Normalization
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.AlternatingFiveAction.Thompson

/-!
# The odd actor on the original alternating-five block

The original prime actor normalizes L and J(S). The genuine A₅ module
and its finite five-point automorphism calculation now show that it
centralizes L, contradicting the actor's original moving commutator.
The proof applies at p=3 or5 before exchanged selection and preserves
central two-covers and the actual S-orbit. It never uses the legacy
core-movement field. The older quotient-lift adapters remain available.

Source: Aschbacher--Smith 15.1.21(ii), printed p.1098, PDF page1115.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- Conditional source application of the full-block lift. The remaining
premise concerns the literal core quotient, not the desired centralization. -/
theorem PreExclusionSource.primeActor_centralizes_of_quotient_action
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hb : ChapterC.IsAlternatingBlock d.L 5) {Y : Subgroup G}
    (y : d.RankOnePrimeActor p Y) (hq : ⁅Y,d.L⁆ ≤ d.L.pCoreIn 2) :
    Y ≤ centralizer (d.L : Set G) :=
  hb.twoPerfect_centralizes_of_quotient_centralizes (y.twoPerfect hp)
    (s.primeActor_normalizes (h := h) y hp) hq

/-- The original moving actor supplies the contradiction after, and only
after, its quotient action has been calculated. -/
theorem PreExclusionSource.false_of_primeActor_quotient_action
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hb : ChapterC.IsAlternatingBlock d.L 5) {Y : Subgroup G}
    (y : d.RankOnePrimeActor p Y) (hq : ⁅Y,d.L⁆ ≤ d.L.pCoreIn 2) : False :=
  s.false_of_moving_actor_centralizes (h := h)
    (s.primeActor_centralizes_of_quotient_action (h := h) hp hb y hq) y.moves

/-- The full exceptional block calculation, for either original odd prime.
The component identity supplies J(S)-normalization; the actor's original
residual placement supplies its own normalization of L. -/
theorem PreExclusionSource.alternatingFive_primeActor_centralizes
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hb : ChapterC.IsAlternatingBlock d.L 5)
    (hmove : ⁅d.L, elementaryAbelianMaxJ d.S⁆ = d.L)
    {Y : Subgroup G} (y : d.RankOnePrimeActor p Y) :
    Y ≤ centralizer (d.L : Set G) := by
  obtain ⟨P,hP⟩ := s.component_sylow
  exact hb.thompson_actor_centralizes d.L d.S Y (T.isPGroup'.to_le d.S_le_T)
    P (hP ▸ d.SL_le_S) hmove (y.twoPerfect hp)
    (s.primeActor_normalizes (h := h) y hp)
    (y.normalizes_local_thompson (h := h) hG hM hJ)

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
