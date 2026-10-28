module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At.Setup
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At.Module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.NormalizerAction

/-!
# The original L₃ normalizers at G,T

The fixed line and known-simple uniqueness identify the component normalizer,
module normalizer and fixed-involution centralizer. The central-cover normalizer
calculation then identifies every normalizer action with the original L-action.
Only the structural source implication at this same G,T is required.

Source: Aschbacher–Smith, 12.2.10 and 12.4.3–5, pp.798,812–813.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At
open Section02 SmallFusion
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The fixed line supplies the actual centralizer guard of 12.4.1. -/
theorem fixed_involution_setup_of_card_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hcard : Nat.card (fixedSubgroup L V) = 2) :
    ∃ z : G, orderOf z = 2 ∧ fixedSubgroup L V = zpowers z ∧
      normalizer (L : Set G) = centralizer ({z} : Set G) ∧
      normalizer (L : Set G) = normalizer (V : Set G) ∧
      z ∈ omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) ∧
      centralizer (omegaOneAmbient ((center (T : Subgroup G)).map
        (T : Subgroup G).subtype) : Set G) ≤ normalizer (L : Set G) :=
  SLThreeSource.At.exists_fixed_involution_setup_of_card_two h D structural
    SLThreeSource.uniquenessEarlier_knownSimple hcard

/-- Every element of the actual full normalizer has an L-conjugation action. -/
theorem normalizer_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {D : ChosenModule T L V}
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥) :
    ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v := by
  obtain ⟨z, _, _, _, hnorm, _, _⟩ :=
    fixed_involution_setup_of_card_two h D structural (E.fixed_card_eq_two hne)
  intro n hn
  exact same_action_of_common_normalizer E n hn (by rwa [hnorm])

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At
