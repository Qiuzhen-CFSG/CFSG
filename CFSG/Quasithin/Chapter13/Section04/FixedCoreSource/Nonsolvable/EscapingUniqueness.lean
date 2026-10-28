module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.UniversalComparison
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentCoveredNatural

/-!
# Universal uniqueness of the escaping central involution

Component selection and recognition at every escaping point reduce the
comparison to ordinary A₆ and L₃(2), since the remaining covered natural
component is now excluded. The proved pair comparison rules out simultaneous
escaping weights two and four. The central four-group then gives uniqueness;
the constant-weight calculation gives r(G,V) ≥ 3.

Nonsolvability is assumed separately at every escaping point, and existence
is supplied by the given escaping z. Retain the original Hypothesis1331,
five-dimensional augmentation marking, same-T modules, original13.3.8 and
13.3.16, fixed and covered module clauses, M=LT and omega fixed index. The
general PairAmalgamSource1347 remains distinct from PlaneAmalgamSource1347,
and LargeDistanceInput remains independent. Their final discharge belongs
to the existing source owners. The mixed/product reciprocal exclusions,
coset graph and final rank-three offender contradiction remain with this
nonsolvable owner; this module does not assert the full13.4.1 conclusion.

Source: Aschbacher--Smith 13.4.12(1) and 13.4.17(5), printed pp.910--911,914.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Subgroup Theory.GroupTheory Stellmacher
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Chapter1.Section02.LocalModels
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Source 13.4.12(1) and the rank bound of13.4.17(5). Selection and
recognition are applied to every escaping point with its own nonsolvability
hypothesis; the covered natural alternative is now excluded internally. -/
theorem escaping_seed_uniqueness_and_rank
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1347 : Solvable.PlaneAmalgamSource1347 D m)
    (hpair1347 : PairAmalgamSource1347 T)
    (h1338 : ∀ H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G),
      ∀ Y : Subgroup G, Y ≤ H → H ≤ normalizer (Y : Set G) →
        IsPPerfect 2 Y → Y ≤ normalizer (L : Set G) → IsPiGroup twoThreePrimes Y)
    (hnonsolvable : ∀ w : V,
      w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
      w.val ∉ centralizer (L : Set G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({w.val} : Set G)))
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) = V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 ∧
      (∀ w : V, w ≠ 1 → w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
        ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z) ∧
      3 ≤ ChapterE.globalR V := by
  obtain ⟨⟨hZ,hcard⟩,hu | hc⟩ := escaping_seed_and_uniqueness_or_covered
    hl h₀ h structural modules D m h1332 fixed five covered h13316 hindex hM h1347
      hpair1347 h1338 hnonsolvable z hz1 hzT hzout
  · exact ⟨hZ,hcard,hu⟩
  · obtain ⟨w,_,hwT,hwL,_,K,hK,hKN,hKM,hfK,hcover,DK,_,_,q,e,he⟩ := hc
    have hcK : Nat.card (center (K ⧸ pCore 2 K)) = 3 := by
      obtain ⟨_,⟨c⟩,_⟩ := hcover
      rw [Nat.card_congr c.toEquiv]
      simp
    exact (covered_natural_component_excluded h₀ h structural D m h1332
      w hwT hwL hK hKN hKM hfK hcK DK q e he).elim
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
