module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentRecognition
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComparisonApplicability

/-!
# The universal escaping-point comparison and its remaining covered case

Apply component selection and recognition separately to every escaping
point, using universal nonsolvability at each invocation. Unless a selected
component is the still-unexcluded covered A₆ with its actual fixed-free
natural module, the four completed pair comparisons exclude simultaneous
weights two and four. The central four-group then gives uniqueness, and the
existing constant-weight argument gives r(G,V) ≥ 3. The full omega-center
has order four in every case, including the covered alternative.

This is a reduction with an explicit, marked exceptional output. It is not
unrestricted 13.4.12: the fixed-free covered-component exclusion remains with
this nonsolvable owner, along with the reciprocal and graph arguments. The
original earlier-source inputs, both distinct amalgam inputs, and independent
LargeDistanceInput retain final discharge with their existing source owners.

Source: Aschbacher--Smith 13.4.10--12 and 13.4.17(5), printed pp.907--911,914.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Chapter1.Section02.LocalModels
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Selection at every escaping point gives the full seed and reduces any
failure of uniqueness to an actual covered natural component. The universal
nonsolvability input is used separately for each point in the comparison.
This does not assert source 13.4.12 until the covered alternative is excluded. -/
theorem escaping_seed_and_uniqueness_or_covered
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
    (omegaOneCenterAmbient (T : Subgroup G) = V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4) ∧
    (((∀ w : V, w ≠ 1 → w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
        ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z) ∧
        3 ≤ ChapterE.globalR V) ∨
      (∃ w : V, w ≠ 1 ∧ w.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
        w.val ∉ centralizer (L : Set G) ∧
        (¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G)) ∧
        ∃ K : Subgroup G,
          K ∈ Chapter1.cComponentsIn (centralizer ({w.val} : Set G)) ∧
          centralizer ({w.val} : Set G) ≤ normalizer (K : Set G) ∧
          (¬ K ≤ normalizer (L : Set G)) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          IsAlternatingCover (K ⧸ pCore 2 K) 6 ∧
          let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
          ∃ DK : ChosenModule T K U,
            U ⊓ centralizer (K : Set G) = ⊥ ∧
            U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
              (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
            ∃ q : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6),
              ∃ e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)),
                ∀ (k : K) (v : U),
                  (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
                    BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
                      (q (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd)) := by
  classical
  have nonfixed (v : V) (hv1 : v ≠ 1)
      (hvout : ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G)) :
      v.val ∉ centralizer (L : Set G) := by
    intro hv
    exact hvout (fixed_generator_centralizer h structural D m ⟨v.property,hv⟩
      (fun he => hv1 (Subtype.ext he))).le
  have hzL := nonfixed z hz1 hzout
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hZ,hcard⟩ := exists_escaping_component_marking_and_seed
    hl h₀ h structural modules D m h1332 fixed five covered h13316 hindex h1338
      z hzT hzL hzout (hnonsolvable z hzT hzL hzout)
  refine ⟨⟨hZ,hcard⟩,?_⟩
  by_cases hc : ∃ w : V, w ≠ 1 ∧ w.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
        w.val ∉ centralizer (L : Set G) ∧
        (¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G)) ∧
        ∃ K : Subgroup G,
          K ∈ Chapter1.cComponentsIn (centralizer ({w.val} : Set G)) ∧
          centralizer ({w.val} : Set G) ≤ normalizer (K : Set G) ∧
          (¬ K ≤ normalizer (L : Set G)) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          IsAlternatingCover (K ⧸ pCore 2 K) 6 ∧
          let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
          ∃ DK : ChosenModule T K U,
            U ⊓ centralizer (K : Set G) = ⊥ ∧
            U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
              (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
            ∃ q : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6),
              ∃ e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)),
                ∀ (k : K) (v : U),
                  (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
                    BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
                      (q (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd
  · exact Or.inr hc
  apply Or.inl
  have recognize (v : V) (hv1 : v ≠ 1)
      (hvT : v.val ∈ omegaOneCenterAmbient (T : Subgroup G))
      (hvout : ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G)) :
      ∃ K : Subgroup G,
        K ∈ Chapter1.cComponentsIn (centralizer ({v.val} : Set G)) ∧
        centralizer ({v.val} : Set G) ≤ normalizer (K : Set G) ∧
        (¬ K ≤ normalizer (L : Set G)) ∧
        K ∈ MainForward.faithfulLocalComponents T ∧
        (Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
          Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))) := by
    have hvL := nonfixed v hv1 hvout
    obtain ⟨K,hK,hfK,_,hKN,_,hKM,_⟩ := exists_escaping_component
      h₀ h structural m h1332 h1338 hvT (fun he => hv1 (Subtype.ext he)) hvout
        (hnonsolvable v hvT hvL hvout)
    rcases selected_component_recognition hl h₀ h structural D m h1332 fixed five covered
        h13316 hindex v hvT hvL hK hKN hKM hfK with hlin | hsix | hcov
    · exact ⟨K,hK,hKN,hKM,hfK,Or.inl hlin⟩
    · exact ⟨K,hK,hKN,hKM,hfK,Or.inr hsix⟩
    · exact (hc ⟨v,hv1,hvT,hvL,hvout,K,hK,hKN,hKM,hfK,hcov⟩).elim
  have hp (v w : V)
      (hvT : v.val ∈ omegaOneCenterAmbient (T : Subgroup G))
      (hwT : w.val ∈ omegaOneCenterAmbient (T : Subgroup G))
      (hv : m.weight v = 2) (hw : m.weight w = 4)
      (hvout : ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G))
      (hwout : ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G)) : False := by
    have hv1 : v ≠ 1 := by intro he; rw [he,m.weight_one] at hv; omega
    have hw1 : w ≠ 1 := by intro he; rw [he,m.weight_one] at hw; omega
    obtain ⟨K,hK,hKN,hKM,hfK,model⟩ := recognize v hv1 hvT hvout
    obtain ⟨N,hN,hNN,hNM,hfN,modelN⟩ := recognize w hw1 hwT hwout
    exact small_components_both_weights_false hl h₀ h structural modules D m h1332 fixed
      hindex hM h1347 v w hvT hwT (nonfixed v hv1 hvout) (nonfixed w hw1 hwout)
      hv hw K N hK hKN hKM hfK model hN hNN hNM hfN modelN hpair1347
  have hu := m.unique_escape_of_weight_exclusion h structural m.central_four_card_le hp
    z hz1 hzT hzout
  exact ⟨hu,m.three_le_globalR_of_unique_escape h structural z hz1 hzT hzout hu⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
