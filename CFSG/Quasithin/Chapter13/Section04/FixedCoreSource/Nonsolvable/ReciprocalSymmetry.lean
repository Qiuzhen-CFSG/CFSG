module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.WeightTwoComponent
/-!
# Source symmetry at the five-dimensional component

The selected augmentation component satisfies the original Hypothesis
13.3.1: its ordinary A6 quotient rules out the A5 antecedent. The same
omega center has order four, with fixed subgroup exactly the original
escaping line, so its reciprocal fixed index is two. Its full normalizer
is the actual centralizer K T.

Apply the two-type graph theorem to this reciprocal core. The original
fixed generator has weight four there, whereas the graph forces weight
two. Thus only the fixed-free natural rows remain, with actual component
point conjugacy and containment of the original fixed line.

The earlier 13.4.7 plane, 13.3.8 and 13.4.2 fusion clauses are quantified
at the faithful core components where source symmetry uses them. They
remain genuine earlier-source inputs of qt-d-1341-fixed-core-source and
qt-d-13316-source. The guarded 13.3.2 inputs transfer on the same T; no
universal Structural1222 record is constructed from an At statement.
The terminal moving actor and offender contradiction remain to be assembled.
Source: Aschbacher–Smith 13.4.17(3–4), printed p.914, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
/-- In the five-dimensional reciprocal row, the original component satisfies
Hypothesis 13.3.1 and 12.2.3, has the same omega fixed index two, and its
full normalizer is the actual centralizer K T. -/
theorem reciprocal_core_source_setup
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (DK : ChosenModule T K ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆)
    (mK : CoreMarking DK) :
    Hypothesis1331 T K ∧ Hypothesis1223 KnownSimple.IsKnownSimple T K ∧
      (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)).relIndex
        (omegaOneCenterAmbient (T : Subgroup G)) = 2 ∧
      normalizer (K : Set G) = K ⊔ (T : Subgroup G) := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨eK⟩ := ordinary_component_of_source_fixed h₀ h structural D m h1332 fixed
    hindex z hzT hzL hK hHN hKM hfK mK.fixed_ne_bot
  have hnotfive : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) := by
    rintro ⟨eFive⟩
    have hc := Nat.card_congr (eK.symm.trans eFive).toEquiv
    rw [nat_card_alternatingGroup,nat_card_alternatingGroup] at hc
    norm_num at hc
  have hK₀ : Hypothesis1331 T K :=
    { h₀ with local_component := hfK
              five_minimal := fun he => (hnotfive he).elim }
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
    (component_quotient_quasisimple h1332 hfK)
  obtain ⟨_,_,hline,_,_,_,hcard⟩ := component_core_marking_of_source_fixed
    h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK mK.fixed_ne_bot
  have hzfixed : z.val ∈ ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ ⊓
      centralizer (K : Set G) := hline.symm ▸ mem_zpowers z.val
  have hNK : centralizer ({z.val} : Set G) = normalizer (K : Set G) :=
    fixed_generator_centralizer hK12 structural DK mK hzfixed hz1
  have hH := (ordinary_six_full_centralizer h₀ h structural modules D m h1332 fixed
    hindex hM z hzT hzL hK hHN hKM hfK eK).1
  refine ⟨hK₀,hK12,?_,hNK.symm.trans hH⟩
  have hfix := component_full_fixed_line h structural z.val hz1 hzT hindex K hK.1 hKM
  have horder : Nat.card (zpowers z.val) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1
  have hc := relIndex_mul_card_of_le (show omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (K : Set G) ≤ omegaOneCenterAmbient (T : Subgroup G) from inf_le_left)
  rw [hfix,horder,hcard] at hc
  rw [hfix]
  omega

/-- Original 13.4.17(3–4): exchange the two actual components in the
remaining core row, contradicting reciprocal weight four by the graph's
weight-two conclusion. The earlier local clauses are supplied at both
components; the guarded 13.3.2 module clauses transfer on the same T. -/
theorem escaping_original_natural_component
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
    (h1347 : ∀ (A W : Subgroup G) (DA : ChosenModule T A W) (ma : CoreMarking DA),
      Hypothesis1331 T A → Solvable.PlaneAmalgamSource1347 DA ma)
    (hpair1347 : PairAmalgamSource1347 T)
    (h1338 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ∀ H ∈ Chapter1.HOutside G (T : Set G) (normalizer (A : Set G) : Set G),
      ∀ Y : Subgroup G, Y ≤ H → H ≤ normalizer (Y : Set G) →
        IsPPerfect 2 Y → Y ≤ normalizer (A : Set G) → IsPiGroup twoThreePrimes Y)
    (hfusion : ∀ (A W : Subgroup G) (DA : ChosenModule T A W),
      CoreMarking DA → Hypothesis1331 T A →
      ∀ v : W, v ≠ 1 → ∀ w ∈ W, IsConj v.val w →
        ∃ n ∈ normalizer (W : Set G), MulAut.conj n v.val = w)
    (hnonsolvable : ∀ w : V,
      w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
      w.val ∉ centralizer (L : Set G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({w.val} : Set G)))
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)) ∧
      K ∈ MainForward.faithfulLocalComponents T ∧
      centralizer ({z.val} : Set G) ≤ normalizer (K : Set G) ∧
      (¬ K ≤ normalizer (L : Set G)) ∧
      let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      ∃ DK : ChosenModule T K U, Nonempty (ComponentModuleAt DK z.val) ∧
        V ⊓ centralizer (L : Set G) ≤ U ∧
        U ⊓ centralizer (K : Set G) = ⊥ ∧
        ∀ w ∈ U, w ≠ 1 → IsConj m.constant.val w := by
  obtain ⟨K,hK,hfK,hHN,hKM,DK,mark,hFU,halt⟩ :=
    escaping_original_component_fixed_line hl h₀ h structural modules D m h1332
      fixed five covered h13316 hindex hM (h1347 L V D m h₀) hpair1347
      (h1338 L h₀) (hfusion L V D m h₀) hnonsolvable z hz1 hzT hzout
  refine ⟨K,hK,hfK,hHN,hKM,DK,mark,hFU,?_⟩
  rcases halt with hnat | ⟨mK,hd,hd4,hdout,hrecip⟩
  · exact hnat
  · exfalso
    have hzL : z.val ∉ centralizer (L : Set G) := by
      intro hz
      exact hzout (fixed_generator_centralizer h structural D m ⟨z.property,hz⟩
        (fun he => hz1 (Subtype.ext he))).le
    obtain ⟨hK₀,hK12,hiK,hNK⟩ := reciprocal_core_source_setup h₀ h structural modules
      D m h1332 fixed hindex hM z hzT hzL hK hHN hKM hfK DK mK
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    let d : U := ⟨m.constant.val,hd⟩
    have hd1 : d ≠ 1 := fun he => m.constant_ne_one (Subtype.ext (congrArg (fun w : U => w.val) he))
    have hdT := (m.constant_mem_central_four h structural).2
    have hnonsolvK : ∀ w : U,
        w.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
        w.val ∉ centralizer (K : Set G) →
        ¬ centralizer ({w.val} : Set G) ≤ normalizer (K : Set G) →
        ¬ Group.IsSolvable (centralizer ({w.val} : Set G)) := by
      intro w hwT hwK hwout
      have hw1 : w ≠ 1 := fun he => hwK (he ▸ one_mem _)
      exact (hrecip w hw1 hwT hwout).2
    have hw2 := (escaping_original_graph_pair hl hK₀ hK12 structural modules DK mK h1332
      (fun _ => fixed h₀) (fun _ => five h₀) (fun _ => covered h₀)
      h13316 hiK hNK (h1347 K U DK mK hK₀) hpair1347
      (h1338 K hK₀) (hfusion K U DK mK hK₀) hnonsolvK d hd1 hdT hdout).1
    change mK.weight d = 4 at hd4
    omega

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
