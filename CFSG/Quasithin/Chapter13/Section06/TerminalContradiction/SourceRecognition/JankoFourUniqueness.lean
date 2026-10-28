module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.Source523KnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.FiveDivisorNormalization
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.FourSporadic
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.SpecificGroups.Janko4.Model.Cardinality

/-!
# Uniqueness of the actual J₄ component in the original A₅ source setup

The concrete J₄ quotient is centerless and has three-rank at least two,
so every other C-component has order prime to three and hence a Suzuki
quotient by the proved known-simple catalogue. Its normalization follows
from the component-orbit argument at five, using the actual J₄ order.
The original source setup then applies 5.2.3 to its join with the full Sylow.
The residual is prime to three, excluding the local alternatives, while
Hypothesis 13.3.1 and the order divisor 35 exclude the global alternatives.

Source: Aschbacher–Smith 5.2.3 and 13.6.27, printed pp.649 and 934–935.
The genuine earlier 5.2.3 theorem is retained explicitly; no Candidate label
or independent simplicity theorem for J₄ is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source SourceParameters
open Components Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]

private theorem jankoFour_quotient_center {H : Type*} [Group H]
    (e : H ≃* Janko4.Model) : center H = ⊥ := by
 apply eq_bot_iff.mpr
 intro x hx
 have he : e x ∈ center Janko4.Model := (centerCongr e ⟨x,hx⟩).property
 rw [Janko4.model_center_eq_bot,mem_bot] at he
 exact e.map_eq_one_iff.mp he

private theorem jankoFour_threeRank {H : Type*} [Group H] [Finite H]
    (e : H ≃* Janko4.Model) : 2 ≤ primeRank 3 H := by
 rw [primeRank_congr 3 e]
 exact ChapterA.Section03.OddPrime.SourceModels.FourSporadic.j4_three_rank_ge_two

private theorem component_unique_of_jankoFour_setup
    (d : Context T L V V₁ V₂ V₃)
    (s : EarlierA5Setup T L V (normalizer (L : Set G)) (normalizer (V : Set G)))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (L₁ : Subgroup G)
    (hH : centralizer ({s.z.val} : Set G) ∈ Section08.Source.Hz
      L₁ (T : Subgroup G) (centralizer ({s.z.val} : Set G)) (normalizer (L : Set G)))
    {K : Subgroup (centralizer ({s.z.val} : Set G))}
    (hK : K.IsCComponent) [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : (K ⧸ pCore 2 K) ≃* Janko4.Model) :
    ∀ D : Subgroup (centralizer ({s.z.val} : Set G)), D.IsCComponent → D = K := by
 let : Fact (Nat.Prime 5) := ⟨by decide⟩
 let : IsSimpleGroup G := d.hypothesis.qtke.simple
 have hsq := d.hypothesis.qtke.involution_centralizer_sqtk s.marked_order
 have hsqQ : IsSQTK KnownSimple.IsKnownSimple
     ((centralizer ({s.z.val} : Set G)) ⧸ pCore 2 (centralizer ({s.z.val} : Set G))) := by
   refine ⟨?_,hsq.isKGroup.quotient _⟩
   intro p hp ho
   let : Fact p.Prime := ⟨hp⟩
   exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
     (hsq.stronglyQuasithin p hp ho)
 have hK35 : 35 ∣ Nat.card (K ⧸ pCore 2 K) := by
   rw [Nat.card_congr e.toEquiv,Janko4.Cardinality.model_card]
   decide
 have h35 : 35 ∣ Nat.card G := hK35.trans
   ((card_quotient_dvd_card _).trans (K.card_subgroup_dvd_card.trans
     (centralizer ({s.z.val} : Set G)).card_subgroup_dvd_card))
 have hglobal : ¬ Source523.GlobalAlternative G := by
   have ha := d.hypothesis.hypothesis1311
   rintro (hm | ⟨f,hf⟩)
   · exact ha.no_M23 hm
   · exact ha.no_rankTwo f (rankTwo_parameter_gt_one_of_thirtyFive_dvd hf h35) hf
 have h25 := source_13_6_25_knownSimple d.hypothesis.qtke s
 intro D hD
 by_contra hne
 have hthree := hK.other_coprime_three_of_rank (jankoFour_quotient_center e)
   (jankoFour_threeRank e) (hsq.stronglyQuasithin 3 (by decide) (by decide)) hD hne
 obtain ⟨m,hm,⟨f⟩⟩ := Catalogue.component_suzuki_quotient
   (ChapterA.SQTKStructure.a36Input_of_theoremsAC
     (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
     (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) hsqQ hD hthree
 let := suzuki_component_normal_of_five_dvd hK
   ((by decide : 5 ∣ 35).trans hK35) hD hne hm f
   (hsqQ.stronglyQuasithin 5 (by decide) (by decide))
 have hn : (T : Subgroup G).subgroupOf (centralizer ({s.z.val} : Set G)) ≤
     normalizer (D : Set (centralizer ({s.z.val} : Set G))) := by
   exact le_top.trans_eq (normalizer_eq_top (H := D)).symm
 obtain ⟨hJ,hmodels⟩ := hz_component_obstruction T L₁ _ (normalizer (L : Set G))
   s.z.val s.marked_order (s.module_le s.z.property) hH D hD hn f hthree h25.2.2.1
   (fun J hJ E hE => component_image_not_le_of_original_setup d.hypothesis.qtke s L₁ _ hJ E hE)
 have hmin : Minimal (fun Y => Y ∈ Chapter1.HOver G (T : Set G) ∧
     ¬ Y ≤ normalizer (L : Set G))
     (D.map (centralizer ({s.z.val} : Set G)).subtype ⊔ (T : Subgroup G)) := hJ
 exact hglobal ((Source523.residual_models_or_global h523 (original_source523_setup d s)
   hJ (h25.2.1 _ hmin.prop)).resolve_left hmodels)

/-- The actual J₄ component in the original line centralizer is unique after
source 5.2.3, using its concrete rank and order in place of a Candidate label. -/
theorem source_component_unique_of_jankoFour
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    {K : Subgroup (centralizer (V₁ : Set G))} (hK : K.IsCComponent)
    [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : (K ⧸ pCore 2 K) ≃* Janko4.Model) :
    ∀ D : Subgroup (centralizer (V₁ : Set G)), D.IsCComponent → D = K := by
 obtain ⟨s, hs, _⟩ := source_parameter_setup_knownSimple d hCv houtside hcounter
 have hC : centralizer ({s.z.val} : Set G) = centralizer (V₁ : Set G) := by
   rw [← hs, zpowers_eq_closure, centralizer_closure]
 have hH : centralizer ({s.z.val} : Set G) ∈ Section08.Source.Hz
     (Ratio.residualCentralizer L V₁) (T : Subgroup G)
     (centralizer ({s.z.val} : Set G)) (normalizer (L : Set G)) := by
   rw [hC]
   exact SourceAbelian.point_centralizer_mem_family d houtside
 have haux : ∀ K' : Subgroup (centralizer ({s.z.val} : Set G)),
     K'.IsCComponent → K'.Normal → IsQuasisimple (K' ⧸ pCore 2 K') →
     ((K' ⧸ pCore 2 K') ≃* Janko4.Model) →
     ∀ D : Subgroup (centralizer ({s.z.val} : Set G)), D.IsCComponent → D = K' := by
   intro K' hK' hn hq e'
   let := hn
   let := hq
   exact component_unique_of_jankoFour_setup d s h523
     (Ratio.residualCentralizer L V₁) hH hK' e'
 have haux' : ∀ K' : Subgroup (centralizer (V₁ : Set G)),
     K'.IsCComponent → K'.Normal → IsQuasisimple (K' ⧸ pCore 2 K') →
     ((K' ⧸ pCore 2 K') ≃* Janko4.Model) →
     ∀ D : Subgroup (centralizer (V₁ : Set G)), D.IsCComponent → D = K' := by
   exact hC ▸ haux
 exact haux' K hK inferInstance inferInstance e
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
