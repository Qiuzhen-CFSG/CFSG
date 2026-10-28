module
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Exceptional
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.ComponentTerminal
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.Source

/-!
# The original A₆ shadow is impossible

The original Frattini argument supplies its nontrivial core and distinguished
involutions. If K ceased to be a component at a core involution, the full
containing-component analysis would give the marked A₈ overcomponent with
four-group core centralizer. The exceptional source calculation excludes it.
Thus K remains a component at every core involution; the marked centralizer
generation gives rank one, and the complete terminal geometry contradicts
the empty characteristic-two local family.

Every premise is a hypothesis of the original tuple. All local models,
quotient actions, fusion rules, selection marks and core geometry are derived.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
2.5.26--27 and completion of Theorem 2.1.1, printed pp.568--570.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement A6Shadow.Frattini A6Shadow.OriginalFrattini OvercomponentsSource
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The first claim of source 2.5.26, on every involution of the actual O₂(H). -/
theorem MathieuSourceSetup.alternating_six_source_core_components
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6) :
    ∀ i : G, i ∈ twoCore H → orderOf i = 2 →
      IsComponent (centralizer ({i} : Set G)) (K.subgroupOf (centralizer {i})) := by
  obtain ⟨d,hH,hK,hS,hM,_,hz,hSC,hGt⟩ :=
    original_earlier_setup c hG hempty hgen hb hstar eK
  have hphi : frattini d.SC ≠ ⊥ := by
    rw [hSC]
    exact (MathieuSourceSetup.alternating_six_source_frattini_and_crossing
      c hG hempty hgen hb hstar eK).1
  have hzz := (d.involution_identities_of_frattini_ne hphi).2
  have htC : d.t ∈ twoCore H := hSC ▸ d.t_mem
  have htZ : d.t ∈ centerIn ((S : Subgroup H).map H.subtype) := by
    rw [←hS]
    exact (show zpowers d.t ≤ centerIn d.S from d.center_sc ▸ inf_le_left)
      (mem_zpowers d.t)
  have hzKK : d.zK ∈ K := by
    have hh : d.zK ∈ centerIn (d.S ⊓ d.K) := d.center_sk.symm ▸ mem_zpowers d.zK
    exact hK ▸ hh.1.2
  intro i hi hi2
  by_contra hbad
  have hiD : i ∈ d.SC := by simpa only [hSC] using hi
  have hiBad : BadInvolution ((S : Subgroup H).map H.subtype) K i := by
    refine ⟨?_,hi2,fun hh => hbad hh.2⟩
    have hiC : i ∈ d.S ⊓ centralizer (d.K : Set G) := d.centralizer_K ▸ hiD
    simpa only [hS,hK] using hiC
  have hit : i ≠ d.t := by
    intro he
    subst i
    apply hbad
    have he : H = centralizer ({d.t} : Set G) := hH.symm.trans hGt
    rw [←he]
    exact c.component
  obtain ⟨hR,E,hE,e,hact,hres⟩ := Overcomponents.FullA6.source_full_a6_overcomponent
    c hG hempty hgen hb hstar eK d.t d.zK d.t_order d.zK_order htC htZ hzKK
    (hz.symm.trans hzz) i hiBad
  let a : MarkedA8Overcomponent d i := {
    Ki := E
    model := e
    le_centralizer := hE.1
    component := hE.2
    residual := hK.trans hres
    transposition := hact }
  exact d.marked_a8_overcomponent_false hGt hphi i hiD hi2 hit
    (by simpa only [hSC] using hR) a

/-- Original 2.5.26, with its overcomponent and marked generation arguments
fully discharged on the source tuple. -/
theorem MathieuSourceSetup.alternating_six_source_core_rank_one
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6) :
    primeRank 2 (twoCore H) = 1 :=
  MathieuSourceSetup.alternating_six_source_rank_one_of_components c hG hempty hgen hb hstar eK
    (MathieuSourceSetup.alternating_six_source_core_components c hG hempty hgen hb hstar eK)

/-- The complete original A₆ branch, without any extra source or model premise. -/
theorem MathieuSourceSetup.alternating_six_source_false
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6) : False :=
  MathieuSourceSetup.alternating_six_source_false_of_components c hG hempty hgen hb hstar eK
    (MathieuSourceSetup.alternating_six_source_core_components c hG hempty hgen hb hstar eK)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
