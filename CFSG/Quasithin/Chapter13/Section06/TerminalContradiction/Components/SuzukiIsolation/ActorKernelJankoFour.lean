module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernelSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.JankoFourQuotient
public import Theory.SpecificGroups.Janko4.Model.Cardinality

/-!
# The Janko-four actor kernel before uniqueness

The native J₄ quotient is centerless, has three-rank at least two, and
has order divisible by five. Thus the same original prime-core and
five-rank argument gives exactly two factors in F*(H/O₂(H)) if an extra
Suzuki component exists. The full actor kernel embeds in Aut(Kbar).
The centralizer of the Suzuki image has generalized Fitting subgroup Kbar;
the proved full innerness of J₄ then identifies that entire centralizer
with J₄. Simplicity is inherited from the actual quasisimple quotient.

Source: Aschbacher–Smith13.6.26–27, printed pp.934–935; the genuine J₄
outer automorphism calculation used by E.1.14(5), printed p.214.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
universe u

private theorem jankoFour_threeRank {H : Type*} [Group H] [Finite H]
    (e : H ≃* Janko4.Model) : 2 ≤ primeRank 3 H := by
  rw [primeRank_congr 3 e]
  exact ChapterA.Section03.OddPrime.SourceModels.FourSporadic.j4_three_rank_ge_two

/-- J₄ has the same actual Suzuki catalogue for its other components. -/
theorem other_suzuki_of_jankoFour {H : Type u} [Group H] [Finite H]
    (hH : IsSQTK KnownSimple.IsKnownSimple H) {K D : Subgroup H}
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : (K ⧸ pCore 2 K) ≃* Janko4.Model) (hD : D.IsCComponent) (hne : D ≠ K) :
    ∃ m : ℕ, 1 ≤ m ∧
      Nonempty ((D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
  other_suzuki_of_centerless_threeRank hH hK
    (jankoFour_quotient_center_eq_bot e) (jankoFour_threeRank e) hD hne

open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
variable {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K D : Subgroup (centralizer (V₁ : Set G))}
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : (K ⧸ pCore 2 K) ≃* Janko4.Model)
    (hD : D.IsCComponent) (hne : D ≠ K)
include d hCv houtside hcounter hK e hD hne

/-- The original J₄ row has the full two-factor structure before uniqueness. -/
theorem jankoFour_structure_of_context :
    let H := centralizer (V₁ : Set G)
    let q := QuotientGroup.mk' (pCore 2 H)
    fittingSubgroup (H ⧸ pCore 2 H) = ⊥ ∧
      generalizedFitting (H ⧸ pCore 2 H) = K.map q ⊔ D.map q ∧
      centralizer (generalizedFitting (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) = ⊥ ∧
      center (generalizedFitting (H ⧸ pCore 2 H)) = ⊥ := by
  let := d.elementary
  have hH := SourceAbelian.point_centralizer_mem_family d houtside
  have hSQ := Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1
  have hlarge := fun p hp hlarge =>
    source_quotient_pCore_eq_bot_of_context_knownSimple d hCv houtside hcounter
      (Ratio.residualCentralizer L V₁) _ hH p hp hlarge
  have hz := jankoFour_quotient_center_eq_bot e
  have hr := jankoFour_threeRank e
  have h5 : 5 ∣ Nat.card (K ⧸ pCore 2 K) := by
    rw [Nat.card_congr e.toEquiv, Janko4.Cardinality.model_card]
    decide
  have hf := fitting_twoCore_quotient_eq_bot
    (hK.threeCore_twoCore_quotient_eq_bot hz hr
      (hSQ.stronglyQuasithin 3 (by decide) (by decide))) hlarge
  exact ⟨hf, generalizedFitting_eq_pair_of_centerless_threeRank hSQ hK hz hr h5
    hD hne hlarge, centerless_of_fitting_bot hf⟩

/-- The actual quotient actor's Suzuki kernel embeds in the J₄ automorphisms. -/
theorem jankoFour_kernel_injective_of_context [K.Normal] [D.Normal]
    (A : Subgroup ((centralizer (V₁ : Set G)) ⧸ pCore 2 (centralizer (V₁ : Set G)))) :
    Function.Injective (action (K.map (QuotientGroup.mk' (pCore 2 _)))
      (D.map (QuotientGroup.mk' (pCore 2 _))) A) := by
  obtain ⟨hf, hF, _⟩ := jankoFour_structure_of_context d hCv houtside hcounter hK e hD hne
  exact action_injective _ _ A hf hF

/-- Full innerness identifies the whole Suzuki centralizer with J₄, so its
original faithful representation is eligible for the J₄ strict-ratio bound. -/
noncomputable def jankoFour_centralizerEquiv [K.Normal] [D.Normal] :
    centralizer (D.map (QuotientGroup.mk' (pCore 2 (centralizer (V₁ : Set G)))) :
      Set ((centralizer (V₁ : Set G)) ⧸ pCore 2 (centralizer (V₁ : Set G)))) ≃* Janko4.Model := by
  let H := centralizer (V₁ : Set G)
  let q := QuotientGroup.mk' (pCore 2 H)
  let Kb := K.map q
  let Db := D.map q
  let C := centralizer (Db : Set (H ⧸ pCore 2 H))
  let := pCore_isNilpotent (p := 2) (G := H)
  obtain ⟨hf, hF, _⟩ := jankoFour_structure_of_context d hCv houtside hcounter hK e hD hne
  have hR := radical_bot_of_fitting_bot hf
  have hKb : Kb.IsCComponent := hK.map_quotient _
  have hDb : Db.IsCComponent := hD.map_quotient _
  have hKD : Kb ≠ Db := fun he => hne (hD.eq_of_map_quotient_eq hK _ he.symm)
  have hKC : Kb ≤ C := commutator_eq_bot_iff_le_centralizer.mp
    (hKb.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hDb hKD)
  let : IsQuasisimple Kb := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hFC := centralizer_generalizedFitting Kb Db hKC hf hF
  let f : Kb.subgroupOf C ≃* Janko4.Model :=
    (subgroupOfEquivOfLe hKC).trans ((cComponentTwoCoreQuotientEquiv hK).symm.trans e)
  let : IsSimpleGroup (K ⧸ pCore 2 K) := jankoFour_quotient_isSimple e
  let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
  let : IsSimpleGroup (Kb.subgroupOf C) := f.isSimpleGroup
  exact ChapterE.JankoFour.ambientEquiv (Kb.subgroupOf C) hFC f

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
