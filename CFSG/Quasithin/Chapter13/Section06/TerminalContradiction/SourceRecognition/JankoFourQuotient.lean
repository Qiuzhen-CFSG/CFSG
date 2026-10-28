module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ResidualKnownSimple
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.FourSporadic
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoFour.Ambient
public import Theory.SpecificGroups.Janko4.Model.Center
/-!
# The actual singular-centralizer quotient in the Janko-four branch

An original component with J₄ two-core quotient has centerless quotient
and three-rank at least two. The ambient SQTK bound kills the quotient
three-core; the original 13.6.26(2) kills every larger-prime core. Given
component uniqueness, its actual image is therefore the whole generalized
Fitting subgroup. The proved full innerness of the J₄ automorphism group
identifies the ambient two-core quotient itself with the native J₄ carrier.

Simplicity is inherited from the original quasisimple component quotient,
using the native center calculation. No global simplicity theorem for the
J₄ carrier is assumed. The source wrappers discharge all prime-core inputs;
component uniqueness remains with the independent isolation argument.

Source: Aschbacher–Smith A.3.18, pp.51–52, and the terminal argument following
13.6.27, pp.934–935; GLS3 Table5.3i for the J₄ outer automorphism calculation.
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Components
open ChapterA.Section03.OddPrime.SourceModels.FourSporadic
variable {H : Type*} [Group H] [Finite H] {K : Subgroup H}

omit [Finite H] in
theorem jankoFour_quotient_center_eq_bot (e : (K ⧸ pCore 2 K) ≃* Janko4.Model) :
    center (K ⧸ pCore 2 K) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hz : e x ∈ center Janko4.Model := ((centerCongr e) ⟨x,hx⟩).property
  rw [Janko4.model_center_eq_bot,mem_bot] at hz
  exact e.map_eq_one_iff.mp hz

omit [Finite H] in
theorem jankoFour_quotient_isSimple [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : (K ⧸ pCore 2 K) ≃* Janko4.Model) : IsSimpleGroup (K ⧸ pCore 2 K) := by
  let := IsQuasisimple.simple (G := K ⧸ pCore 2 K)
  exact ((QuotientGroup.quotientMulEquivOfEq (jankoFour_quotient_center_eq_bot e)).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

/-- The original quotient has the simple Janko-four component as its whole generalized Fitting subgroup. -/
theorem jankoFour_generalizedFitting_eq [IsQuasisimple (K ⧸ pCore 2 K)]
    (hK : K.IsCComponent) (e : (K ⧸ pCore 2 K) ≃* Janko4.Model)
    (hthree : primeRank 3 H ≤ 2)
    (hu : ∀ D : Subgroup H, D.IsCComponent → D=K)
    (hlarge : ∀ p : ℕ, p.Prime → 3<p → pCore p (H ⧸ pCore 2 H)=⊥) :
    generalizedFitting (H ⧸ pCore 2 H) = componentImage K := by
  have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_congr 3 e]
    exact j4_three_rank_ge_two
  have h3 := hK.threeCore_twoCore_quotient_eq_bot
    (jankoFour_quotient_center_eq_bot e) hr hthree
  exact hK.generalizedFitting_twoCore_quotient_eq hu
    (fitting_twoCore_quotient_eq_bot h3 hlarge)

/-- Full innerness of Janko-four eliminates the remaining ambient quotient extension. -/
noncomputable def jankoFour_ambientQuotientEquiv [IsQuasisimple (K ⧸ pCore 2 K)]
    (hK : K.IsCComponent) (e : (K ⧸ pCore 2 K) ≃* Janko4.Model)
    (hthree : primeRank 3 H ≤ 2)
    (hu : ∀ D : Subgroup H, D.IsCComponent → D=K)
    (hlarge : ∀ p : ℕ, p.Prime → 3<p → pCore p (H ⧸ pCore 2 H)=⊥) :
    (H ⧸ pCore 2 H) ≃* Janko4.Model := by
  let eq := cComponentTwoCoreQuotientEquiv hK
  let : IsSimpleGroup (K ⧸ pCore 2 K) := jankoFour_quotient_isSimple e
  let : IsSimpleGroup (componentImage K) := eq.symm.isSimpleGroup
  exact ChapterE.JankoFour.ambientEquiv (componentImage K)
    (jankoFour_generalizedFitting_eq hK e hthree hu hlarge) (eq.symm.trans e)

open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- Apply the quotient identification to the actual singular centralizer, retaining only component uniqueness. -/
noncomputable def source_jankoFour_ambientQuotientEquiv
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K : Subgroup (centralizer (V₁ : Set G))} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : (K ⧸ pCore 2 K) ≃* Janko4.Model)
    (hu : ∀ D : Subgroup (centralizer (V₁ : Set G)), D.IsCComponent → D=K) :
    ((centralizer (V₁ : Set G)) ⧸ pCore 2 (centralizer (V₁ : Set G))) ≃* Janko4.Model := by
  let := d.elementary
  have hH := SourceAbelian.point_centralizer_mem_family d houtside
  have hsq := Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1
  exact jankoFour_ambientQuotientEquiv hK e
    (hsq.stronglyQuasithin 3 (by decide) (by decide)) hu
    (fun p hp hlarge => source_quotient_pCore_eq_bot_of_context_knownSimple d hCv
      houtside hcounter (Ratio.residualCentralizer L V₁) _ hH p hp hlarge)

/-- The same actual quotient inherits simplicity from the original quasisimple component. -/
theorem source_jankoFour_ambientQuotient_isSimple
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K : Subgroup (centralizer (V₁ : Set G))} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (e : (K ⧸ pCore 2 K) ≃* Janko4.Model)
    (hu : ∀ D : Subgroup (centralizer (V₁ : Set G)), D.IsCComponent → D=K) :
    IsSimpleGroup ((centralizer (V₁ : Set G)) ⧸ pCore 2 (centralizer (V₁ : Set G))) := by
  let : IsSimpleGroup (K ⧸ pCore 2 K) := jankoFour_quotient_isSimple e
  let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
  exact (source_jankoFour_ambientQuotientEquiv d hCv houtside hcounter hK e hu).isSimpleGroup
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
