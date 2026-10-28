module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalControl
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.Geometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.SecondAction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.SpanIntersection
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OrthogonalImage.Displacement
public import Theory.GroupTheory.SylowLocalCore

/-!
# Local branches in the outside-overgroup lemma

In the first choice, the preceding residual-module calculation gives the
nontrivial commutator on V. This establishes the Sylow conclusion before any
use of it in the core argument. The earlier span identity also proves (2),
and the earlier normalizer identity proves (4).

For the rank-two core, the identity R=C_T(V) puts the entire M∩I-conjugate
span of R inside C_G(V). Sylow restriction to that normal span then proves
the required Sylow membership directly. The normalizer-core equality is a
general property of the core of a Sylow overgroup. Thus this specialization
does not require the as-yet unavailable general C.1.2(4).

The second-choice cubic span and residual-intersection calculation discharge
the premises of the quotient and theta calculation. `local_branches` assembles
all of (1)–(6), including the complete alternatives `RankTwoCase` and
`RankOneCase`. It derives the first-choice commutator from the earlier action
image and proves the Sylow witness before using any core calculation.
`chosen_action` supplies the specified elementary module W=V or W=V₂,
its normalizer control, and noncentrality on V and U_I for (8) and (9).

Only exact earlier 15.3.2–9 outputs remain inputs. Their discharge belongs
to the enclosing Preliminaries assembly; the remaining six clauses of
15.3.11 belong to OutsideStructure. No current structural conclusion or
inhabitant of `Conclusions` is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(1)–(6), printed pp.1123–1124.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches
variable {G : Type*} [Group G] [Finite G]

/-- All the module and action facts in the first choice. The two action
inputs are the equalities proved in the argument for 15.3.7. -/
theorem first_choice_action (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (hfirst : d.Yplus = d.Y)
    (hcomm : ⁅d.V, d.Y⁆ = d.V) (hspan : localSpan d.Z d.Y = d.V) :
    d.V ≠ ⊥ ∧ d.V ≤ I ∧ IsElementaryAbelian 2 d.V ∧
      d.V = ⁅d.V, d.Yplus⁆ ∧ d.V ≤ localSpan d.Z d.Yplus ∧
      ¬ d.Yplus ≤ centralizer (d.V : Set G) ∧
      ¬ d.Yplus ≤ centralizer (d.UI I : Set G) := by
  have he : ⁅d.V, d.Yplus⁆ = d.V := by rw [hfirst, hcomm]
  have hn : ⁅d.V, d.Yplus⁆ ≠ ⊥ := by rw [he]; exact v_ne_bot d
  have hs : d.V ≤ localSpan d.Z d.Yplus := by rw [hfirst, hspan]
  refine ⟨v_ne_bot d, v_le_outside d I hI, d.action.elementary,
    he.symm, hs, ?_, ?_⟩
  · intro hc
    exact hn (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  · exact not_centralizing_localSpan d.Z d.Yplus I d.V
      (le_sup_left.trans hI.1.2) hs hn

/-- The first-choice Sylow conclusion uses noncentrality already proved
from 15.3.7. The remaining inputs are exactly 15.3.2(4) and 15.3.6(2). -/
theorem first_choice_sylow (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (hfirst : d.Yplus = d.Y)
    (hcomm : ⁅d.V, d.Y⁆ = d.V)
    (hNS : normalizer (d.S : Set G) ≤ d.M)
    (h24 : ∀ X : Subgroup G, (d.T : Subgroup G) ≤ X → X ≤ d.M →
      twoResidualAmbient X ≤ d.M ⊓ centralizer (d.V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X d.M) :
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S := by
  have hact : ¬ d.Yplus ≤ centralizer (d.V : Set G) := by
    intro hc
    apply v_ne_bot d
    rw [← hcomm, ← hfirst]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
  exact lemma_15_3_11_1_of_action d.T d.M d.V d.Yplus d.S I d.sylow_le
    ((choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice).trans
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)) inf_le_left
    (d.action.planeStabilizer_index_two d.T d.sylow_le 1) hNS d.action.normalizes
    h24 (chosen_residual_eq d.M d.Mc d.S d.V₁ d.Yplus d.choice) hact hI

/-- Clause (1) for both choices, from earlier 15.3.2, 15.3.6 and 15.3.7
outputs. Neither branch assumes a local structural conclusion of 15.3.11. -/
theorem chosen_sylow (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus)
    (hcomm : ⁅d.V, d.Y⁆ = d.V)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hNS : normalizer (d.S : Set G) ≤ d.M)
    (h24 : ∀ X : Subgroup G, (d.T : Subgroup G) ≤ X → X ≤ d.M →
      twoResidualAmbient X ≤ d.M ⊓ centralizer (d.V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X d.M) :
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S := by
  rcases d.choice with hfirst | hsecond
  · exact first_choice_sylow d I hI hfirst hcomm hNS h24
  · exact second_choice_sylow d I hI hsecond h7image hNS h24

omit [Finite G] in
/-- Clauses (2) and (4) in the first choice, from the earlier span and
normalizer identities. -/
theorem first_choice_centralizer_and_normalizer (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (hfirst : d.Yplus = d.Y)
    (hspan : localSpan d.Z d.Y = d.V)
    (hNV : normalizer (d.V : Set G) = d.M)
    (hNY : normalizer (d.Y : Set G) = d.M) :
    I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I ∧
      I ⊓ normalizer (d.Yplus : Set G) = d.MI I := by
  change I ∈ outsideFamily d.Yplus d.S d.M at hI
  rw [hfirst] at hI ⊢
  exact first_choice_centralizer_normalizer d.Z d.Y d.S d.M I d.V hI hspan hNV hNY

/-- The local two-core contains the entire elementary module in either choice. -/
theorem v_le_r (d : CharacteristicTwo.LocalData G) : d.V ≤ d.R := by
  let _ := d.action.elementary
  apply le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 d.V)
    ((v_le_s d).trans le_sup_right)
  exact (sup_le ((choice_le d.M d.Y d.S d.V₁ d.Yplus d.choice).trans
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc))
    (inf_le_left.trans d.sylow_le)).trans d.action.normalizes

theorem r_ne_bot (d : CharacteristicTwo.LocalData G) : d.R ≠ ⊥ :=
  fun h => v_ne_bot d (le_bot_iff.mp (h ▸ v_le_r d))

omit [Finite G] in
/-- The established Sylow witness bounds the local core by S. -/
theorem r_le_s (d : CharacteristicTwo.LocalData G) (I : Subgroup G)
    (hI : I ∈ d.Hplus)
    (hSyl : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S) : d.R ≤ d.S := by
  obtain ⟨P, hP⟩ := hSyl
  obtain ⟨Q, hQ⟩ := P.exists_map_subtype_eq_of_le hI.1.2
    (hP.le.trans le_sup_right)
  exact (pCoreIn_le_sylow (d.Yplus ⊔ d.S) Q).trans_eq (hQ.trans hP)

omit [Finite G] in
/-- The core-normalizer equality in (5i) follows directly from the Sylow
witness and R=O₂(Y₊S), in both choices. -/
theorem r_eq_normalizer_core (d : CharacteristicTwo.LocalData G) (I : Subgroup G)
    (hI : I ∈ d.Hplus)
    (hSyl : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S) :
    d.R = (I ⊓ normalizer (d.R : Set G)).pCoreIn 2 := by
  obtain ⟨P, hP⟩ := hSyl
  exact (pCoreIn_normalizer_eq_of_sylow_le P hI.1.2
    (hP.le.trans le_sup_right)).symm

/-- The literal R=C_T(V) identity makes R Sylow in its M∩I-conjugate span.
Only the identity and the already established Sylow witness are needed. -/
theorem rankTwo_sylow_span (d : CharacteristicTwo.LocalData G) (I : Subgroup G)
    (hI : I ∈ d.Hplus)
    (hSyl : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    ∃ Q : Sylow 2 (localSpan d.R (d.MI I)),
      (Q : Subgroup _).map (localSpan d.R (d.MI I)).subtype = d.R := by
  have hRS := r_le_s d I hI hSyl
  have hSMI : d.S ≤ d.MI I :=
    le_inf (inf_le_left.trans d.sylow_le) (le_sup_right.trans hI.1.2)
  have hspan : localSpan d.R (d.MI I) ≤ d.MI I :=
    conjugateSpanBy_le_self (hRS.trans hSMI)
  have hcentral : localSpan d.R (d.MI I) ≤ centralizer (d.V : Set G) :=
    conjugateSpanBy_le (hR.le.trans inf_le_right)
      ((inf_le_left.trans d.action.normalizes).trans
        (normalizer_le_normalizer_centralizer d.V))
  obtain ⟨P, hP⟩ := hSyl
  obtain ⟨PM, hPM⟩ := P.exists_map_subtype_eq_of_le
    (show d.MI I ≤ I from inf_le_right) (hP ▸ hSMI)
  obtain ⟨Q, hQ⟩ := PM.exists_map_subtype_eq_inf_of_normalizes hspan
    (le_normalizer_conjugateSpanBy _ _)
  refine ⟨Q, hQ.trans ?_⟩
  rw [hPM, hP]
  apply le_antisymm
  · exact (le_inf (inf_le_left.trans (show d.S ≤ (d.T : Subgroup G) from inf_le_left))
      (inf_le_right.trans hcentral)).trans hR.ge
  · exact le_inf hRS (le_conjugateSpanBy _ _)

/-- Earlier O₂(YT)=C_T(V) and uniqueness of YT supply relative normality
and all characteristic-normalizer control once R=C_T(V) is calculated. -/
theorem rankTwo_characteristic_control (d : CharacteristicTwo.LocalData G)
    (h7core : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (h7unique : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ (d.T : Subgroup G)) d.M)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    (d.R.subgroupOf (d.Y ⊔ (d.T : Subgroup G))).Normal ∧
      normalizer (d.R : Set G) ≤ d.M ∧ d.R.characteristicNormalizerClosure ≤ d.M := by
  have hn : d.Y ⊔ (d.T : Subgroup G) ≤ normalizer (d.R : Set G) := by
    rw [hR, ← h7core]
    exact (d.Y ⊔ (d.T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hp : IsPGroup 2 d.R := isPGroup_pCoreIn 2 _
  exact ⟨normal_subgroupOf_of_le_normalizer hn,
    normalizer_le_of_unique_maximalTwoLocal h7unique.2.2 hp (r_ne_bot d) hn,
    characteristicNormalizerClosure_le_of_unique_maximalTwoLocal h7unique.2.2 hp hn⟩

omit [Finite G] in
private theorem earlier_quotient_isPGroup (d : CharacteristicTwo.LocalData G)
    (h7 : QuotientTheta.EarlierThreeAlternatives d) : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y) :=
  fun x => ⟨1, by simpa only [pow_one] using QuotientTheta.earlier_quotient_cube d h7 x⟩

/-- The second choice supplies W=V₂ with every module and action property
used in clauses (2), (8), and (9). -/
theorem second_choice_action (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (hsecond : SecondChoice d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7span : localSpan d.Z d.Y = d.V) :
    d.V₂ ≠ ⊥ ∧ d.V₂ ≤ I ∧ IsElementaryAbelian 2 d.V₂ ∧
      d.V₂ = ⁅d.V₂, d.Yplus⁆ ∧ d.V₂ ≤ localSpan d.Z d.Yplus ∧
      ¬ d.Yplus ≤ centralizer (d.V : Set G) ∧
      ¬ d.Yplus ≤ centralizer (d.UI I : Set G) := by
  exact ⟨plane_ne_bot d _, plane_le_outside d I hI _,
    d.action.elementary_of_le (d.action.plane_le _),
    (second_choice_commutator d hsecond h7image).2.symm,
    second_choice_plane_le_span d hsecond h7image h7span,
    second_choice_noncentral d hsecond h7image,
    second_choice_noncentral_ui d I hsecond h7image h7span⟩

/-- Choose the source module W=V in the first choice and W=V₂ in the
second. Its ambient normalizer controls the centralizer used in the
odd-core argument; its commutator and span give the nontrivial star action.
Only the earlier 15.3.7 action facts and N_G(V)=M remain inputs. -/
theorem chosen_action (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7span : localSpan d.Z d.Y = d.V)
    (hNV : normalizer (d.V : Set G) = d.M) :
    ∃ W : Subgroup G,
      ((d.Yplus = d.Y ∧ W = d.V) ∨ (SecondChoice d ∧ W = d.V₂)) ∧
      W ≠ ⊥ ∧ W ≤ I ∧ IsElementaryAbelian 2 W ∧ W = ⁅W, d.Yplus⁆ ∧
      W ≤ localSpan d.Z d.Yplus ∧ normalizer (W : Set G) ≤ d.M ∧
      ¬ d.Yplus ≤ centralizer (d.V : Set G) ∧
      ¬ d.Yplus ≤ centralizer (d.UI I : Set G) := by
  have hcomm := d.action.commutator_eq_of_residual_image d.Y
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) h7image
  rcases d.choice with hfirst | hsecond
  · obtain ⟨hne, hle, hel, hc, hs, hnV, hnU⟩ :=
      first_choice_action d I hI hfirst hcomm h7span
    exact ⟨d.V, Or.inl ⟨hfirst, rfl⟩, hne, hle, hel, hc, hs, hNV.le, hnV, hnU⟩
  · obtain ⟨hne, hle, hel, hc, hs, hnV, hnU⟩ :=
      second_choice_action d I hI hsecond h7image h7span
    exact ⟨d.V₂, Or.inr ⟨hsecond, rfl⟩, hne, hle, hel, hc, hs,
      (second_choice_normalizers d hsecond h7image).2.1, hnV, hnU⟩

/-- All of clause (3), with the odd quotient required by the intersection
calculation derived from the genuine alternatives of 15.3.7. -/
theorem second_choice_structure (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (hsecond : SecondChoice d)
    (h7 : QuotientTheta.EarlierThreeAlternatives d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    d.Yplus = twoResidualAmbient (d.Y ⊓ I) ∧
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M ∧
      normalizer (d.Yplus : Set G) ≤ d.M :=
  ⟨second_choice_intersection_residual d I hI hsecond h7image
      (earlier_quotient_isPGroup d h7),
    second_choice_normalizers d hsecond h7image⟩

/-- Clauses (2) and (4) in both choices. The second choice uses the proved
cubic span and residual intersection, with no current structural input. -/
theorem chosen_centralizer_and_normalizer (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus)
    (h7 : QuotientTheta.EarlierThreeAlternatives d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7span : localSpan d.Z d.Y = d.V)
    (hNV : normalizer (d.V : Set G) = d.M)
    (hNY : normalizer (d.Y : Set G) = d.M) :
    I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I ∧
      I ⊓ normalizer (d.Yplus : Set G) = d.MI I := by
  rcases d.choice with hfirst | hsecond
  · exact first_choice_centralizer_and_normalizer d I hI hfirst h7span hNV hNY
  · exact ⟨second_choice_centralizer_le d I hI hsecond h7image h7span,
      second_choice_normalizer_eq d I hI hsecond h7image (earlier_quotient_isPGroup d h7)⟩

/-- The full structural alternative (5) and theta identity (6), after
clause (1) has been established. In the rank-two branch the core is normal
in YT, radical in its I-normalizer, and Sylow in its actual MI-conjugate
span. Characteristic-normalizer generation is the literal C(G,R). -/
theorem local_structure_and_theta_of_sylow (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus)
    (h7 : QuotientTheta.EarlierThreeAlternatives d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7core : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (h7unique : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ (d.T : Subgroup G)) d.M)
    (hSyl : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S) :
    (RankTwoCase d I ∨ RankOneCase d I) ∧ d.Yplus = theta (d.MI I) := by
  have hintersection (hsecond : SecondChoice d) :
      d.Yplus = twoResidualAmbient (d.Y ⊓ I) :=
    (second_choice_structure d I hI hsecond h7 h7image).1
  obtain ⟨htheta, halgebra⟩ :=
    QuotientTheta.quotient_and_theta d I hI h7 h7image h7core hSyl hintersection
  refine ⟨?_, htheta⟩
  rcases halgebra with ⟨hcubic, hquotient, hcore, hR⟩ | hone
  · obtain ⟨hnormal, _, hcontrol⟩ := rankTwo_characteristic_control d h7core h7unique hR
    exact Or.inl ⟨hcubic, hquotient, hcore, hnormal, hR,
      r_eq_normalizer_core d I hI hSyl, rankTwo_sylow_span d I hI hSyl hR, hcontrol⟩
  · exact Or.inr hone

/-- Clauses (1)–(6) of 15.3.11 from the genuine local construction and
the precise earlier 15.3.2–9 inputs. In particular, the Sylow witness is
proved from noncentral action before it is used in the core calculations.
The enclosing Preliminaries assembly supplies these earlier inputs;
no conclusion of the current lemma is assumed. -/
theorem local_branches (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus)
    (h7 : QuotientTheta.EarlierThreeAlternatives d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7span : localSpan d.Z d.Y = d.V)
    (h7core : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (h7unique : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ (d.T : Subgroup G)) d.M)
    (hNV : normalizer (d.V : Set G) = d.M)
    (hNY : normalizer (d.Y : Set G) = d.M)
    (hNS : normalizer (d.S : Set G) ≤ d.M)
    (h24 : ∀ X : Subgroup G, (d.T : Subgroup G) ≤ X → X ≤ d.M →
      twoResidualAmbient X ≤ d.M ⊓ centralizer (d.V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X d.M) :
    (∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S) ∧
      I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I ∧
      (SecondChoice d → d.Yplus = twoResidualAmbient (d.Y ⊓ I) ∧
        normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M ∧
        normalizer (d.Yplus : Set G) ≤ d.M) ∧
      I ⊓ normalizer (d.Yplus : Set G) = d.MI I ∧
      (RankTwoCase d I ∨ RankOneCase d I) ∧ d.Yplus = theta (d.MI I) := by
  have hcomm := d.action.commutator_eq_of_residual_image d.Y
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) h7image
  have hSyl := chosen_sylow d I hI hcomm h7image hNS h24
  obtain ⟨hcentralizer, hnormalizer⟩ :=
    chosen_centralizer_and_normalizer d I hI h7 h7image h7span hNV hNY
  exact ⟨hSyl, hcentralizer, fun hsecond => second_choice_structure d I hI hsecond h7 h7image,
    hnormalizer, local_structure_and_theta_of_sylow d I hI h7 h7image h7core h7unique hSyl⟩

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches
end
