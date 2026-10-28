module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.ResidualDirections
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Residual
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.CentralizerAction.PlaneImage
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# Excluding the second choice in the L₃(2) residual argument

Put K = O²(C_Y(V)), using the original Y. In CaseTwo, taking the residual
centralizer of V₁ first and then the residual centralizer of V₂ gives K.
The actual cubic action and |Y₊/O₂(Y₊)| = 9 therefore give |K|₃ = 3.
Normality of Y in M and M-invariance of V make K normal in M, hence
S-invariant and normal in Y₊. The rank-two shadow identifies this direction
with Y_C because [V,Y_L] is nontrivial.

The residual K has nontrivial two-core: K is nontrivial and inherits
characteristic two from M. Maximal two-locality now gives N_G(K) = M.
The previously proved component normalization of Y_C contradicts L ≰ M,
so the actual choice in Hypothesis 15.3.10 must be Y₊ = Y.

This is the second-choice reduction in 15.3.23. Its inputs are the genuine
15.3.7 action image, 15.3.11 rank-two shadow and core equality, 15.3.12
residual directions, generation and order-nine quotient, and the earlier
nontrivial action [V,Y_L] ≠ 1. The L₃(2) model and the characteristic-two
hypothesis on I are used upstream to produce these inputs; this deduction
works from their stated conclusions. S-invariance remains explicit through
ResidualDirection. The terminal theorem takes the actual ambient condition
(E) at T, which supplies characteristic two of M under CaseTwo.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7, 15.3.10–12 and 15.3.23, printed pp.1122–1125 and 1128,
especially the penultimate paragraph of p.1128.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree
open CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G] [Finite G]

private theorem le_twoResidual_of_perfect {A B : Subgroup G}
    (hAB : A ≤ B) (hA : IsPPerfect 2 A) : A ≤ Stellmacher.twoResidualAmbient B := by
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  have h := embedded_pResidual_mono 2 hAB
  rwa [(pResidual_eq_top_iff 2 A).mpr hA, ← MonoidHom.range_eq_map, range_subtype] at h

private theorem twoResidual_mono {A B : Subgroup G} (hAB : A ≤ B) :
    Stellmacher.twoResidualAmbient A ≤ Stellmacher.twoResidualAmbient B := by
  simp only [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  exact embedded_pResidual_mono 2 hAB

/-- The literal centralizing residual of the original Y is unchanged by first
passing to the residual centralizer of V₁ and then centralizing V₂. -/
theorem caseTwo_centralizing_residual_eq (d : LocalData G)
    (hcase : CaseTwo d.M d.Y d.S d.V₁ d.Yplus) :
    centralizingFactor d.Y d.V = centralizingFactor d.Yplus d.V₂ := by
  have hplus : d.Yplus = centralizingFactor d.Y d.V₁ := hcase.2
  have hplusY : d.Yplus ≤ d.Y := hplus ▸ centralizingFactor_le_left _ _
  have hplusC : d.Yplus ≤ centralizer (d.V₁ : Set G) := hplus ▸ centralizingFactor_le _ _
  have hKplus : centralizingFactor d.Y d.V ≤ d.Yplus := by
    rw [hplus]
    exact twoResidual_mono (inf_le_inf_left _ (centralizer_le (d.action.plane_le 1)))
  apply le_antisymm
  · exact le_twoResidual_of_perfect
      (le_inf hKplus ((centralizingFactor_le _ _).trans
        (centralizer_le (d.action.plane_le (Multiplicative.ofAdd (1 : ZMod 2))))))
      (centralizingFactor_isPPerfect _ _)
  · have hB1 : centralizingFactor d.Yplus d.V₂ ≤ centralizer (d.V₁ : Set G) :=
      (centralizingFactor_le_left _ _).trans hplusC
    have hBV : centralizingFactor d.Yplus d.V₂ ≤ centralizer (d.V : Set G) := by
      apply le_centralizer_iff.mpr
      apply (natural_planes_sup d.action (by decide :
        (1 : OrthogonalPlaneIndex) ≠ Multiplicative.ofAdd (1 : ZMod 2))).ge.trans
      exact sup_le (le_centralizer_iff.mp hB1)
        (le_centralizer_iff.mp (centralizingFactor_le _ _))
    exact le_twoResidual_of_perfect
      (le_inf ((centralizingFactor_le_left _ _).trans hplusY) hBV)
      (centralizingFactor_isPPerfect _ _)

/-- M preserves the literal residual, since it preserves both Y and V. -/
theorem M_normalizes_centralizing_residual (d : LocalData G) :
    d.M ≤ normalizer (centralizingFactor d.Y d.V : Set G) := by
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  exact normalizes_centralizingFactor
    ((normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal _ _))
    d.action.normalizes

/-- The literal residual is a genuine invariant direction in the second choice. -/
theorem caseTwo_centralizing_residual_direction (d : LocalData G)
    (hcase : CaseTwo d.M d.Y d.S d.V₁ d.Yplus)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9) :
    ResidualDirection d.Yplus d.S (centralizingFactor d.Y d.V) := by
  have he := caseTwo_centralizing_residual_eq d hcase
  have hplusM : d.Yplus ≤ d.M :=
    (yplus_le_residualY_of_choice d.choice).trans (Chapter14.SourcePreliminaries.sourceResidual_le _ _)
  have hn := M_normalizes_centralizing_residual d
  refine ⟨he ▸ centralizingFactor_le_left _ _,
    normal_subgroupOf_of_le_normalizer (hplusM.trans hn),
    (inf_le_left.trans d.sylow_le).trans hn, centralizingFactor_isPPerfect _ _, ?_⟩
  rw [he]
  exact (caseTwo_action_of_full_image d.action (by decide :
    (1 : OrthogonalPlaneIndex) ≠ Multiplicative.ofAdd (1 : ZMod 2)) hcase h7 h9).1

/-- In the second choice, Y_C is O²(C_Y(V)), formed using the original Y. -/
theorem caseTwo_YC_eq_centralizing_residual (d : LocalData G) (L : Subgroup G)
    (hcase : CaseTwo d.M d.Y d.S d.V₁ d.Yplus)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9)
    (hshadow : RankTwoShadow d.Yplus d.S)
    (hL : ResidualDirection d.Yplus d.S (YL d L))
    (hC : ResidualDirection d.Yplus d.S (YC d L))
    (hgen : d.Yplus = YL d L ⊔ YC d L)
    (hne : ⁅d.V, YL d L⁆ ≠ ⊥) :
    YC d L = centralizingFactor d.Y d.V := by
  exact (centralizing_direction_eq_YC d L _ h9 hshadow hL hC hgen
    (caseTwo_centralizing_residual_direction d hcase h7 h9)
    (centralizingFactor_le _ _) hne).symm

private theorem normal_core_ne_bot {M K : Subgroup G} (hKM : K ≤ M)
    (hn : (K.subgroupOf M).Normal)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) (hne : K ≠ ⊥) :
    K.pCoreIn 2 ≠ ⊥ := by
  let := hn
  have hK := (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe hKM)).mp (normal_core_selfCentralizing hc (K.subgroupOf M))
  intro hb
  have hb' : pCore 2 K = ⊥ :=
    ((pCore 2 K).map_eq_bot_iff_of_injective K.subtype_injective).mp hb
  apply hne
  apply (eq_bot_iff_forall K).mpr
  intro x hx
  have hm : (⟨x, hx⟩ : K) ∈ pCore 2 K := hK (by
    intro y hy
    have hy1 : y = 1 := mem_bot.mp (hb' ▸ hy)
    simp only [hy1, one_mul, mul_one])
  have hx1 : (⟨x, hx⟩ : K) = 1 := mem_bot.mp (hb' ▸ hm)
  exact congrArg Subtype.val hx1

/-- The residual has nontrivial two-core: its cubic part makes it nontrivial,
and its normality in the characteristic-two group M gives characteristic two. -/
theorem caseTwo_centralizing_residual_twoCore_ne_bot (d : LocalData G)
    (hcase : CaseTwo d.M d.Y d.S d.V₁ d.Yplus)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9)
    (hM : centralizer (pCore 2 d.M : Set d.M) ≤ pCore 2 d.M) :
    (centralizingFactor d.Y d.V).pCoreIn 2 ≠ ⊥ := by
  have hKM : centralizingFactor d.Y d.V ≤ d.M :=
    (centralizingFactor_le_left _ _).trans
      (Chapter14.SourcePreliminaries.sourceResidual_le _ _)
  apply normal_core_ne_bot hKM
    (normal_subgroupOf_of_le_normalizer (M_normalizes_centralizing_residual d)) hM
  intro hb
  have h3 := (caseTwo_centralizing_residual_direction d hcase h7 h9).three_part
  rw [hb] at h3
  norm_num at h3

/-- The normalizer of the literal residual is M. Maximal two-locality comes
from the genuine uniqueness clause of CaseTwo, and the nontrivial core is proved. -/
theorem caseTwo_centralizing_residual_normalizer (d : LocalData G)
    (hcase : CaseTwo d.M d.Y d.S d.V₁ d.Yplus)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9)
    (hM : centralizer (pCore 2 d.M : Set d.M) ≤ pCore 2 d.M) :
    normalizer (centralizingFactor d.Y d.V : Set G) = d.M := by
  have hKM : centralizingFactor d.Y d.V ≤ d.M :=
    (centralizingFactor_le_left _ _).trans
      (Chapter14.SourcePreliminaries.sourceResidual_le _ _)
  exact normalizer_eq_of_nontrivial_core d.M _ _ hKM hcase.1.1
    (normal_subgroupOf_of_le_normalizer (M_normalizes_centralizing_residual d))
    (caseTwo_centralizing_residual_twoCore_ne_bot d hcase h7 h9 hM) le_rfl

/-- The literal-residual identification and normalizer bound contradict the
 outside component's normalization of Y_C. -/
theorem not_caseTwo_of_residual_directions (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9)
    (hshadow : RankTwoShadow d.Yplus d.S)
    (hL : ResidualDirection d.Yplus d.S (YL d c.L))
    (hC : ResidualDirection d.Yplus d.S (YC d c.L))
    (hgen : d.Yplus = YL d c.L ⊔ YC d c.L)
    (hne : ⁅d.V, YL d c.L⁆ ≠ ⊥)
    (hE : IsEvenCharacteristicAt d.T)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    ¬ CaseTwo d.M d.Y d.S d.V₁ d.Yplus := by
  intro hcase
  have hM := hE d.M hcase.1.1 d.sylow_le
  apply YC_normalizer_not_le_M d c hcore hR hC.invariant
  rw [caseTwo_YC_eq_centralizing_residual d c.L hcase h7 h9 hshadow hL hC hgen hne,
    caseTwo_centralizing_residual_normalizer d hcase h7 h9 hM]

/-- Therefore the actual choice in Hypothesis 15.3.10 is its first choice. -/
theorem yplus_eq_Y_of_residual_directions (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (h7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h9 : Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9)
    (hshadow : RankTwoShadow d.Yplus d.S)
    (hL : ResidualDirection d.Yplus d.S (YL d c.L))
    (hC : ResidualDirection d.Yplus d.S (YC d c.L))
    (hgen : d.Yplus = YL d c.L ⊔ YC d c.L)
    (hne : ⁅d.V, YL d c.L⁆ ≠ ⊥)
    (hE : IsEvenCharacteristicAt d.T)
    (hcore : c.L.pCoreIn 2 ≤ d.R)
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    d.Yplus = d.Y := by
  exact d.choice.resolve_right
    (not_caseTwo_of_residual_directions d c h7 h9 hshadow hL hC hgen hne hE hcore hR)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree

end
