module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Thompson.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OriginalResidualImage
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceResidualFlags

/-!
# The original rank-four centralizer contradiction

The selected source configuration supplies simultaneous intrinsic and plus
SL₄(2) markings. Complete B.5.1 gives its actual natural moved section and
marks the seed stabilizer with the same actor. The residual of the component
centralizer and the actual Sylow image generate the marked four-block group.
Transport to the internal seed span therefore proves the Thompson equality
used in the final paragraph after 13.6.23.

The original flag identifies the invariant plane, the selected component is
O^{3′}(G_v), and source 13.6.16(1) gives the vanishing join-core. Together these
contradict the nontrivial Thompson subgroup. Constructing a Y_z member from
failed containment then gives the original nonsingular centralizer bound.

No orthogonal-module, local-image, Thompson or classification callback remains
in this endgame. The genuine earlier flag/local and fusion inputs, 13.3.2,
13.6.3 and the reduced SL₄/SL₅ list remain explicit; the final export also
discharges the redundant SL₃ exclusion by comparing group orders. In
particular this is the rank-four branch, not an unconditional 13.6.7 proof.

Source: Aschbacher--Smith, 13.6.23 and its concluding paragraph, printed p.933,
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
open LocalAction LocalAction.OrthogonalModule
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

private theorem not_linearThree_of_four_or_five
    {B : Type u} [Group B]
    (hb : Nonempty (B ≃* SL(4,ZMod 2)) ∨ Nonempty (B ≃* SL(5,ZMod 2))) :
    ¬ Nonempty (B ≃* SL(3,ZMod 2)) := by
  rintro ⟨e3⟩
  rcases hb with h4 | h5
  · obtain ⟨e4⟩ := h4
    have hc := Nat.card_congr (e4.symm.trans e3).toEquiv
    rw [Atlas.Order20160A8.sl4Two_card, Matrix.PSL3Two.card_SL] at hc
    omega
  · obtain ⟨e5⟩ := h5
    have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    rw [Nat.card_zmod] at h
    have hp : (∏ i : Fin 5, (2 ^ 5 - 2 ^ i.val)) = 9999360 := by decide
    rw [show Nat.gcd 5 (2 - 1) = 1 by decide, show 2 - 1 = 1 from rfl,
      mul_one, mul_one, hp] at h
    have he := Nat.card_congr (e5.symm.trans e3).toEquiv
    rw [Matrix.PSL3Two.card_SL] at he
    have hc := Nat.card_congr (binaryProjectiveEquiv 5 (by decide)).toEquiv
    omega

variable
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (hsmall : ∀ B ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module),
      ¬ Nonempty (plusImage B L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz B ≃* SL(3, ZMod 2)))
    (hmodels : ∀ B ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module),
      Nonempty (plusImage B L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz B ≃* SL(4, ZMod 2)) ∨
      Nonempty (plusImage B L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz B ≃* SL(5, ZMod 2)))
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))

include d V₃ earlier standing hm hfusion hform hfailure h1332 h63 hL hz hsmall hmodels hK

/-- The original selected rank-four component contradicts the source
join-core vanishing, with the local image and Thompson comparison proved. -/
theorem false_of_original_rankFour_source : False := by
  obtain ⟨c,⟨eK⟩⟩ := action_configuration_of_original_source d V₃ earlier standing hm
    hfusion hform hfailure h1332 h63 hL hz hsmall hmodels hK
  let := c.elementary
  obtain ⟨m,_,_,_,hseed,_,_⟩ :=
    source_orthogonal_seed_marking c SourceB5.classification.quasisimple
  have hJ := Thompson.source_thompson_eq_of_movedSection c eK m
    (source_residual_join_image c m hseed)
  apply Source.false_of_flag_residual_thompson_comparison d d.flag K c.residual
    d.flag_centralizer_index hJ
  exact (c.earlier_control K c.selected.1 c.invariant
    (fun h => c.seed_moved (c.lv_le.trans h))).1

omit hfailure hK in
/-- The surviving rank-four source branch supplies the original nonsingular
centralizer containment, with the actual selected component constructed. -/
theorem centralizer_le_normalizer_of_original_rankFour_source :
    Gv (markedV d.flag.module) ≤ normalizer (V : Set G) := by
  by_contra hfailure
  obtain ⟨K,_,_,_,hK⟩ := exists_mem_Yz_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion hform hfailure
  exact false_of_original_rankFour_source d V₃ earlier standing hm hfusion hform hfailure
    h1332 h63 hL hz hsmall hmodels hK

omit hfailure hK hsmall in
/-- Once the original selected quotient catalogue is reduced to SL₄/SL₅,
its orders also discharge the forbidden SL₃ replacement. -/
theorem centralizer_le_normalizer_of_original_reduced_models :
    Gv (markedV d.flag.module) ≤ normalizer (V : Set G) := by
  apply centralizer_le_normalizer_of_original_rankFour_source d V₃ earlier standing hm
    hfusion hform h1332 h63 hL hz _ hmodels
  intro B hB
  exact not_linearThree_of_four_or_five (hmodels B hB)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal
