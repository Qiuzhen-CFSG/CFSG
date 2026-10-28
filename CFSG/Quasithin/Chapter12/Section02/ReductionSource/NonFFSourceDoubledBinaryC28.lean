module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryReciprocalObstruction
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Radical

/-!
# The whole doubled orbit as a C.2.8 module

The reciprocal-obstruction witness retains the complete marked doubled source
orbit.  In the degree-three natural model its section centralizer centralizes
that whole orbit, so the literal witness can be repackaged as the source
C.2.8 pushing-up hypothesis.  This is the interface consumed by C.4.8 and
4.2.13; no scalar-only module surrogate is used.

Source: Aschbacher--Smith C.2.8 and C.4.8, printed pp.147 and 153--154.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource Representation Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem orbit_core_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    L.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) := by
  apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
  simpa only [D.fundamentalSetup_module,Chapter3.Section02.localJoin,D.localOrbit_eq,
    D.sourceOrbit_eq] using (D.fundamentalSetup h.toHypothesis1221).core_centralizes_module

/-- The section centralizer centralizes the retained six-dimensional source
orbit in the degree-three natural model. -/
theorem sourceOrbit_binary_sectionCentralizer_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    sectionCentralizer L ≤ centralizer (D.sourceOrbit : Set G) := by
  let W := D.sourceOrbit
  let N := normalizer (W : Set G)
  let φ := W.normalizerMonoidHom
  have hC := (le_sectionCentralizer_iff (sectionCentralizer L) L).mp le_rfl
  have hCW := hC.1.trans (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge
  have hQC := D.orbit_core_centralizes h
  intro x hx
  let xN : N := ⟨x,hCW hx⟩
  have hc (l : L) : Commute (φ xN) (φ (inclusion D.sourceOrbit_component_normalizes l)) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [←map_commutatorElement]
    ext w
    change ⁅x,(l : G)⁆ * (w : G) * ⁅x,(l : G)⁆⁻¹ = (w : G)
    exact mul_inv_eq_iff_eq_mul.mpr
      (hQC (hC.2 (commutator_mem_commutator hx l.property)) w w.property).symm
  let a := (φ xN).toAdditive
  let f : Additive W ≃ₗ[ZMod 2] Additive W :=
    a.toLinearEquiv (fun c v => ZMod.map_smul a.toAddMonoidHom c v)
  have hf : f = LinearEquiv.refl _ _ := D.sourceOrbit_binary_centralizer_eq_one
    h hd F hF hmodel f (by
      intro l v
      exact congrArg (fun b : MulAut W => Additive.ofMul (b v.toMul)) (hc l).eq)
  intro w hw
  have hh := LinearEquiv.congr_fun hf (Additive.ofMul (⟨w,hw⟩ : W))
  have he : x * w * x⁻¹ = w := congrArg (fun v : Additive W => (v.toMul : G)) hh
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Repackage the literal reciprocal-obstruction witness as C.2.8, with the
whole doubled source orbit as the module. -/
theorem sourceOrbit_binary_witness_hypothesisC28
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G)) LH (J.pCoreIn 2) D.sourceOrbit := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := hw.2.2.2.2.2.2.1
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy LH (H ⊓ normalizer (L : Set G)) = LH :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  have hmove : D.sourceOrbit = ⁅D.sourceOrbit,LH⁆ := by
    have hm := D.doubledOrbit_commutator_component h
    rw [←D.sourceOrbit_eq] at hm
    exact hm.trans (commutator_eq_of_product_centralizing_factor
      hw.2.2.2.2.2.2.2.1 (le_centralizer_iff.mp (D.orbit_core_centralizes h)))
  have hWL : D.sourceOrbit ≤ LH := by
    rw [hmove]
    exact le_normalizer_iff_commutator_le_right.mp ((hWJ.trans hc.radical_le).trans hn)
  have hWR : D.sourceOrbit ≤ (center (J.pCoreIn 2)).map (J.pCoreIn 2).subtype := by
    intro w hwW
    refine ⟨⟨w,hWJ hwW⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro r
    apply Subtype.ext
    exact (D.sourceOrbit_binary_sectionCentralizer_centralizes h hd F hF hmodel
      (hJC r.property).2 w hwW).symm
  refine ⟨hc.sqtk,hc.radical_isTwoGroup,hc.radical_le,hc.local_le,hc.local_fitting,
    hc.core_nontrivial,hc.component_le,hc.component,hc.section_sylow,
    hc.characteristic_control,D.sourceOrbit_weakClosure_setup.nontrivial,inferInstance,
    hWL.trans (le_conjugateSpanBy _ _),?_,?_,?_⟩
  · rw [hspan]
    exact hmove
  · rw [hc.span_join_core]
    exact hWR
  · rw [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]

/-- The original multiple-overgroup obstruction supplies C.2.8 on the whole
orbit and the actual escaping generalized-Fitting preimage.  The independent
native J₄ cover is the sole added premise. -/
theorem sourceOrbit_binary_reciprocal_hypothesisC28_of_janko_cover
    (hnative : Janko4.LocalStructure.LargeCenterRadicals.MaximalTwoLocalCover)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : D.SourceOrbitNonFF)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
        A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ J P W : Subgroup G, Witness L V A J P W ∧
          D.sourceOrbit ≤ J.pCoreIn 2 ∧
          J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L ∧
          ChapterC.HypothesisC28 KnownSimple.IsKnownSimple P
            (P ⊓ normalizer (L : Set G))
            ((solvableResidual (L ⊓ P : Subgroup G)).map (L ⊓ P).subtype)
            (J.pCoreIn 2) D.sourceOrbit ∧
          ¬ (generalizedFitting (P ⧸ pCore 2 P)).comap
            (QuotientGroup.mk' (pCore 2 P)) ≤ (normalizer (L : Set G)).subgroupOf P := by
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hnot,J,P,W,hw,hWJ,hJC,hescape⟩ :=
    D.sourceOrbit_binary_reciprocal_obstruction_of_janko_cover
      hnative h hd hmany hnon F hF hmodel
  exact ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hnot,J,P,W,hw,hWJ,hJC,
    D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC,hescape⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
