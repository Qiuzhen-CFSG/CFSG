module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearRank
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Radical
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerReduction
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Ranks

/-!
# Original two-subgroup centralization for the nonbinary doubled row

A two-subgroup of the original component's section centralizer acts on
the whole orbit by commuting operators. The pair has no centralizing
involution, so induction on two-power order kills this action. Applying
this to the literal reciprocal radical places the whole original orbit
in its center and supplies C.2.8. Odd scalar centralizers are retained;
no assertion about the entire section centralizer is made.
Source: Aschbacher--Smith C.2.8, 4.1.4 and 7.3.4, printed pp.147,606–607,699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem two_power_trivial {A : Type*} [Group A]
    (hA : ∀ a : A, a^2=1 → a=1) (a : A) (n : ℕ) (hn : a^(2^n)=1) : a=1 := by
  induction n with
  | zero => simpa using hn
  | succ n ih =>
    apply ih
    apply hA
    rw [←pow_mul,←Nat.pow_succ]
    exact hn

private theorem orbit_core_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    L.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) := by
  apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
  simpa only [D.fundamentalSetup_module,Chapter3.Section02.localJoin,D.localOrbit_eq,
    D.sourceOrbit_eq] using (D.fundamentalSetup h.toHypothesis1221).core_centralizes_module

/-- Every actual two-subgroup of the section centralizer fixes the full linear-three orbit. -/
theorem sourceOrbit_linear_two_sectionCentralizer_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (P : Subgroup G) (hP : IsPGroup 2 P) (hPC : P ≤ sectionCentralizer L) :
    P ≤ centralizer (D.sourceOrbit : Set G) := by
  let W := D.sourceOrbit
  let N := normalizer (W : Set G)
  let φ := W.normalizerMonoidHom
  let C := centralizer ((φ.comp (inclusion D.sourceOrbit_component_normalizes)).range : Set (MulAut W))
  have hC := (le_sectionCentralizer_iff (sectionCentralizer L) L).mp le_rfl
  have hPW := (hPC.trans hC.1).trans (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge
  have hQC := D.orbit_core_centralizes h
  have hin (x : P) : φ (inclusion hPW x) ∈ C := by
    rintro _ ⟨l,rfl⟩
    apply (commutatorElement_eq_one_iff_commute.mp ?_).eq.symm
    simp only [MonoidHom.comp_apply]
    rw [←map_commutatorElement]
    ext w
    change ⁅(x : G),(l : G)⁆ * (w : G) * ⁅(x : G),(l : G)⁆⁻¹ = (w : G)
    exact mul_inv_eq_iff_eq_mul.mpr
      (hQC (hC.2 (commutator_mem_commutator (hPC x.property) l.property)) w w.property).symm
  let ψ : P →* C := (φ.comp (inclusion hPW)).codRestrict C hin
  have hkill (a : C) (hsq : a^2=1) : a=1 := by
    let b := a.val.toAdditive
    let f : Additive W ≃ₗ[ZMod 2] Additive W :=
      b.toLinearEquiv (fun c v => ZMod.map_smul b.toAddMonoidHom c v)
    have hf : f=LinearEquiv.refl _ _ := D.sourceOrbit_linear_involution_centralizer
      h hd F hmodel f (by
        intro v
        exact congrArg (fun z : C => Additive.ofMul (z.val v.toMul)) hsq) (by
        intro l v
        have hh := a.property (φ (inclusion D.sourceOrbit_component_normalizes l)) ⟨l,rfl⟩
        exact congrArg (fun z : MulAut W => Additive.ofMul (z v.toMul)) hh.symm)
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    exact congrArg Additive.toMul (LinearEquiv.congr_fun hf (Additive.ofMul v))
  intro x hx w hw
  obtain ⟨n,hn⟩ := hP.exists_pow_pow_eq_one (⟨x,hx⟩ : P)
  have hp : ψ ⟨x,hx⟩ = 1 := two_power_trivial hkill _ n (by rw [←map_pow,hn,map_one])
  have hh := congrArg (fun z : C => (z.val ⟨w,hw⟩ : G)) hp
  change x*w*x⁻¹=w at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Repackage the literal reciprocal-obstruction witness as C.2.8, with the
whole doubled source orbit as the module. -/
theorem sourceOrbit_linear_witness_hypothesisC28
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
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
    exact (D.sourceOrbit_linear_two_sectionCentralizer_centralizes h hd F hmodel
      (J.pCoreIn 2) (isPGroup_pCoreIn 2 J) (hJC.trans inf_le_right) r.property w hwW).symm
  refine ⟨hc.sqtk,hc.radical_isTwoGroup,hc.radical_le,hc.local_le,hc.local_fitting,
    hc.core_nontrivial,hc.component_le,hc.component,hc.section_sylow,
    hc.characteristic_control,D.sourceOrbit_weakClosure_setup.nontrivial,inferInstance,
    hWL.trans (le_conjugateSpanBy _ _),?_,?_,?_⟩
  · rw [hspan]
    exact hmove
  · rw [hc.span_join_core]
    exact hWR
  · rw [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
