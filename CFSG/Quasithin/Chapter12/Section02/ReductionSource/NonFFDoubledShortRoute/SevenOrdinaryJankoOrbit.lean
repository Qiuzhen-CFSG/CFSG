module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.AlternatingPushingUp
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSevenCoordinates
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Radical

/-!
# C.2.8 on the actual doubled A₇ orbit

The original conjugator-twisted faithful A₇ four-spaces are inequivalent.
Their checked trivial invertible commutant makes the original component's
section centralizer centralize the whole doubled orbit. The reciprocal
witness's actual mu-star membership puts its two-core in that section
centralizer, so the whole orbit lies in the core's center. This supplies
C.2.8 on the eight-dimensional original orbit, preserving the seed and the
reciprocal witness module as their distinct original subgroups.

Source: Aschbacher–Smith C.2.8, 4.1.4 and 7.5.5, printed pp.147,606–607,701,
and the A₇ pair commutant in H.8, p.389, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Representation.AlternatingSevenConjugatePair.Model
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual A₇ doubled action has trivial invertible binary commutant. -/
theorem sourceOrbit_seven_centralizer_eq_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (f : Additive D.sourceOrbit ≃ₗ[ZMod 2] Additive D.sourceOrbit)
    (hf : ∀ l v, f (doubledSeedAction L D.sourceOrbit
      D.sourceOrbit_component_normalizes l v) =
      doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes l (f v)) :
    f = LinearEquiv.refl _ _ := by
  obtain ⟨_,_,_,q,hq,_,a,_,hne,e,he,_⟩ :=
    D.sourceOrbit_seven_pair_coordinates h hd σ hmodel
  let τ := σ.comp a.toMonoidHom
  let b := e.symm.trans (f.trans e)
  have hb (v : Additive D.sourceOrbit) : b (e v) = e (f v) := by
    simp only [b,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
  have hbc (g : alternatingGroup (Fin 7)) (v : Four × Four) :
      b ((σ.prod τ) g v) = (σ.prod τ) g (b v) := by
    obtain ⟨l,rfl⟩ := hq g
    obtain ⟨w,rfl⟩ := e.surjective v
    rw [←he,hb,hf,he,hb]
  have hid := doubledSeven_pair_centralizer σ τ hσ (hσ.comp a.injective)
    four_dimension hne b hbc
  apply LinearEquiv.ext
  intro v
  apply e.injective
  exact (hb v).symm.trans (LinearEquiv.congr_fun hid (e v))

private theorem seven_orbit_core_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    L.pCoreIn 2 ≤ centralizer (D.sourceOrbit : Set G) := by
  apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
  simpa only [D.fundamentalSetup_module,Chapter3.Section02.localJoin,D.localOrbit_eq,
    D.sourceOrbit_eq] using (D.fundamentalSetup h.toHypothesis1221).core_centralizes_module

/-- The original component's section centralizer fixes the entire A₇ orbit. -/
theorem sourceOrbit_seven_sectionCentralizer_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    sectionCentralizer L ≤ centralizer (D.sourceOrbit : Set G) := by
  let W := D.sourceOrbit
  let N := normalizer (W : Set G)
  let φ := W.normalizerMonoidHom
  have hC := (le_sectionCentralizer_iff (sectionCentralizer L) L).mp le_rfl
  have hCW := hC.1.trans (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge
  have hQC := D.seven_orbit_core_centralizes h
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
  have hf : f = LinearEquiv.refl _ _ := D.sourceOrbit_seven_centralizer_eq_one
    h hd σ hσ hmodel f (by
      intro l v
      exact congrArg (fun b : MulAut W => Additive.ofMul (b v.toMul)) (hc l).eq)
  intro w hw
  have hh := LinearEquiv.congr_fun hf (Additive.ofMul (⟨w,hw⟩ : W))
  have he : x * w * x⁻¹ = w := congrArg (fun v : Additive W => (v.toMul : G)) hh
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The same reciprocal witness supports C.2.8 with the whole doubled orbit. -/
theorem sourceOrbit_seven_witness_hypothesisC28
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
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
      hw.2.2.2.2.2.2.2.1 (le_centralizer_iff.mp (D.seven_orbit_core_centralizes h)))
  have hWL : D.sourceOrbit ≤ LH := by
    rw [hmove]
    exact le_normalizer_iff_commutator_le_right.mp ((hWJ.trans hc.radical_le).trans hn)
  have hWR : D.sourceOrbit ≤ (center (J.pCoreIn 2)).map (J.pCoreIn 2).subtype := by
    intro w hwW
    refine ⟨⟨w,hWJ hwW⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro r
    apply Subtype.ext
    exact (D.sourceOrbit_seven_sectionCentralizer_centralizes h hd σ hσ hmodel
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

private theorem seven_witness_core_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {A J H U : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (hw : Witness L V A J H U) :
    D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L := by
  obtain ⟨hc,_,hW,hne⟩ := D.doubledOrbit_oddActorResidual_cover h A
    (by simpa only [←D.sourceOrbit_eq] using hA) ho
  have hI := ((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer
  obtain ⟨hs,_⟩ := coveringOvergroup_eta L.le_normalizer le_rfl hI hc.subset hne
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hNL : (L.subgroupOf (normalizer (L : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  have hperfect : IsPPerfect 2 L := by
    intro N hN hp
    let := hN
    have he : Subsingleton (L ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (L ⧸ N) hp.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  refine ⟨?_,core_le_sectionCentralizer_of_eta
    L.le_normalizer hNL hperfect hs.1 hw.1.1.1⟩
  rw [D.sourceOrbit_eq]
  exact hW.trans hw.2.1.1

/-- The given reciprocal witness supports whole-orbit C.2.8. Both radical
inclusions follow from this same actor and witness, preserving any component
already selected in its overgroup. -/
theorem sourceOrbit_seven_witness_hypothesisC28_of_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {A J H U : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (hw : Witness L V A J H U) :
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) D.sourceOrbit := by
  obtain ⟨hWJ,hJC⟩ := D.seven_witness_core_data h hA ho hw
  exact D.sourceOrbit_seven_witness_hypothesisC28 h hd σ hσ hmodel hw hWJ hJC

/-- The actual odd actor's reciprocal branch supplies full-orbit C.2.8 and
Fitting escape, with both radical inclusions derived from that same witness. -/
theorem sourceOrbit_seven_reciprocal_hypothesisC28
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H U : Subgroup G, Witness L V A J H U ∧
      D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L ∧
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
        (H ⊓ normalizer (L : Set G))
        ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
        (J.pCoreIn 2) D.sourceOrbit ∧
      ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
        (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H := by
  have hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) :=
    le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  obtain ⟨J,H,U,hw,hescape⟩ := D.sourceOrbit_seven_reciprocal_escape h σ hmodel A hA ho hnot
  obtain ⟨hWJ,hJC⟩ := D.seven_witness_core_data h hA ho hw
  exact ⟨J,H,U,hw,hWJ,hJC,
    D.sourceOrbit_seven_witness_hypothesisC28 h hd σ hσ hmodel hw hWJ hJC,hescape⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
