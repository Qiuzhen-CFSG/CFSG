module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionModelSieve
public import Theory.GroupTheory.GeneralizedFitting.CentralPrimeCoreLayer
public import Theory.GroupTheory.CentralTwoQuotientOddCore

/-!
# Odd-core elimination and the actual quotient action

The original point z centralizes O_{2'}(C_G(w)) by the cubic plane action,
and inverts it by the original 1.1.5 hypotheses. Odd order therefore makes
this core trivial. Triviality descends to every component: its center is
its intrinsic two-core, of order dividing two. In particular the perfect
triple-cover alternatives for A6 and A7 cannot occur; their prescribed
permutation actions are realized on the alternating groups themselves.

The generalized-Fitting centralizer theorem now identifies the center,
solvable radical and layer centralizer of C_G(w) with the marked W=<w>.
The quotient has trivial odd core and solvable radical, and acts faithfully
on the original layer by the literal conjugation map. Component quotients
by their two-cores are simple. These results preserve both original local
markings and do not yet identify the remaining model or outer extension.
That inspection and final core-collapse assembly belong to
qt-e-14322-core-collapse.

Source: Aschbacher--Smith 14.3.22, printed p.999, using 1.1.5(2--3)
and the generalized-Fitting argument of 1.2.11; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
private theorem alternatingAction_of_oddCore
    {X : Type*} [Group X] [Finite X] {α : MulAut X} {n : ℕ}
    {σ : Equiv.Perm (Fin n)}
    (ho : pPrimeCore 2 X = ⊥)
    (ha : CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure.AlternatingAction α n σ) :
    ∃ e : X ≃* alternatingGroup (Fin n),
      ∀ x : X, (e (α x) : Equiv.Perm (Fin n)) = σ * e x * σ⁻¹ := by
  rcases ha with h | ⟨hq, ⟨e⟩, _⟩
  · exact h
  · have hZ : center X = ⊥ := pPrimeCore_eq_bot_iff.mp ho _ inferInstance (by
      rw [Nat.card_congr e.toEquiv]
      change Nat.Coprime 2 (Nat.card (ZMod 3))
      norm_num)
    have hcard := Nat.card_congr e.toEquiv
    rw [hZ, card_bot] at hcard
    norm_num at hcard


open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hc s

theorem source_triple_oddCore_eq_bot
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    pPrimeCore 2 (ResidualFusion.C (tripleProduct d a)) = ⊥ := by
  let C := ResidualFusion.C (tripleProduct d a)
  obtain ⟨S, hS⟩ := source_triple_global_sylow
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨M₁, _, h115⟩ := source_triple_original_lemma115_setup
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself S hS
  have hz := source_triple_point_centralizes_oddCore
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  apply bot_unique
  intro r hr
  have hinv := h115.inverts_oddCore r hr
  have hcomm := hz r (mem_map_of_mem C.subtype hr)
  rw [← hcomm, mul_inv_cancel_right] at hinv
  have hsq : r ^ 2 = 1 := Subtype.ext (by
    change (r : G) ^ 2 = 1
    calc
      (r : G) ^ 2 = (r : G) * (r : G) := pow_two _
      _ = (r : G) * (r : G)⁻¹ := congrArg ((r : G) * ·) hinv
      _ = 1 := mul_inv_cancel _)
  have ho : orderOf r = 1 := Nat.eq_one_of_dvd_coprimes
    (pPrimeCore_coprime_card (p := 2) (G := C))
    (orderOf_dvd_of_pow_eq_one hsq) ((pPrimeCore 2 C).orderOf_dvd_natCard hr)
  exact mem_bot.mpr (orderOf_eq_one_iff.mp ho)

theorem source_triple_layer_centralizer_eq
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    centralizer (componentLayer (ResidualFusion.C (tripleProduct d a)) :
      Set (ResidualFusion.C (tripleProduct d a))) = ResidualFusion.W (tripleProduct d a) := by
  have hcore := twoCore_eq_markedKernel (source_triple_twoCore_eq
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)
  exact (centralizer_layer_eq_pCore_of_central (source_triple_oddCore_eq_bot
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)
      (hcore ▸ ResidualFusion.W_central _)).trans hcore

theorem source_triple_center_eq
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    center (ResidualFusion.C (tripleProduct d a)) = ResidualFusion.W (tripleProduct d a) := by
  exact le_antisymm ((center_le_centralizer _).trans
    (source_triple_layer_centralizer_eq
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).le)
    (ResidualFusion.W_central _)

theorem source_triple_radical_eq
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    solvableRadical (ResidualFusion.C (tripleProduct d a)) = ResidualFusion.W (tripleProduct d a) := by
  have hcore := twoCore_eq_markedKernel (source_triple_twoCore_eq
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)
  exact (solvableRadical_eq_pCore_of_central (source_triple_oddCore_eq_bot
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)
      (hcore ▸ ResidualFusion.W_central _)).trans hcore

theorem source_triple_quotient_oddCore_eq_bot
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    pPrimeCore 2 (ResidualFusion.C (tripleProduct d a) ⧸ ResidualFusion.W (tripleProduct d a)) = ⊥ := by
  apply pPrimeCore_quotient_eq_bot_of_central_two_subgroup _ (ResidualFusion.W_central _)
  · rw [← twoCore_eq_markedKernel (source_triple_twoCore_eq
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)]
    exact pCore_isPGroup
  · exact source_triple_oddCore_eq_bot
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself

theorem source_triple_quotient_radical_eq_bot
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    solvableRadical (ResidualFusion.C (tripleProduct d a) ⧸ ResidualFusion.W (tripleProduct d a)) = ⊥ := by
  have hcore := quotient_twoCore_eq_bot (source_triple_twoCore_eq
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)
  exact (solvableRadical_eq_pCore_of_central (source_triple_quotient_oddCore_eq_bot
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)
    (hcore ▸ bot_le)).trans hcore

theorem source_triple_component_center
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D) :
    pPrimeCore 2 D = ⊥ ∧ center D = pCore 2 D ∧ Nat.card (center D) ∣ 2 := by
  have ho := hD.1.pPrimeCore_eq_bot (source_triple_oddCore_eq_bot
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)
  let := hD.2
  have hz : center D = pCore 2 D := IsQuasisimple.center_eq_pCore ho
  have hcore := twoCore_eq_markedKernel (source_triple_twoCore_eq
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)
  refine ⟨ho, hz, ?_⟩
  rw [hz, pCore_subnormal_eq_comap 2 hD.1, hcore]
  have hcardW : Nat.card (ResidualFusion.W (tripleProduct d a)) = 2 := by
    rw [ResidualFusion.W, Nat.card_zpowers, ← orderOf_coe]
    exact (source_triple_local_geometry
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).involution
  exact hcardW ▸ (ResidualFusion.W (tripleProduct d a)).card_comap_dvd_of_injective
    D.subtype D.subtype_injective

theorem source_triple_alternating_action_model
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D)
    {α : MulAut D} {n : ℕ} {σ : Equiv.Perm (Fin n)} (ha : AlternatingAction α n σ) :
    ∃ e : D ≃* alternatingGroup (Fin n),
      ∀ x : D, (e (α x) : Equiv.Perm (Fin n)) = σ * e x * σ⁻¹ :=
  alternatingAction_of_oddCore (source_triple_component_center
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD).1 ha

theorem source_triple_component_quotient_simple
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    {D : Subgroup (ResidualFusion.C (tripleProduct d a))}
    (hD : IsComponent (ResidualFusion.C (tripleProduct d a)) D) :
    IsSimpleGroup (D ⧸ pCore 2 D) := by
  let := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  exact (QuotientGroup.quotientMulEquivOfEq (source_triple_component_center
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself hD).2.1).symm.isSimpleGroup

theorem source_triple_quotient_layer_action
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let C := ResidualFusion.C (tripleProduct d a)
    let W := ResidualFusion.W (tripleProduct d a)
    ∃ ρ : (C ⧸ W) →* MulAut (componentLayer C), Function.Injective ρ ∧
      ∀ (c : C) (x : componentLayer C),
        (ρ (QuotientGroup.mk' W c) x : C) = c * (x : C) * c⁻¹ := by
  intro C W
  have ho := source_triple_oddCore_eq_bot
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hcore := twoCore_eq_markedKernel (source_triple_twoCore_eq
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)
  have hcentral : pCore 2 C ≤ center C := hcore ▸ ResidualFusion.W_central _
  let eW : (C ⧸ W) ≃* (C ⧸ pCore 2 C) := QuotientGroup.quotientMulEquivOfEq hcore.symm
  exact ⟨(centralPrimeCoreLayerAction ho hcentral).comp eW.toMonoidHom,
    (centralPrimeCoreLayerAction_injective ho hcentral).comp eW.injective,
    fun c x => centralPrimeCoreLayerAction_mk ho hcentral c x⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
