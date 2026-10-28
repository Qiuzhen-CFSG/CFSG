module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Even
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorCentralizerElementary
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.GeneralizedFitting.ComponentCentralizerCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentCentralizerAction

/-!
# Faithful action of the actual marked quotient centralizer

The centralizer of the component lies in the elementary two-group C_G(A).
Perfectness lifts its quotient centralizer through the central marked line.
The quotient has trivial two-core, so its component centralizer is trivial.
Consequently the centralizer of the original marked involution normalizes
the component image and acts faithfully by conjugation. Transport through
the literal component quotient embedding gives the required action.

The source producer retains all the original hypotheses, including terminal
solvability. The independent model-centralizer calculation remains a premise
of the even-exclusion consumer; no ambient normality of the component is used.
Source: Aschbacher--Smith, 14.3.20, printed pp.997--998, `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
variable {F : InvariantFlag T V 2} {L A : Subgroup G}
namespace MarkedPoint
variable (P : MarkedPoint F L A)

/-- The actual component image has trivial centralizer in the point quotient. -/
theorem componentImage_centralizer_eq_bot
    (hCA : IsPGroup 2 (centralizer (A : Set G)))
    (hA : ElementaryFactor F L A) (z : G) (hz : F.Vi 1 = zpowers z)
    (B : Subgroup G) (hKB : P.blockCentralizer ≤ B)
    (hB : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer))
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element) :
    centralizer ((B.subgroupOf P.globalCentralizer).map P.pointQuotientMap :
      Set P.PointQuotient) = ⊥ := by
  let K := B.subgroupOf P.globalCentralizer
  let q := P.pointQuotientMap
  let Kbar := K.map q
  let : IsQuasisimple K := hB.2
  have hker : q.ker ≤ centralizer (K : Set P.globalCentralizer) := by
    rw [P.pointQuotientMap_ker]
    exact P.pointKernel_le_center.trans (center_le_centralizer _)
  have hlift : (centralizer (K : Set P.globalCentralizer)).map q =
      centralizer (Kbar : Set P.PointQuotient) := by
    rw [← comap_centralizer_map_eq_of_perfect q K hker,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hCAle : centralizer (K : Set P.globalCentralizer) ≤
      (centralizer (A : Set G)).subgroupOf P.globalCentralizer := by
    intro c hc a ha
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc
      ⟨a, (P.factor_le_blockCentralizer ha).2⟩ (hKB (P.factor_le_blockCentralizer ha)))
  have hp : IsPGroup 2 (centralizer (Kbar : Set P.PointQuotient)) := by
    rw [← hlift]
    exact ((hCA.comap_subtype (K := P.globalCentralizer)).to_le hCAle).map q
  have hKbar : IsComponent P.PointQuotient Kbar := by
    apply (hB.map_surjective q (QuotientGroup.mk'_surjective _)).resolve_left
    intro he
    have hzmem : q (P.markedGenerator hA.seed_le z hz) ∈ Kbar :=
      mem_map_of_mem q (hKB (P.generator_mem hA.seed_le z hz))
    change Kbar = ⊥ at he
    rw [he, mem_bot] at hzmem
    have ho := P.markedGenerator_quotient_order hA z hz
    rw [hzmem, orderOf_one] at ho
    contradiction
  have hqcore : pCore 2 P.PointQuotient = ⊥ := by
    change pCore 2 (P.globalCentralizer ⧸ P.pointKernel) = ⊥
    rw [← pCore_map_iso 2
      (QuotientGroup.quotientMulEquivOfEq (P.pointKernel_eq_core hcore)).symm,
      pCore_quotient_pCore_eq_bot, Subgroup.map_bot]
  have hc := hKbar.centralizer_pCore_eq_bot_of_pCore_eq_bot 2 hqcore
  apply (eq_bot_iff_forall _).mpr
  intro c hc'
  have htop : (⊤ : Subgroup (centralizer (Kbar : Set P.PointQuotient))) ≤
      pCore 2 (centralizer (Kbar : Set P.PointQuotient)) :=
    le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩
  have hm := htop (show (⟨c, hc'⟩ : centralizer (Kbar : Set P.PointQuotient)) ∈ ⊤ from mem_top _)
  rw [hc, mem_bot] at hm
  exact congrArg Subtype.val hm
/-- The literal component quotient gives the faithful marked-centralizer action. -/
theorem componentCentralizerAction_of_factor_centralizer_isPGroup
    (hCA : IsPGroup 2 (centralizer (A : Set G)))
    (hA : ElementaryFactor F L A) (z : G) (hz : F.Vi 1 = zpowers z)
    (B : Subgroup G) (hKB : P.blockCentralizer ≤ B)
    (hB : IsComponent P.globalCentralizer (B.subgroupOf P.globalCentralizer))
    (hcore : P.globalCentralizer.pCoreIn 2 = zpowers P.element) :
    P.ComponentCentralizerAction B hB hcore (P.markedGenerator hA.seed_le z hz) := by
  let K := B.subgroupOf P.globalCentralizer
  let X := K ⧸ pCore 2 K
  let Kbar := K.map P.pointQuotientMap
  let j : X →* P.PointQuotient := P.componentQuotientMap B hB hcore
  have hj : Function.Injective j := P.componentQuotientMap_injective B hB hcore
  have hr : j.range = Kbar := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 K) ⟨x, hx⟩, rfl⟩
  let e : X ≃* Kbar := (MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hr)
  let x : X := P.componentQuotientGenerator hA z hz B hKB
  have he (y : X) : (e y : P.PointQuotient) = j y := rfl
  have hex : (e x : P.PointQuotient) =
      P.pointQuotientMap (P.markedGenerator hA.seed_le z hz) := rfl
  have hx : (e x : P.PointQuotient) ≠ 1 := by
    intro hx
    have ho := P.markedGenerator_quotient_order hA z hz
    rw [← hex, hx, orderOf_one] at ho
    contradiction
  have hKbar : IsComponent P.PointQuotient Kbar := by
    apply (hB.map_surjective P.pointQuotientMap (QuotientGroup.mk'_surjective _)).resolve_left
    intro hbot
    change Kbar = ⊥ at hbot
    exact hx (mem_bot.mp (hbot.le (e x).property))
  have hC := P.componentImage_centralizer_eq_bot hCA hA z hz B hKB hB hcore
  obtain ⟨ρ, hρ, hact⟩ := hKbar.exists_faithful_centralizer_action e hC x hx
  simp only [he] at hact ρ hρ
  exact ⟨ρ, hρ, hact⟩

end MarkedPoint

open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The faithful action required by the even branch of 14.3.20 follows from
its original source hypotheses, retaining the solvability input. -/
theorem evenCentralizerActionSource_of_source_inputs
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
    : EvenCentralizerActionSource F (sourceResidual M Mc) := by
  intro A hA _ P z hz _ _ hcore _ B _ hKB hB _ _ _ _
  let := hA.elementary
  have hEA := (Recognition.source_factor_centralizer_elementary_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    A hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized).1
  let := hEA
  exact P.componentCentralizerAction_of_factor_centralizer_isPGroup
    (IsElementaryAbelian.isPGroup 2 _) hA z hz B hKB hB hcore

/-- Apply the constructed action to the actual even-exclusion consumer.
Only its independent model-centralizer calculation remains explicit. -/
theorem evenExclusionSource_of_source_inputs_and_model_bounds
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
    (hmodels : EvenModelCentralizerBounds.{u}) :
    EvenExclusionSource F (sourceResidual M Mc) :=
  evenExclusionSource_of_centralizer_inputs F (sourceResidual M Mc) hmodels
    (evenCentralizerActionSource_of_source_inputs
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
