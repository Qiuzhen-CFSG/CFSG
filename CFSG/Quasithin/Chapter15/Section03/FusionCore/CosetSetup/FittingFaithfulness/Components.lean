module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness.Kernel
public import CFSG.Quasithin.MainForward.SourceFamilies
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.Frattini.PGroup

/-!
# C-component centralization from the genuine empty faithful local family

A C-component of H remains one in its subgroup generated with T; the latter
has nontrivial two-core. Its intrinsic module must therefore vanish when
L_f(G,T) is empty. The proved A.4.8(4) then makes it centralize Ω₁(Z(Q)).
For C ≤ Z(Q) with central squares, its commutators lie in that omega-center;
two-perfect commutator idempotence proves that it centralizes C.

The printed proof cites A.4.11. Its relevant direction is (2) implies (1),
from a moved, normal elementary abelian V with O₂(H/C_H(V)) = 1 to membership
in X_f; that direction does not need the chief-factor hypothesis. Here we
avoid any unproved reducedness premise by using A.4.8 directly and the
Frattini bound from 15.3.48(2). Neither U nor V_H is assumed abelian.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.59–61,
and proof of 15.3.49(a), p.1142.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness
open ChapterA.Section04

private theorem perfect_twoPerfect {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] : IsPPerfect 2 G := by
  intro N hn hp
  let := hn
  let := hp.isNilpotent
  exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)

private theorem fitting_eq_core {G : Type*} [Group G] [Finite G]
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    generalizedFitting G = pCore 2 G := by
  have he : componentLayer G = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    let := hK.2
    have hk := subnormal_core_selfCentralizing hc K hK.1
    have hz := IsQuasisimple.pCore_le_center (G := K) 2
    have ht : (⊤ : Subgroup K) ≤ center K := by
      calc
        ⊤ = centralizer (center K : Set K) := centralizer_center.symm
        _ ≤ centralizer (pCore 2 K : Set K) := centralizer_le hz
        _ ≤ center K := hk.trans hz
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp (top_unique ht))).elim
  rw [generalizedFitting, he, sup_bot_eq, Fitting_eq_pcore G 2
    (pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hc)]

private theorem intrinsicModule_map {G D : Type*} [Group G] [Group D]
    (f : G →* D) (hf : Function.Injective f) (L : Subgroup G) :
    intrinsicSignalizerModule (L.map f) = (intrinsicSignalizerModule L).map f := by
  change signalizerModule (L.map f) ((L.map f).pCoreIn 2) =
    (signalizerModule L (L.pCoreIn 2)).map f
  rw [signalizerModule_eq_commutator_omegaCenter, signalizerModule_eq_commutator_omegaCenter,
    ← map_pCoreIn_of_injective 2 L f hf, omegaOneCenterAmbient_map_injective f hf, map_commutator]

/-- C-components of H give genuine members of L(G,T), by restriction to
L T and inclusion of the nontrivial two-core of H in that subgroup's core. -/
theorem cComponent_mem_localComponents
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hQ : pCore 2 H ≠ ⊥)
    (L : Subgroup H) (hL : L.IsCComponent) :
    L.map H.subtype ∈ MainForward.localComponents T := by
  let B := L.map H.subtype
  have hBH : B ≤ H := map_subtype_le _
  have hJH : B ⊔ (T : Subgroup G) ≤ H := sup_le hBH hTH
  have hcompH : (B.subgroupOf H).IsCComponent := by
    change ((L.map H.subtype).comap H.subtype).IsCComponent
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  refine ⟨hcompH.subgroupOf_of_le le_sup_left hJH, ?_⟩
  intro hb
  have hc := pCore_le_map_of_sylow_le (T.subtype hTH)
    ((B ⊔ (T : Subgroup G)).subgroupOf H)
    (show (T.subtype hTH : Subgroup H) ≤ (B ⊔ (T : Subgroup G)).subgroupOf H from
      fun x hx => (show (T : Subgroup G) ≤ B ⊔ (T : Subgroup G) from le_sup_right) hx)
  have hi : pCore 2 ((B ⊔ (T : Subgroup G)).subgroupOf H) = ⊥ := by
    have hh := pCore_map_iso 2 (subgroupOfEquivOfLe hJH)
    rw [hb] at hh
    exact (map_eq_bot_iff_of_injective _ (subgroupOfEquivOfLe hJH).injective).mp hh
  rw [hi, Subgroup.map_bot] at hc
  exact hQ (le_bot_iff.mp hc)

/-- Emptiness of the actual faithful local family forces the intrinsic
signalizer module of every C-component of H to vanish. -/
theorem intrinsicModule_eq_bot_of_emptyLf
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hQ : pCore 2 H ≠ ⊥)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (L : Subgroup H) (hL : L.IsCComponent) : intrinsicSignalizerModule L = ⊥ := by
  by_contra hn
  let B := L.map H.subtype
  let := hL.perfect
  let : Group.IsPerfect B := Group.IsPerfect.map H.subtype
  have hBcore : centralizer (pCore 2 B : Set B) ≤ pCore 2 B :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2
      (L.equivMapOfInjective H.subtype H.subtype_injective)).mp
      (subnormal_core_selfCentralizing hc L hL.subnormal)
  have hBne : B ≠ ⊥ := fun hb =>
    hL.ne_bot ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp hb)
  have hm : intrinsicSignalizerModule B ≠ ⊥ := by
    change intrinsicSignalizerModule (L.map H.subtype) ≠ ⊥
    rw [intrinsicModule_map H.subtype H.subtype_injective]
    exact fun hb => hn ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp hb)
  have hmem : B ∈ MainForward.faithfulLocalComponents T :=
    ⟨cComponent_mem_localComponents T H hTH hQ L hL,
      ⟨hBne, perfect_twoPerfect, fitting_eq_core hBcore⟩, hm⟩
  rw [hempty] at hmem
  exact hmem

/-- A.4.8(4) supplies the needed omega-center implication directly. It
requires neither a chief-factor condition nor a reduced-module witness. -/
theorem cComponent_centralizes_omegaCore_of_intrinsicModule_eq_bot
    {G : Type*} [Group G] [Finite G] (L : Subgroup G) (hL : L.IsCComponent)
    (hzero : intrinsicSignalizerModule L = ⊥) :
    L ≤ centralizer (omegaOneCenterAmbient (pCore 2 G) : Set G) := by
  let := hL.perfect
  have hp : IsPPerfect 2 L := perfect_twoPerfect
  have hn : L ≤ normalizer (pCore 2 G : Set G) := le_normalizer_of_normal
  have hcomm : ⁅L, pCore 2 G⁆ ≤ L.pCoreIn 2 := by
    rw [commutator_comm]
    exact (commutator_le_core_commutator_of_isSubnormal L (pCore 2 G)
      hL.subnormal hp pCore_isPGroup hn).trans
      (map_mono (commutator_le_left _ _))
  have hm := signalizerModule_le_intrinsicModule L (pCore 2 G) hp hn
    (pCoreIn_le_of_subnormal 2 hL.subnormal) hcomm
  rw [hzero, signalizerModule_eq_commutator_omegaCenter] at hm
  exact commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hm)

/-- The Frattini bound in 15.3.48 makes the squares in C central. Once a
two-perfect group fixes the omega-center of Q, its action on C is quadratic,
and commutator idempotence makes that action trivial. -/
theorem centralizes_of_omegaCore_and_central_squares
    {G : Type*} [Group G] [Finite G]
    (L C : Subgroup G) [C.Normal] [IsMulCommutative C]
    (hL : IsPPerfect 2 L) (hCQ : C ≤ pCore 2 G)
    (hCQcent : C ≤ centralizer (pCore 2 G : Set G))
    (hsq : ∀ c ∈ C, c ^ 2 ∈ center G)
    (hfix : L ≤ centralizer (omegaOneCenterAmbient (pCore 2 G) : Set G)) :
    L ≤ centralizer (C : Set G) := by
  have hc : ⁅C,L⁆ ≤ omegaOneCenterAmbient (pCore 2 G) := by
    apply commutator_le.mpr
    intro c hc l hl
    have hcommC : ⁅c,l⁆ ∈ C := commutator_le_left C L (commutator_mem_commutator hc hl)
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hCQ hcommC, ?_, fun q hq => hCQcent hcommC q hq⟩
    have hd : l * c⁻¹ * l⁻¹ ∈ C :=
      (inferInstance : C.Normal).conj_mem _ (C.inv_mem hc) l
    have hcd : Commute c (l * c⁻¹ * l⁻¹) :=
      (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative C) hd) c hc
    have hz : l * c ^ 2 * l⁻¹ = c ^ 2 := by
      rw [(mem_center_iff.mp (hsq c hc)) l, mul_assoc, mul_inv_cancel, mul_one]
    calc
      ⁅c,l⁆ ^ 2 = (c * (l * c⁻¹ * l⁻¹)) ^ 2 := by simp only [commutatorElement_def, mul_assoc]
      _ = c ^ 2 * (l * c⁻¹ * l⁻¹) ^ 2 := hcd.mul_pow 2
      _ = c ^ 2 * (l * c ^ 2 * l⁻¹)⁻¹ := by
        congr 1
        simp only [pow_two, mul_inv_rev, inv_inv]
        group
      _ = 1 := by rw [hz, mul_inv_cancel]
  have hquad : ⁅⁅C,L⁆,L⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hc.trans (le_centralizer_iff.mp hfix))
  have hi := commutator_isPPerfect_idempotent L C hL (pCore_isPGroup.to_le hCQ)
    (le_normalizer_of_normal : L ≤ normalizer (C : Set G))
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hi.symm.trans hquad))

/-- The actual empty L_f hypothesis implies that C-components centralize
the fixed core, using A.4.8 and the source square bound. -/
theorem cComponents_centralize_of_emptyLf
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hQ : pCore 2 H ≠ ⊥)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (C : Subgroup H) [C.Normal] [IsMulCommutative C]
    (hCQ : C ≤ pCore 2 H) (hCQcent : C ≤ centralizer (pCore 2 H : Set H))
    (hsq : ∀ c ∈ C, c ^ 2 ∈ center H) :
    ∀ L : Subgroup H, L.IsCComponent → L ≤ centralizer (C : Set H) := by
  intro L hL
  let := hL.perfect
  exact centralizes_of_omegaCore_and_central_squares L C perfect_twoPerfect hCQ hCQcent hsq
    (cComponent_centralizes_omegaCore_of_intrinsicModule_eq_bot L hL
      (intrinsicModule_eq_bot_of_emptyLf T H hTH hQ hc hempty L hL))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness

end
