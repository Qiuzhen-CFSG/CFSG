module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.XiFixed
public import CFSG.Quasithin.ChapterA.Section04.SourceChains.Applications

/-!
# Faithfulness of the original Xi subgroup

In the contrary ambient Sylow branch, the checked Xi subgroup X normalizes
W and has C_W(X)=1. Put N=XT and Q=O2(N). Normality puts W inside Q,
and the p-group center theorem supplies a nonidentity element of
W intersect Omega1(Z(Q)). Thus [X,Omega1(Z(Q))] is nontrivial.
The genuine A.4.8 comparison transfers this to the intrinsic module V(X).
The actual global characteristic-two theorem supplies X in the signalizer
class, proving X in Xi_f without an MS-classification premise.

The component application in `Embedding` uses this result in 1.3.9(2).
Original ambient MS fixed-subgroup nontriviality, maximality and the terminal
component exclusions remain with `qt-d-double-natural-pure-fusion` and its
existing source producer `qt-rank-two-ms93`; the earlier-input assembly
parent is `qt-d-double-natural-centralizers`.
Source: Aschbacher--Smith 12.1.4, printed p.790, A.4.8(5), p.59,
and 1.3.9(2), p.514.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual Xi residual is faithful under the original contrary Sylow
hypotheses, with no MS input. -/
theorem doubleNatural_four_pure_xi_faithful_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      PureFourXi.residual T L ∈ XiF G (T : Subgroup G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf
  let X := PureFourXi.residual T L
  let N := X ⊔ (T : Subgroup G)
  let Q := N.pCoreIn 2
  let W := componentOrbit V (T : Subgroup G)
  have hXi := (D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf).1
  have hXW := D.doubleNatural_four_pure_xi_centralizer_of_many h hmany B S w hw hp hfix hf
  have hXN : X ≤ N := le_sup_left
  have hNX : N ≤ normalizer (X : Set G) := sup_le X.le_normalizer hXi.invariant
  have hnormal : (X.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNX
  have hN : N ∈ He G := (lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T))
    ⟨hXi.join_mem_H,show (T : Subgroup G) ≤ N from le_sup_right⟩
  have hXL : X ≤ L := PureFourXi.residual_le_component T L h.maximal_faithful.2.1.2.1
    D.sylow_normalizes_component
  have hNL : N ≤ normalizer (L : Set G) :=
    sup_le (hXL.trans L.le_normalizer) D.sylow_normalizes_component
  have hNW : N ≤ normalizer (W : Set G) := by
    dsimp only [W]
    rw [B.orbit_eq]
    exact hNL.trans (le_normalizer_componentOrbit _ _)
  have hWN : W ≤ N := (D.doubledOrbit_E322 h).le_sylow.trans le_sup_right
  have hWQ : W ≤ Q := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 W) hWN hNW
  have hWne : W ≠ ⊥ := by
    intro he
    exact hw (Subtype.ext (mem_bot.mp (he ▸ w.property)))
  have hXne : X ≠ ⊥ := by
    intro he
    apply hWne
    apply bot_unique
    intro x hx
    have hxc : x ∈ centralizer (X : Set G) := by
      rw [he]
      intro y hy
      have hy1 : y = 1 := hy
      simp only [hy1,one_mul,mul_one]
    exact hXW ▸ (show x ∈ W ⊓ centralizer (X : Set G) from ⟨hx,hxc⟩)
  have htype : IsSignalizerType X := ⟨hXne,hXi.perfect,
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      ((Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hXN)).mp
        (subnormal_core_selfCentralizing (mem_He_iff.mp hN) _ hnormal.isSubnormal))⟩
  have hXQ : X ≤ normalizer (Q : Set G) := hXN.trans
    (N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))
  have hQX : Q ≤ normalizer (X : Set G) := (pCoreIn_le 2 N).trans hNX
  have hcore : X.pCoreIn 2 ≤ Q :=
    pCoreAmbient_mono_of_isSubnormalIn X N 2 hXN hnormal.isSubnormal
  have hcomm : ⁅X,Q⁆ ≤ X.pCoreIn 2 :=
    commutator_le_pCore_of_mutual_normalization X Q (isPGroup_pCoreIn 2 N) hXQ hQX
  have hQW : Q ≤ normalizer (W : Set G) := (pCoreIn_le 2 N).trans hNW
  let : (W.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer hQW
  have hWQne : W.subgroupOf Q ≠ ⊥ := by
    intro he
    apply hWne
    rw [←map_subgroupOf_eq_of_le hWQ,he,Subgroup.map_bot]
  have hmeet := center_inf_ne_bot_of_normal (isPGroup_pCoreIn 2 N) (W.subgroupOf Q) hWQne
  obtain ⟨x,hx,hxne⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hmeet)
  have hxomega : (x : G) ∈ omegaOneCenterAmbient Q :=
    (mem_omegaOneCenterAmbient_iff Q x).mpr ⟨x.property,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) (show (x : G) ∈ W from hx.2),
      fun y hy => congrArg Subtype.val (mem_center_iff.mp hx.1 ⟨y,hy⟩)⟩
  have hmod : signalizerModule X Q ≠ ⊥ := by
    intro he
    have hc : omegaOneCenterAmbient Q ≤ centralizer (X : Set G) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [commutator_comm,←signalizerModule_eq_commutator_omegaCenter,he]
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := hXW ▸ ⟨hx.2,hc hxomega⟩
    exact hxne (Subtype.ext (mem_bot.mp hxbot))
  exact ⟨hXi,htype,(signalizerModule_ne_bot_iff_intrinsic X Q hXi.perfect
    (isPGroup_pCoreIn 2 N) hXQ hcore hcomm).mp hmod⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
