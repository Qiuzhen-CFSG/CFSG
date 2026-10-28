module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
public import Theory.GroupTheory.EmbeddedCenterMap
/-!
# Nonabelian MS center realizations in the binary linear-three branch

Write P=O₂(K) and Q=[P,K]. If Z(Q) is centralized by P, commutator
idempotence gives [Z(P),K]=[Z(Q),K]. In C.1.34(3), the natural section
Z(Q) is centralized by P and a fixed-point-free matrix shows [Z(Q),K]=Z(Q).
In (4), the central four and the natural moved section together centralize P.
Thus both alternatives realize the literal source U, with the original actor.

In case (3), C_Q(K)=1. Consequently the central kernel of the restriction
K→Ǩ is disjoint from Q. Commutators of the checked-center preimage lie in
Q, and their commutators with P lie also in that kernel. A second use of
commutator idempotence proves [Z₀,K]=U for the actual checked quotient.

The full alternative predicates retain every dual section, centrality,
cardinality, direct-sum and Sylow-centralizer clause. The final applications
use the genuine MS-pair with R=Tᵥ. Case (4)'s checked-center identity is
not asserted here: its central four prevents the disjoint-kernel argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.34,
printed pp.136–137, and 13.6.22, printed pp.932–933.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters
variable {G : Type*} [Group G]
theorem centerIn_eq (D : Subgroup G) : sCenter D = D ⊓ centralizer (D : Set G) := by
  ext d
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, fun y hy => congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)⟩
  · rintro ⟨hd, hc⟩
    exact ⟨⟨d, hd⟩, mem_center_iff.mpr (fun y => Subtype.ext (hc y y.property)), rfl⟩

theorem sourceU_eq_core_center [Finite G] (K : Subgroup G) :
    sourceU K = ⁅sCenter (K.pCoreIn 2), K⁆ := by
  unfold sourceU CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
  rw [map_embeddedCenter _ _ K.subtype_injective]
  rfl

theorem normalizes_core_center (K : Subgroup G) :
    K ≤ normalizer (sCenter (K.pCoreIn 2)) :=
  (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))).trans
    (normalizer_le_normalizer_characteristic_image (K.pCoreIn 2) (center (K.pCoreIn 2)))

theorem msQ_eq_core_commutator [Finite G] (K R : Subgroup G)
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K) :
    msQ K R = ⁅K.pCoreIn 2, K⁆ := by
  rw [msQ_eq_ambient_blockU K R hs hp, blockU, map_commutator,
    ← MonoidHom.range_eq_map, range_subtype]
  rfl

theorem sourceU_eq_moved_center [Finite G] (K R : Subgroup G)
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (hc : sCenter (msQ K R) ≤ centralizer (K.pCoreIn 2 : Set G)) :
    sourceU K = ⁅sCenter (msQ K R), K⁆ := by
  have hQ : msQ K R ≤ K.pCoreIn 2 := by
    rw [msQ_eq_core_commutator K R hs hp]
    exact le_normalizer_iff_commutator_le_left.mp
      (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hzP : sCenter (K.pCoreIn 2) ≤ K.pCoreIn 2 := map_subtype_le _
  have hid := commutator_isPPerfect_idempotent K (sCenter (K.pCoreIn 2)) hp
    ((isPGroup_pCoreIn 2 K).to_le hzP) (normalizes_core_center K)
  have hUZ : ⁅sCenter (K.pCoreIn 2), K⁆ ≤ sCenter (msQ K R) := by
    rw [centerIn_eq (msQ K R)]
    refine le_inf ?_ ?_
    · rw [msQ_eq_core_commutator K R hs hp]
      exact commutator_mono hzP le_rfl
    · exact (le_normalizer_iff_commutator_le_left.mp (normalizes_core_center K)).trans
        (((centerIn_eq _).le.trans inf_le_right).trans (centralizer_le hQ))
  rw [sourceU_eq_core_center]
  refine le_antisymm (hid.symm.le.trans (commutator_mono hUZ le_rfl)) ?_
  apply commutator_mono _ le_rfl
  rw [centerIn_eq (K.pCoreIn 2)]
  exact le_inf ((map_subtype_le _).trans hQ) hc

private def movingMatrix : BinaryLinearThree.Group :=
  ⟨!![0,1,0;0,0,1;1,1,0], by decide⟩

private theorem movingMatrix_displacement (w : BinaryLinearThree.Vector) :
    ∃ x : BinaryLinearThree.Vector, BinaryLinearThree.W movingMatrix x - x = w := by
  revert w
  decide +kernel

theorem natural_section_commutator {K D : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K D ⊥ (linearThreeActor e) BinaryLinearThree.W) :
    ⁅D, K⁆ = D := by
  obtain ⟨_, hn, _, hnormal, f, he⟩ := h
  let := hnormal
  let q : D →* Multiplicative BinaryLinearThree.Vector :=
    f.toMonoidHom.comp (QuotientGroup.mk' _)
  have hq : Function.Injective q := by
    apply f.injective.comp
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk', bot_subgroupOf]
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp hn)
  intro d hd
  obtain ⟨x, hx⟩ := movingMatrix_displacement (Multiplicative.toAdd (q ⟨d, hd⟩))
  obtain ⟨y, hy⟩ := (f.surjective.comp (QuotientGroup.mk'_surjective _))
    (Multiplicative.ofAdd x)
  obtain ⟨k, hk⟩ := linearThreeActor_surjective e movingMatrix
  let y' := D.normalizerMonoidHom ⟨k, hn k.property⟩ y
  have hcoord : q (y' * y⁻¹) = q ⟨d, hd⟩ := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv]
    simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    have hyq : Multiplicative.toAdd (q y) = x := congrArg Multiplicative.toAdd hy
    rw [show Multiplicative.toAdd (q y') =
        BinaryLinearThree.W (linearThreeActor e k) (Multiplicative.toAdd (q y)) from
      he k y y' rfl, hk, hyq, hx]
  have hd' := congrArg Subtype.val (hq hcoord)
  change (y' : G) * (y : G)⁻¹ = d at hd'
  rw [← hd', commutator_comm]
  exact commutator_mem_commutator k.property y.property

variable {J H : Type*} [Group J] [Group H] [Finite J]

theorem center_preimage_commutator_of_disjoint_kernel (hp : IsPPerfect 2 J)
    (f : J →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hdisj : blockU J ⊓ f.ker = ⊥) :
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup J)⁆ =
      ⁅sCenter (pCore 2 J), (⊤ : Subgroup J)⁆ := by
  let : Finite H := Finite.of_surjective f hf
  let X := (sCenter (pCore 2 H)).comap f
  let M := ⁅X, (⊤ : Subgroup J)⁆
  have hcore : (pCore 2 H).comap f = pCore 2 J :=
    f.comap_pCore_of_ker_isPGroup hf hk
  have hmap : (pCore 2 J).map f = pCore 2 H := by
    rw [← hcore, map_comap_eq_self_of_surjective hf]
  have hXP : X ≤ pCore 2 J := by
    rw [← hcore]
    exact comap_mono (map_subtype_le _)
  have hnX : X.Normal := inferInstanceAs
    (((center (pCore 2 H)).map (pCore 2 H).subtype).comap f).Normal
  have hMX : M ≤ X := commutator_le_left _ _
  have hMQ : M ≤ blockU J := commutator_mono hXP le_rfl
  have hXPker : ⁅X, pCore 2 J⁆ ≤ f.ker := by
    rw [← Subgroup.map_eq_bot_iff, map_commutator, hmap]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (map_comap_le _ _).trans ((centerIn_eq _).le.trans inf_le_right)
  have hMP : ⁅M, pCore 2 J⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hdisj]
    exact le_inf ((commutator_mono hMQ le_top).trans (commutator_le_left _ _))
      ((commutator_mono hMX le_rfl).trans hXPker)
  have hMZ : M ≤ sCenter (pCore 2 J) := by
    rw [centerIn_eq]
    exact le_inf (hMX.trans hXP) (commutator_eq_bot_iff_le_centralizer.mp hMP)
  have hid : ⁅M, (⊤ : Subgroup J)⁆ = M :=
    commutator_isPPerfect_idempotent ⊤ X
      (hp.of_surjective (topEquiv (G := J)).symm.toMonoidHom
        (topEquiv (G := J)).symm.surjective)
      (pCore_isPGroup.to_le hXP) (by rw [normalizer_eq_top])
  apply le_antisymm (hid.symm.le.trans (commutator_mono hMZ le_rfl))
  apply commutator_mono _ le_rfl
  intro z hz
  change f z ∈ sCenter (pCore 2 H)
  rw [centerIn_eq] at hz ⊢
  refine ⟨?_, ?_⟩
  · rw [← hmap]
    exact mem_map_of_mem f hz.1
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmap.symm ▸ hx : x ∈ (pCore 2 J).map f)
    exact (map_mul f y z).symm.trans ((congrArg f (hz.2 y hy)).trans (map_mul f z y))

variable [Finite G] {K R S : Subgroup G}

/-- The complete third alternative, including its dual sections. -/
def CaseThree (K R S : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) : Prop :=
  HasSectionModel K (sCenter (msQ K R)) ⊥ (linearThreeActor e) BinaryLinearThree.W ∧
  HasSectionModel K (msQ K R) (sCenter (msQ K R)) (linearThreeActor e)
    (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual) ∧
  MSNotCentralizerCore K R S

/-- The complete fourth alternative, with its central order-four subgroup
and all three successive module sections. -/
def CaseFour (K R S : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) : Prop :=
  let Q := msQ K R
  let Z := sCenter Q
  let C := Q ⊓ centralizer (K : Set G)
  let U := ⁅Z, K⁆
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  IsElementaryAbelian 2 C ∧ Nat.card C = 4 ∧
    C ≤ sCenter (K ⊔ R) ∧ Z = C ⊔ U ∧ C ⊓ U = ⊥ ∧
    HasSectionModel K U ⊥ (linearThreeActor e) BinaryLinearThree.W ∧
    HasSectionModel K Phi Z (linearThreeActor e) BinaryLinearThree.W.dual ∧
    HasSectionModel K D Phi (linearThreeActor e)
      (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual) ∧
    HasSectionModel K Q D (linearThreeActor e) (BinaryLinearThree.W.prod BinaryLinearThree.W) ∧
    MSNotCentralizerCore K R S

theorem caseThree_sourceU
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseThree K R S e) :
    sourceU K = sCenter (msQ K R) := by
  have hc := core_centralizes_trivial_section e BinaryLinearThree.W h.1
  exact (sourceU_eq_moved_center K R hs hp
    (fun z hz p hp => (hc hp z hz).symm)).trans (natural_section_commutator e h.1)

theorem caseFour_sourceU
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    sourceU K = ⁅sCenter (msQ K R), K⁆ := by
  apply sourceU_eq_moved_center K R hs hp
  rw [h.2.2.2.1]
  apply sup_le
  · exact (h.2.2.1.trans ((centerIn_eq _).le.trans inf_le_right)).trans
      (centralizer_le ((pCoreIn_le 2 K).trans le_sup_left))
  · have hc := core_centralizes_trivial_section e BinaryLinearThree.W h.2.2.2.2.2.1
    exact fun z hz p hp => (hc hp z hz).symm

theorem caseThree_fixed_eq_bot
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseThree K R S e) :
    msQ K R ⊓ centralizer (K : Set G) = ⊥ := by
  have hQ : msQ K R ≤ K := by
    rw [msQ_eq_ambient_blockU K R hs hp]
    exact map_subtype_le _
  have hfixed := section_centralizer_eq h.1 (linearThreeActor_surjective e) bot_le
    (fun w hw => BinaryLinearThree.ParabolicFixedFree.natural_fixed_eq_zero w (fun g _ => hw g))
  apply le_bot_iff.mp
  rintro q ⟨hq, hc⟩
  have hz : q ∈ sCenter (msQ K R) := by
    rw [centerIn_eq]
    exact ⟨hq, centralizer_le hQ hc⟩
  have hbot : (⟨q, hz⟩ : sCenter (msQ K R)) ∈
      (⊥ : Subgroup G).subgroupOf (sCenter (msQ K R)) := hfixed ▸ hc
  exact hbot

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels

omit [Finite G] in
theorem checkedKMap_kernel_central (K : Subgroup G) (v : G) (hK : K ≤ Gv v) :
    (BinaryRankTwo.CenterPreimage.checkedKMap K v hK).ker ≤ center K := by
  rw [BinaryRankTwo.CenterPreimage.checkedKMap_kernel]
  intro k hk
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact congrArg (fun y : Gv v => (y : G))
    (mem_center_iff.mp (vLine_le_center v hk) (inclusion hK x))

omit [Finite G] in
/-- The actual checked kernel has order dividing two. -/
theorem checkedKMap_kernel_card (K : Subgroup G) (v : G) (hK : K ≤ Gv v)
    (hv : v ^ 2 = 1) :
    Nat.card (BinaryRankTwo.CenterPreimage.checkedKMap K v hK).ker ∣ 2 := by
  rw [BinaryRankTwo.CenterPreimage.checkedKMap_kernel]
  apply (card_comap_dvd_of_injective (vLine v) (inclusion hK)
    (inclusion_injective hK)).trans
  change Nat.card (zpowers (centralElement v)) ∣ 2
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one (show centralElement v ^ 2 = 1 from Subtype.ext hv)

omit [Finite G] in
/-- The checked kernel is central in the genuine MS ambient group KT_v. -/
theorem checkedKMap_kernel_central_join (K T : Subgroup G) (v : G) (hK : K ≤ Gv v) :
    (BinaryRankTwo.CenterPreimage.checkedKMap K v hK).ker.map K.subtype ≤
      sCenter (K ⊔ Tv T v) := by
  rw [centerIn_eq]
  rintro x ⟨k, hk, rfl⟩
  refine ⟨(le_sup_left : K ≤ K ⊔ Tv T v) k.property, ?_⟩
  rw [BinaryRankTwo.CenterPreimage.checkedKMap_kernel] at hk
  intro y hy
  have hyG : y ∈ Gv v := (sup_le hK inf_le_right) hy
  exact congrArg (fun z : Gv v => (z : G))
    (mem_center_iff.mp (vLine_le_center v hk) ⟨y, hyG⟩)

theorem caseThree_checked_commutator (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseThree K R S e) :
    ⁅sourceZ0 K v hK, K⁆ = sourceU K := by
  have hd : blockU K ⊓ (BinaryRankTwo.CenterPreimage.checkedKMap K v hK).ker = ⊥ := by
    apply le_bot_iff.mp
    rintro k ⟨hk, hker⟩
    have hkc : (k : G) ∈ centralizer (K : Set G) := by
      intro x hx
      exact congrArg Subtype.val (mem_center_iff.mp (checkedKMap_kernel_central K v hK hker) ⟨x, hx⟩)
    have hq : (k : G) ∈ msQ K R := by
      rw [msQ_eq_ambient_blockU K R hs hp]
      exact mem_map_of_mem K.subtype hk
    have hb := caseThree_fixed_eq_bot hs hp e h ▸ (show (k : G) ∈ msQ K R ⊓ centralizer (K : Set G) from ⟨hq, hkc⟩)
    exact Subtype.ext hb
  have hh := center_preimage_commutator_of_disjoint_kernel hp
    (BinaryRankTwo.CenterPreimage.checkedKMap K v hK)
    (BinaryRankTwo.CenterPreimage.checkedKMap_surjective K v hK)
    (BinaryRankTwo.CenterPreimage.checkedKMap_pKernel K v hK hv) hd
  have hm := congrArg (map K.subtype) hh
  rw [map_commutator, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact hm

open Representation

theorem caseThree_realization (v : G) (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseThree K R S e) :
    sourceU K = sCenter (msQ K R) ∧
    (∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
      m.actor = linearThreeActor e) ∧
    ⁅sourceZ0 K v hK, K⁆ = sourceU K := by
  refine ⟨caseThree_sourceU hs hp e h, ?_, caseThree_checked_commutator v hK hv hs hp e h⟩
  rw [caseThree_sourceU hs hp e h]
  exact natural_model_of_section e h.1

theorem caseFour_sourceU_realization
    (hs : (K.subgroupOf (K ⊔ R)).IsSubnormal) (hp : IsPPerfect 2 K)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e) :
    sourceU K = ⁅sCenter (msQ K R), K⁆ ∧
    (∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
      m.actor = linearThreeActor e) := by
  refine ⟨caseFour_sourceU hs hp e h, ?_⟩
  rw [caseFour_sourceU hs hp e h]
  exact natural_model_of_section e h.2.2.2.2.2.1

/-- The genuine MS-pair supplies the relative subnormality and
 two-perfection used by the center calculation. -/
theorem msPair_core_hypotheses {κ : GroupClass} (h : LinearThreeMSPair κ K R 1 (ZMod 2)) :
    (K.subgroupOf (K ⊔ R)).IsSubnormal ∧ IsPPerfect 2 K := by
  refine ⟨h.component.2.subnormal, ?_⟩
  let := h.component.2.perfect
  let f := subgroupOfEquivOfLe (show K ≤ K ⊔ R from le_sup_left)
  have hperfect : IsPPerfect 2 (K.subgroupOf (K ⊔ R)) := by
    intro N hN hpN
    let := hN
    have htriv : Subsingleton ((K.subgroupOf (K ⊔ R)) ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent _ hpN.isNilpotent
    apply eq_top_iff.mpr
    intro k _
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  exact hperfect.of_surjective f.toMonoidHom f.surjective

/-- Application of case (3) at the literal source radical T_v. -/
theorem caseThree_at_Tv {κ : GroupClass} (T : Subgroup G) (v : G)
    (hK : K ≤ Gv v) (hv : v ^ 2 = 1)
    (hMS : LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseThree K (Tv T v) S e) :
    sourceU K = sCenter (msQ K (Tv T v)) ∧
    (∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
      m.actor = linearThreeActor e) ∧
    ⁅sourceZ0 K v hK, K⁆ = sourceU K :=
  caseThree_realization v hK hv (msPair_core_hypotheses hMS).1
    (msPair_core_hypotheses hMS).2 e h

/-- Case (4) realizes the actual source U with the same actor. The checked
center identity in this alternative remains a separate source obligation. -/
theorem caseFour_at_Tv {κ : GroupClass} (T : Subgroup G) (v : G)
    (hMS : LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K (Tv T v) S e) :
    sourceU K = ⁅sCenter (msQ K (Tv T v)), K⁆ ∧
    (∃ m : ConjugationQuotientModel K (sourceU K) BinaryLinearThree.W,
      m.actor = linearThreeActor e) :=
  caseFour_sourceU_realization (msPair_core_hypotheses hMS).1
    (msPair_core_hypotheses hMS).2 e h

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters
