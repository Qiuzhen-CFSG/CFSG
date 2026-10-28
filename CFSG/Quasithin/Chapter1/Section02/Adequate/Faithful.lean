module

public import CFSG.Quasithin.Chapter1.Section02.Adequate.Chains
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Global
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.Order.MaximalUpward

/-!
# Faithful local components along a chain

The Sylow intersection with a subnormal component is Sylow in that component.
Consequently N_T(B) is Sylow in B N_T(B). The two-core of this join is the
actual section centralizer C_{N_T(B)}(B/O₂(B)), by maximal signalizers.

Once the normalizers along a chain agree, these facts verify every local
Sylow and core hypothesis of A.4.10. Its full source implication then gives
the module inequality in 1.2.9(1) and upward closure in the canonical faithful
family. The order argument gives 1.2.9(2). The common-normalizer assertion
and A.4.10 remain explicit earlier inputs; this is a conditional deduction.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
A.4.2(5), A.4.10, pp.57–60, and Lemma 1.2.9, p.507.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.Section02.Adequate
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

/-- The actual local normalizer is Sylow in its product with the component. -/
theorem local_normalizer_isSylow {S B : Subgroup G} (hB : B ∈ L G S) :
    IsSylowIn 2 (S ⊓ normalizer (B : Set G))
      (B ⊔ (S ⊓ normalizer (B : Set G))) := by
  obtain ⟨P, hP⟩ := IndexTwo.isSylowIn_inf_of_subnormal hB.2.1 le_sup_left hB.1.subnormal
  apply IsPGroup.exists_sylow_sup_of_coprime_index B _
    ((isSylowIn_iff.mp hB.2.1).1.to_le inf_le_left) inf_le_right
    (P : Subgroup B) P.not_dvd_index
  rw [hP]
  exact le_inf inf_le_left (inf_le_right.trans B.le_normalizer)

/-- The source identity O₂(B N_S(B)) = C_{N_S(B)}(B/O₂(B)),
with both intrinsic cores and the action centralizer retained. -/
theorem local_normalizer_core_eq_sectionCentralizer {S B : Subgroup G}
    (hB : B ∈ L G S) :
    (B ⊔ (S ⊓ normalizer (B : Set G))).pCoreIn 2 =
      twoSectionCentralizer B (S ⊓ normalizer (B : Set G)) := by
  let R := S ⊓ normalizer (B : Set G)
  let J := B ⊔ R
  have hRJ : R ≤ J := le_sup_right
  have hBJ : B ≤ J := le_sup_left
  have hJB : J ≤ normalizer (B : Set G) := sup_le B.le_normalizer inf_le_right
  have hsub : (B.subgroupOf J).IsSubnormal :=
    (normal_subgroupOf_of_le_normalizer hJB).isSubnormal
  obtain ⟨P, hP⟩ := local_normalizer_isSylow hB
  have hQR : J.pCoreIn 2 ≤ R := (pCoreIn_le_sylow J P).trans_eq hP
  have hBQ : B.pCoreIn 2 ≤ J.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn B J 2 hBJ hsub
  have hmax : IsMaximalTwoSignalizer B J (J.pCoreIn 2) := by
    have hm := normal_sylow_core_isMaximal B J hBJ hJB (mem_L_isPPerfect hB) P
    rw [hP] at hm
    exact hm
  have hc : J.pCoreIn 2 ≤ twoSectionCentralizer B R := by
    rw [le_twoSectionCentralizer_iff]
    have hs := ((isMaximalTwoSignalizer_iff _ _ _).mp hmax).1
    exact ⟨hQR, hQR.trans inf_le_right,
      signalizer_commutator_le_pCore B J _ hBJ hsub (mem_L_isPPerfect hB) hs⟩
  have hBC : B.pCoreIn 2 ≤ twoSectionCentralizer B R := hBQ.trans hc
  have hCB : ⁅B, twoSectionCentralizer B R⁆ ≤ B.pCoreIn 2 :=
    ((le_twoSectionCentralizer_iff B R _).mp le_rfl).2.2
  have hsig : IsTwoSignalizer B J (twoSectionCentralizer B R) := by
    apply (isTwoSignalizer_iff _ _ _).mpr
    refine ⟨(twoSectionCentralizer_le B R).trans hRJ,
      ((isSylowIn_iff.mp hB.2.1).1.to_le inf_le_left).to_le
        (twoSectionCentralizer_le B R), ?_⟩
    exact le_normalizer_iff_commutator_le_right.mpr (hCB.trans hBC)
  exact le_antisymm hc (((isMaximalTwoSignalizer_iff _ _ _).mp hmax).2 _ hsig hc)

/-- The exact universal A.4.10 implication, retaining the section centralizer,
the two Sylow conditions, the core bound, and all three conclusions.
This is an explicit earlier theorem input, not a proof of A.4.10. -/
def A410EarlierResult (G : Type*) [Group G] : Prop :=
  ∀ X Y U : Subgroup G, X ≤ Y → IsSignalizerType X → IsSignalizerType Y →
    U ≤ normalizer (Y : Set G) → IsSylowIn 2 U (Y ⊔ U) →
    (Y ⊔ U).pCoreIn 2 ≤ U ⊓ normalizer (X : Set G) →
    IsSylowIn 2 (U ⊓ normalizer (X : Set G)) ((Y ⊔ U) ⊓ normalizer (X : Set G)) →
    IsMaximalTwoSignalizer X ((Y ⊔ U) ⊓ normalizer (X : Set G))
      (twoSectionCentralizer X U) ∧
    signalizerModule X (twoSectionCentralizer X U) ≤
      signalizerModule Y ((Y ⊔ U).pCoreIn 2) ∧
    (IsFaithfulSignalizerType X → IsFaithfulSignalizerType Y)

/-- The module inequality and faithful upward closure of 1.2.9(1), conditional
on A.4.10 and the earlier normalizer equality of 1.2.8(1). -/
theorem faithful_chain_of_A410_of_normalizer_eq (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T) (hA410 : A410EarlierResult G)
    {B K : Subgroup G} (hB : B ∈ MainForward.faithfulLocalComponents T)
    (hK : K ∈ L G T) (hBK : B ≤ K)
    (hN : (T : Subgroup G) ⊓ normalizer (B : Set G) =
      (T : Subgroup G) ⊓ normalizer (K : Set G)) :
    signalizerModule B ((B ⊔ ((T : Subgroup G) ⊓ normalizer (B : Set G))).pCoreIn 2) ≤
      signalizerModule K ((K ⊔ ((T : Subgroup G) ⊓ normalizer (K : Set G))).pCoreIn 2) ∧
    K ∈ MainForward.faithfulLocalComponents T := by
  obtain ⟨hBL, hBf⟩ := (mem_faithfulLocalComponents_iff T B).mp hB
  let R := (T : Subgroup G) ⊓ normalizer (K : Set G)
  have hRB : R ≤ normalizer (B : Set G) := hN.symm.le.trans inf_le_right
  have hSyl : IsSylowIn 2 R (K ⊔ R) := local_normalizer_isSylow hK
  have hcore : (K ⊔ R).pCoreIn 2 ≤ R := by
    obtain ⟨P, hP⟩ := hSyl
    exact (pCoreIn_le_sylow _ P).trans_eq hP
  have hSylN : IsSylowIn 2 (R ⊓ normalizer (B : Set G))
      ((K ⊔ R) ⊓ normalizer (B : Set G)) := by
    rw [inf_of_le_left hRB]
    exact hSyl.restrict (le_inf le_sup_right hRB) inf_le_left
  have ha := hA410 B K R hBK hBf.1 (mem_L_isSignalizerType T hE hK)
    inf_le_right hSyl (le_inf hcore (hcore.trans hRB)) hSylN
  refine ⟨?_, (mem_faithfulLocalComponents_iff T K).mpr ⟨hK, ha.2.2 hBf⟩⟩
  rw [local_normalizer_core_eq_sectionCentralizer hBL, hN]
  exact ha.2.1

/-- Under the earlier chain theorem and A.4.10, maximality in the faithful
family is exactly maximality in the full canonical family plus faithfulness. -/
theorem faithful_maximal_iff_of_A410_of_normalizer_eq (T : Sylow 2 G)
    (hE : IsEvenCharacteristicAt T) (hA410 : A410EarlierResult G)
    (hN : ∀ B K : Subgroup G, B ∈ L G T → K ∈ L G T → B ≤ K →
      (T : Subgroup G) ⊓ normalizer (B : Set G) =
        (T : Subgroup G) ⊓ normalizer (K : Set G)) (B : Subgroup G) :
    Maximal (fun K => K ∈ MainForward.faithfulLocalComponents T) B ↔
      B ∈ LStar G T ∧ IsFaithfulSignalizerType B := by
  have hup {X Y : Subgroup G} (hX : X ∈ L G T) (hY : Y ∈ L G T)
      (hXf : IsFaithfulSignalizerType X) (hXY : X ≤ Y) : IsFaithfulSignalizerType Y := by
    have hf := (faithful_chain_of_A410_of_normalizer_eq T hE hA410
      ((mem_faithfulLocalComponents_iff T X).mpr ⟨hX, hXf⟩) hY hXY
      (hN X Y hX hY hXY)).2
    exact ((mem_faithfulLocalComponents_iff T Y).mp hf).2
  have hstar (X : Subgroup G) : Maximal (fun Y => Y ∈ L G T) X ↔ X ∈ LStar G T := by
    exact ⟨fun h => ⟨h.1, fun Y hY hXY => le_antisymm (h.2 hY hXY) hXY⟩,
      fun h => ⟨h.1, fun Y hY hXY => (h.2 Y hY hXY).le⟩⟩
  simp only [mem_faithfulLocalComponents_iff]
  rw [Theory.maximal_and_iff_of_upward_closed @hup, hstar]

end CFSG.Quasithin.Chapter1.Section02.Adequate
