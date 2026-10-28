module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientInvariantSubgroup
public import Theory.GroupTheory.PCoreImageRestriction
public import Theory.GroupTheory.QuotientIntersection
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson

/-!
# The original two-core of XT

The faithful normal PSL₂(16) component in LT/O₂(LT) and the actual
order-five torus determine the two-core of the image of XT. Pulling it
back through the literal quotient recovers (T∩L)O₂(LT), with no new
Sylow or kernel premise.
Source: Aschbacher--Smith 6.1.4, printed p.665.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The actual source identity S=O₂(XT)=T_L O₂(LT). -/
theorem original_hermitian_quintic_sylow_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2)) :
    (quinticResidual T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let hi := h.reduced_enlargement.rankOneInput hout
  obtain ⟨D,hD,hDB,hDX,hX,_,_⟩ := original_hermitian_quintic_torus h hout hm
  let J := L ⊔ (T : Subgroup G)
  let B := L.subgroupOf J
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let Y := (quinticResidual T L ⊔ (T : Subgroup G)).subgroupOf J
  have hXL : quinticResidual T L ≤ L := (map_subtype_le _).trans inf_le_left
  have hYJ : quinticResidual T L ⊔ (T : Subgroup G) ≤ J :=
    sup_le (hXL.trans le_sup_left) le_sup_right
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer hi.sylow_normalizes)
  let q := QuotientGroup.mk' (pCore 2 J)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let K := B.map q
  let : K.Normal := (inferInstance : B.Normal).map q hq
  let Pq := P.mapSurjective hq
  let Yq := Y.map q
  let eb : B ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let eqB := QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb (pCore_map_iso 2 eb)
  let eK : K ≃* (L ⧸ pCore 2 L) := (coreQuotientEquivImage 2 B).symm.trans eqB
  let := hi.quotient_quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv eqB.symm
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv (coreQuotientEquivImage 2 B)
  have hsup : B ⊔ (P : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup (show L ≤ J from le_sup_left) le_sup_right,subgroupOf_self]
  have htwo : IsPGroup 2 ((J ⧸ pCore 2 J) ⧸ K) :=
    isPGroup_quotient_of_sup_eq_top K ((P : Subgroup J).map q) (P.isPGroup'.map q) (by
      rw [←Subgroup.map_sup,hsup,map_top_of_surjective q hq])
  have hz : center K = ⊥ := by
    apply bot_unique
    intro x hx
    apply eK.map_eq_one_iff.mp
    exact hi.quotient_center_eq_bot.le (MulEquivClass.apply_mem_center eK hx)
  have hCK : centralizer (K : Set (J ⧸ pCore 2 J)) = ⊥ :=
    (centralizer_eq_twoCore_of_centerless_quasisimple_quotient K hz htwo).trans
      (pCore_quotient_pCore_eq_bot 2)
  obtain ⟨e0,f0,hf0⟩ := hm
  let e := (eK.trans e0).trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL)
  have hF : Nat.card (Representation.OrthogonalFourMinus.FiniteModel.Field 2) = 16 := by
    exact (GaloisField.card 2 4 (by decide)).trans (by norm_num)
  have hPQY : (Pq : Subgroup (J ⧸ pCore 2 J)) ≤ Yq := map_mono (comap_mono le_sup_right)
  obtain ⟨S,hS⟩ := Pq.exists_subgroupOf_eq_of_normal K
  let D0 := D.subgroupOf J
  have hDL : D ≤ L := hDB.trans inf_le_left
  have hDJ : D ≤ J := hDL.trans le_sup_left
  have hD0B : D0 ≤ B := comap_mono hDL
  let Dq := D0.map q
  have hDqK : Dq ≤ K := map_mono hD0B
  let DK := Dq.subgroupOf K
  have hDq5 : Nat.card Dq = 5 := by
    have hD0c : Nat.card D0 = 5 := by rw [Nat.card_congr (subgroupOfEquivOfLe hDJ).toEquiv,hD]
    have hd : Disjoint D0 q.ker := by
      rw [QuotientGroup.ker_mk']
      obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := J)).exists_card_eq
      exact disjoint_of_coprime_natCard (by rw [hD0c,hk]; exact (by decide : Nat.Coprime 5 2).pow_right k)
    have hf : Function.Injective (q.subgroupMap D0) := by
      apply (injective_iff_map_eq_one _).mpr
      intro d hdq
      apply Subtype.ext
      exact disjoint_def.mp hd d.property (congrArg Subtype.val hdq)
    exact (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap D0) ⟨hf,q.subgroupMap_surjective D0⟩).toEquiv).symm.trans hD0c
  have hDK5 : Nat.card DK = 5 := by rw [Nat.card_congr (subgroupOfEquivOfLe hDqK).toEquiv,hDq5]
  have hkerP : q.ker ≤ (P : Subgroup J) := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal P
  have hUq : ((P : Subgroup J) ⊓ B).map q = (Pq : Subgroup (J ⧸ pCore 2 J)) ⊓ K := by
    rw [inf_comm,map_inf_of_ker_le q B (P : Subgroup J) hkerP,inf_comm]
    rfl
  have hDU : D0 ≤ normalizer (((P : Subgroup J) ⊓ B : Subgroup J) : Set J) := by
    have hn : D ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := hDB.trans inf_le_right
    have he : ((T : Subgroup G) ⊓ L).subgroupOf J = (P : Subgroup J) ⊓ B := rfl
    rw [←he,←subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ L ≤ J from inf_le_left.trans le_sup_right)]
    exact comap_mono hn
  have hDqN : Dq ≤ normalizer (((Pq : Subgroup (J ⧸ pCore 2 J)) ⊓ K : Subgroup (J ⧸ pCore 2 J)) : Set _) := by
    rw [←hUq]
    exact (map_mono hDU).trans (le_normalizer_map q)
  have hDKN : DK ≤ normalizer (S : Set K) := by
    change DK ≤ normalizer ((S : Subgroup K) : Set K)
    rw [hS,←inf_subgroupOf_right (Pq : Subgroup (J ⧸ pCore 2 J)) K,
      ←subgroupOf_normalizer_eq (show (Pq : Subgroup (J ⧸ pCore 2 J)) ⊓ K ≤ K from inf_le_right)]
    exact comap_mono hDqN
  have hDKY : DK.map K.subtype ≤ Yq := by
    rw [map_subgroupOf_eq_of_le hDqK]
    exact map_mono (comap_mono (hDX.trans le_sup_left))
  have hYN : Yq ≤ normalizer (((Pq : Subgroup (J ⧸ pCore 2 J)) ⊓ K : Subgroup (J ⧸ pCore 2 J)) : Set _) := by
    have hYnorm : quinticResidual T L ⊔ (T : Subgroup G) ≤
        normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
      apply sup_le ((map_subtype_le _).trans inf_le_right)
      exact (le_inf (T : Subgroup G).le_normalizer hi.sylow_normalizes).trans inf_normalizer_le_normalizer_inf
    have hnorm : Y ≤ normalizer (((P : Subgroup J) ⊓ B : Subgroup J) : Set J) := by
      rw [←show ((T : Subgroup G) ⊓ L).subgroupOf J = (P : Subgroup J) ⊓ B from rfl,
        ←subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ L ≤ J from inf_le_left.trans le_sup_right)]
      exact comap_mono hYnorm
    rw [←hUq]
    exact (map_mono hnorm).trans (le_normalizer_map q)
  have hcore := normal_quintic_twoCore_eq hF K e Pq Yq hPQY S hS DK hDK5 hDKN hDKY hCK hYN
  have hpre := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 q Y
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  have hPG : (P : Subgroup J).map J.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)
  have hBG : B.map J.subtype = L := map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left)
  have hPqpre : ((Pq : Subgroup (J ⧸ pCore 2 J)) ⊓ K).comap q =
      ((P : Subgroup J) ⊓ B) ⊔ pCore 2 J := by
    rw [←hUq,comap_map_eq,QuotientGroup.ker_mk']
  rw [hcore,hPqpre] at hpre
  have hle : ((P : Subgroup J) ⊓ B) ⊔ pCore 2 J ≤ Y :=
    sup_le (inf_le_left.trans (comap_mono le_sup_right))
      ((pCore_isPGroup.le_sylow_of_normal P).trans (comap_mono le_sup_right))
  rw [inf_eq_right.mpr hle] at hpre
  have heG := congrArg (Subgroup.map J.subtype) hpre.symm
  rw [map_pCoreIn_of_injective 2 Y J.subtype J.subtype_injective,
    map_subgroupOf_eq_of_le hYJ,Subgroup.map_sup,
    Subgroup.map_inf _ _ _ J.subtype_injective,hPG,hBG] at heG
  exact heG

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
