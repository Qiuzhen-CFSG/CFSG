module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsCoreEscape
public import Theory.GroupAction.FiveOnSixteenIrreducible
public import Theory.SpecificGroups.SL2.OddSylowCentralizer
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupAction.SubgroupConjugation

/-!
# The product of the two original cores is the full inner Sylow

The actual Tits core lies in the inner Sylow but escapes the original LT
core. Its image is a nontrivial subgroup of the original elementary group
of order sixteen, invariant under the same quintic torus. The fixed-free
five-action forces the image to be the entire original inner Sylow quotient.
All original groups, full cores, and source hypotheses are retained.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups

private theorem quintic_invariant_sylow
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 16) (P : Sylow 2 SL(2,F))
    (D A : Subgroup SL(2,F)) (hD : Nat.card D = 5)
    (hDP : D ≤ normalizer (P : Set SL(2,F)))
    (hAP : A ≤ P) (hDA : D ≤ normalizer (A : Set SL(2,F)))
    (hA : A ≠ ⊥) : A = P := by
  let : Normalizes D (P : Subgroup SL(2,F)) := ⟨hDP⟩
  have hP : Nat.card P = 16 :=
    (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P).symm.toEquiv).trans hF
  have hfixed : FixedPoints.subgroup D (P : Subgroup SL(2,F)) = ⊥ := by
    obtain ⟨d,hd⟩ : ∃ d : D, d ≠ 1 := by
      have hn : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      exact exists_ne 1
    apply bot_unique
    intro r hr
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.eq_one_of_sylow_commutes_nontrivial_odd P r d r.property
      (fun he => hd (Subtype.ext he)) (by decide : Odd 5)
      (by simpa [hD] using congrArg Subtype.val (pow_card_eq_one' (x := d)))
    have he := congrArg Subtype.val (hr d)
    change (d : SL(2,F)) * (r : SL(2,F)) * (d : SL(2,F))⁻¹ = (r : SL(2,F)) at he
    exact (show Commute (d : SL(2,F)) (r : SL(2,F)) from
      mul_inv_eq_iff_eq_mul.mp he).symm
  let AP := A.subgroupOf (P : Subgroup SL(2,F))
  let : IsInvariant D (P : Subgroup SL(2,F)) AP := ⟨fun d r => by
    change (r : SL(2,F)) ∈ A ↔ ((d : SL(2,F)) * (r : SL(2,F)) * (d : SL(2,F))⁻¹ ∈ A)
    exact mem_normalizer_iff.mp (hDA d.property) r⟩
  rcases invariant_eq_bot_or_top_of_five_actor hD hP hfixed AP with hb | ht
  · apply False.elim (hA _)
    have hh := congrArg (Subgroup.map (P : Subgroup SL(2,F)).subtype) hb
    simpa only [AP,map_subgroupOf_eq_of_le hAP,Subgroup.map_bot] using hh
  · have hh := congrArg (Subgroup.map (P : Subgroup SL(2,F)).subtype) ht
    simpa only [AP,map_subgroupOf_eq_of_le hAP,←MonoidHom.range_eq_map,range_subtype] using hh

private theorem quintic_invariant_inner_sylow
    {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 16) (C : Subgroup H) [C.Normal]
    (e : C ≃* SL(2,F)) (P : Sylow 2 H) (D A : Subgroup H)
    (hD : Nat.card D = 5) (hDC : D ≤ C)
    (hDP : D ≤ normalizer (((P : Subgroup H) ⊓ C) : Set H))
    (hAP : A ≤ (P : Subgroup H) ⊓ C)
    (hDA : D ≤ normalizer (A : Set H)) (hA : A ≠ ⊥) :
    A = (P : Subgroup H) ⊓ C := by
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal C
  let DC := D.subgroupOf C
  let AC := A.subgroupOf C
  let P' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hAC : A ≤ C := hAP.trans inf_le_right
  have hACP : AC ≤ (S : Subgroup C) := by
    rw [hS]
    exact comap_mono (hAP.trans inf_le_left)
  have hDCP : DC ≤ normalizer (S : Set C) := by
    change DC ≤ normalizer ((S : Subgroup C) : Set C)
    rw [hS,←inf_subgroupOf_right (P : Subgroup H) C,
      ←subgroupOf_normalizer_eq (show (P : Subgroup H) ⊓ C ≤ C from inf_le_right)]
    exact comap_mono hDP
  have hDCA : DC ≤ normalizer (AC : Set C) := by
    rw [←subgroupOf_normalizer_eq hAC]
    exact comap_mono hDA
  have hDC5 : Nat.card DC = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv).trans hD
  have hACne : AC.map e.toMonoidHom ≠ ⊥ := by
    intro he
    have hb : AC = ⊥ := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      simpa only [Subgroup.map_bot] using he
    have hh := congrArg (Subgroup.map C.subtype) hb
    exact hA (by simpa only [AC,map_subgroupOf_eq_of_le hAC,Subgroup.map_bot] using hh)
  have heq := quintic_invariant_sylow hF P' (DC.map e.toMonoidHom)
    (AC.map e.toMonoidHom)
    (by rw [card_map_of_injective e.injective,hDC5])
    ((map_mono hDCP).trans (le_normalizer_map e.toMonoidHom))
    (map_mono hACP) ((map_mono hDCA).trans (le_normalizer_map e.toMonoidHom)) hACne
  have heqC : AC = (S : Subgroup C) := Subgroup.map_injective e.injective heq
  have hh := congrArg (Subgroup.map C.subtype) heqC
  rw [map_subgroupOf_eq_of_le hAC,hS,subgroupOf_map_subtype] at hh
  exact hh

open Theory.GroupTheory Stellmacher Representation
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- The full original Tits core and the full original LT core generate
exactly the original inner Sylow; neither quotient kernel is replaced. -/
theorem original_hermitian_tits_core_sup_original_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    (K ⊔ (T : Subgroup G)).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      ((T : Subgroup G) ⊓ L) ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let R := (K ⊔ (T : Subgroup G)).pCoreIn 2
  let U := (T : Subgroup G) ⊓ L
  let S := U ⊔ Q
  let C := L.subgroupOf J
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let q := QuotientGroup.mk' (pCore 2 J)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let hi := h.reduced_enlargement.rankOneInput hout
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer hi.sylow_normalizes)
  let N := C.map q
  let : N.Normal := (inferInstance : C.Normal).map q hq
  let ec : C ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let eqc := QuotientGroup.congr (pCore 2 C) (pCore 2 L) ec (pCore_map_iso 2 ec)
  let := hi.quotient_quasisimple
  let : IsQuasisimple (C ⧸ pCore 2 C) := IsQuasisimple.of_mulEquiv eqc.symm
  let eN : N ≃* (L ⧸ pCore 2 L) := (coreQuotientEquivImage 2 C).symm.trans eqc
  have hm' := hm
  obtain ⟨eL,f,hf⟩ := hm'
  let en := eN.trans eL
  let Pq := P.mapSurjective hq
  let Rj := R.subgroupOf J
  let Rq := Rj.map q
  have hQJ : Q ≤ J := map_subtype_le _
  have hUJ : U ≤ J := inf_le_left.trans le_sup_right
  have hSJ : S ≤ J := sup_le hUJ hQJ
  have hRS : R ≤ S := original_hermitian_tits_core_le_inner_sylow
    h hout hm hM₁ hCM₁ hK hnot hqK e
  have hRJ : R ≤ J := hRS.trans hSJ
  have hQsub : Q.subgroupOf J = pCore 2 J := by
    change ((pCore 2 J).map J.subtype).comap J.subtype = pCore 2 J
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hSimage : (S.subgroupOf J).map q = (Pq : Subgroup _) ⊓ N := by
    have hkerP : q.ker ≤ (P : Subgroup J) := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal P
    have hUq : ((P : Subgroup J) ⊓ C).map q = (Pq : Subgroup _) ⊓ N := by
      rw [inf_comm,map_inf_of_ker_le q C (P : Subgroup J) hkerP,inf_comm]
      rfl
    have hmapQ : (pCore 2 J).map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
    rw [show S = U ⊔ Q from rfl,subgroupOf_sup hUJ hQJ,Subgroup.map_sup,hQsub,
      hmapQ,sup_bot_eq]
    exact hUq
  have hRne : Rq ≠ ⊥ := by
    intro he
    have hk : Rj ≤ q.ker := (map_eq_bot_iff Rj).mp he
    rw [QuotientGroup.ker_mk'] at hk
    apply original_hermitian_tits_core_not_le_original_core
      h hout hm hM₁ hCM₁ hK hnot hqK e
    have hh := map_mono (f := J.subtype) hk
    rwa [map_subgroupOf_eq_of_le hRJ] at hh
  have hRqP : Rq ≤ (Pq : Subgroup _) ⊓ N := by
    rw [←hSimage]
    exact map_mono (comap_mono hRS)
  obtain ⟨D,hD,hDB,hDX,_,_,_⟩ := original_hermitian_quintic_torus h hout hm
  have hDL : D ≤ L := hDB.trans inf_le_left
  have hDJ : D ≤ J := hDL.trans le_sup_left
  let Dj := D.subgroupOf J
  let Dq := Dj.map q
  have hDqN : Dq ≤ N := map_mono (comap_mono hDL)
  have hDq5 : Nat.card Dq = 5 := by
    have hDj5 : Nat.card Dj = 5 :=
      (Nat.card_congr (subgroupOfEquivOfLe hDJ).toEquiv).trans hD
    have hdis : Disjoint Dj q.ker := by
      rw [QuotientGroup.ker_mk']
      obtain ⟨a,ha⟩ := (pCore_isPGroup (p := 2) (G := J)).exists_card_eq
      exact disjoint_of_coprime_natCard (by rw [hDj5,ha]; exact (by decide : Nat.Coprime 5 2).pow_right a)
    have hqi : Function.Injective (q.subgroupMap Dj) := by
      apply (injective_iff_map_eq_one _).mpr
      intro d hd
      apply Subtype.ext
      exact disjoint_def.mp hdis d.property (congrArg Subtype.val hd)
    exact (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap Dj)
      ⟨hqi,q.subgroupMap_surjective Dj⟩).toEquiv).symm.trans hDj5
  have hDN : D ≤ normalizer (S : Set G) := by
    rw [show S = ((T : Subgroup G) ⊓ L) ⊔ J.pCoreIn 2 from rfl,
      ←original_hermitian_quintic_sylow_core h hout hm]
    exact (hDX.trans le_sup_left).trans
      ((quinticResidual T L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _
          (pCore 2 (quinticResidual T L ⊔ (T : Subgroup G) : Subgroup G))))
  have hDjS : Dj ≤ normalizer (S.subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq hSJ]
    exact comap_mono hDN
  have hDqP : Dq ≤ normalizer
      (((Pq : Subgroup (J ⧸ pCore 2 J)) ⊓ N : Subgroup (J ⧸ pCore 2 J)) : Set (J ⧸ pCore 2 J)) := by
    rw [←hSimage]
    exact (map_mono hDjS).trans (le_normalizer_map q)
  have hDR : D ≤ normalizer (R : Set G) := by
    have hXK := original_hermitian_quintic_le_tits_component
      h hout hm hM₁ hCM₁ hK hnot hqK e
    exact (hDX.trans (hXK.trans le_sup_left)).trans
      ((K ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G))))
  have hDjR : Dj ≤ normalizer (Rj : Set J) := by
    rw [←subgroupOf_normalizer_eq hRJ]
    exact comap_mono hDR
  have heq : Rq = (Pq : Subgroup _) ⊓ N := quintic_invariant_inner_sylow
    (by exact (GaloisField.card 2 4 (by decide)).trans (by norm_num))
    N en Pq Dq Rq hDq5 hDqN hDqP hRqP
    ((map_mono hDjR).trans (le_normalizer_map q)) hRne
  have hh : Rj ⊔ pCore 2 J = S.subgroupOf J := by
    have hh := congrArg (Subgroup.comap q) (heq.trans hSimage.symm)
    rw [comap_map_eq,comap_map_eq,QuotientGroup.ker_mk'] at hh
    have hQS : pCore 2 J ≤ S.subgroupOf J := by
      rw [←hQsub]
      exact comap_mono le_sup_right
    rwa [sup_eq_left.mpr hQS] at hh
  have hmap := congrArg (Subgroup.map J.subtype) hh
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hRJ,map_subgroupOf_eq_of_le hSJ] at hmap
  exact hmap

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
