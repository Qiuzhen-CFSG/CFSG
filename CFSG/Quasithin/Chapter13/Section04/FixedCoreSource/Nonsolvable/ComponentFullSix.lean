module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullOrbit
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentNaturalResidual
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ComponentCentralizer
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.ReducedNormal.QuasisimpleImage
public import Theory.SpecificGroups.Alternating.TwoThreeCycles

/-!
# The full A₆ component orbit in an involution centralizer

A normal ordinary A₆ component has three-rank two. The rank-addition
argument therefore makes the centralizer of its faithful reduced image
prime to three. This selects the quasisimple B.5.6 row without using the
legacy splitting assertion for the outer A₆–C₃ case. Order 360 eliminates
the reducible B.5.1 alternatives and gives Irr⁺ minimality.

Apply that minimality to Q=[⟨Ω₁Z(T)^C_G(z)⟩,K]. Its nonzero fully moved
subgroup U=[⟨Ω₁Z(T)^K⟩,K] is all of Q. The central seed splitting then
identifies the full orbit with the original one and makes U normal in
C_G(z). Both natural and five-dimensional augmentation rows are retained.
The next full-centralizer module consumes these identities to prove H=KT.

Earlier Chapter12/13.3 inputs retain their original producers and final
discharge with qt-d-1341-fixed-core-source. The comparison, reciprocal
commutator and graph arguments remain with this owner. Both escaping
weights still require nonsolvability.
Source: Aschbacher–Smith B.5.1, B.5.6 and 13.4.10(7), pp.99,105,909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem six_center_eq_bot {A : Type*} [Group A]
    (e : A ≃* alternatingGroup (Fin 6)) : center A = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have he : e x = 1 := (alternatingGroup.center_eq_bot (by simp)).le
    ((centerCongr e) ⟨x,hx⟩).property
  exact e.injective (he.trans e.map_one.symm)

private theorem reduced_six_centralizer_three_free
    (K U : Subgroup G) [K.Normal] [U.Normal]
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hr : IsPReduced 2 U) (hm : ⁅U,K⁆ ≠ ⊥)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hrank : primeRank 3 G ≤ 2) :
    Nat.Coprime 3 (Nat.card (centralizer
      (K.map (QuotientGroup.mk' (centralizer (U : Set G))) :
        Set (G ⧸ centralizer (U : Set G))))) := by
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  let B := K.map q
  let C := centralizer (B : Set (G ⧸ centralizer (U : Set G)))
  let P := C.comap q
  have hz := six_center_eq_bot e
  have hker := reduced_quasisimple_subgroupMap_ker U K hr hz hm
  have hc : ⁅(pResidual 2 P).map P.subtype,K⁆ ≤ K.pCoreIn 2 := by
    apply commutator_le.mpr
    intro x hx k hk
    have hxP : x ∈ P := map_subtype_le _ hx
    have hcomm : ⁅x,k⁆ ∈ K := (commutator_le_right (⊤ : Subgroup G) K)
      (commutator_mem_commutator (mem_top x) hk)
    have hzero : q ⁅x,k⁆ = 1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact (mem_centralizer_iff.mp hxP (q k) (mem_map_of_mem q hk)).symm
    have hcore : (⟨⁅x,k⁆,hcomm⟩ : K) ∈ pCore 2 K := by
      rw [←hker]
      exact Subtype.ext hzero
    exact mem_map_of_mem K.subtype hcore
  have hrK : 2 ≤ primeRank 3 K := by
    have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
    rw [←primeRank_congr 3 e,
      primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup] at hh
    exact hh
  have hb := ResidualCentralizerRank.primeRank_sum_le_of_normal_factor
    (by decide : Odd 3) P K hc (by simp [hz])
  have hp : Nat.Coprime 3 (Nat.card P) := Nat.prime_three.coprime_iff_not_dvd.mpr
    (PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega : primeRank 3 P = 0))
  exact hp.coprime_dvd_right (card_dvd_of_surjective (q.subgroupComap C)
    (q.subgroupComap_surjective_of_surjective C (QuotientGroup.mk'_surjective _)))

/-- A reduced subgroup fully moved by a normal ordinary A₆ component is Irr⁺,
including when the ambient overgroup has odd-order elements outside KT. -/
theorem full_six_reduced_component_minimal
    (S : Sylow 2 G) (K U : Subgroup G) [K.Normal] [U.Normal]
    [IsElementaryAbelian 2 U]
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hred : IsPReduced 2 U) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hgen : ⁅K,elementaryAbelianMaxJ (S : Subgroup G)⁆ = K)
    (hmove : ⁅U,K⁆ = U) (hne : U ≠ ⊥) :
    ∀ A : Subgroup G, A ≤ U → K ≤ normalizer (A : Set G) →
      A = U ∨ A ≤ centralizer (K : Set G) := by
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let N := offenderSubgroup ρ
  let Bq := K.map q
  let B := Bq.subgroupOf N
  have hcore : K.pCoreIn 2 ≤ C := by
    have hc : K.pCoreIn 2 ≤ pCore 2 G := by
      change (pCore 2 K).map K.subtype ≤ pCore 2 G
      exact le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
    exact hc.trans (le_centralizer_iff.mp hred.le_centralizer_pCore)
  have hBq : Bq ≤ N := by
    have hJT := ChapterB.RankOneBaumann.thompson_image_le_offender_layer S U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      (hred.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)) N le_rfl
    let : N.Normal := offenderSubgroup_normal ρ
    change K.map q ≤ N
    rw [←hgen,map_commutator]
    exact (commutator_mono le_rfl hJT).trans (commutator_le_right _ _)
  have hcompq : IsComponent (G ⧸ C) Bq :=
    hK.isComponent_map_of_twoCore_killed hqK q (QuotientGroup.mk'_surjective C)
      (by rwa [QuotientGroup.ker_mk']) (by
        intro he
        have hc : K ≤ C := by
          simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff K).mp he
        exact hne (hmove.symm.trans
          (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))))
  have hcomp : IsComponent N B := hcompq.subgroupOf hBq
  let : Nontrivial B := (nontrivial_iff_ne_bot _).mpr hcomp.isCComponent.ne_bot
  let : Nontrivial N := Function.Injective.nontrivial (f := B.subtype) Subtype.val_injective
  have ha := ChapterB.offender_restriction_classification ρ
    ChapterB.SourceInduction.adequateClassification_knownSimple
    (NormalElementaryQuotient.representation_injective U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C))
    hred.quotient_pCore_eq_bot
    ⟨{ Cover := G, kernel := C, sqtk := hG, equiv := MulEquiv.refl _ }⟩
  let : Bq.Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective C)
  let : B.Normal := inferInstance
  have hmov : moved ρ Bq = ⊤ := by
    change subspaceCommutator (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) ⊤ (K.map q) = ⊤
    rw [←NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) K]
    change AddSubgroup.toZModSubmodule 2 ((⁅U,K⁆ : Subgroup G).subgroupOf U).toAddSubgroup = ⊤
    rw [hmove,subgroupOf_self]
    rfl
  let := hqK
  have hnon : ⁅U,K⁆ ≠ ⊥ := by rwa [hmove]
  let eb := (subgroupOfEquivOfLe hBq).trans
    ((reducedQuasisimpleImageEquiv U K hred (six_center_eq_bot eK) hnon).symm.trans eK)
  have hcard : Nat.card B = 360 := by
    rw [Nat.card_congr eb.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hc : Nat.Coprime 3 (Nat.card (centralizer (B : Set N))) := by
    have hle : (centralizer (B : Set N)).map N.subtype ≤
        centralizer (Bq : Set (G ⧸ C)) := by
      rintro _ ⟨x,hx,rfl⟩ b hb
      exact congrArg N.subtype (hx ⟨b,hBq hb⟩ hb)
    have hh := (reduced_six_centralizer_three_free K U hred hnon eK
      (hG.stronglyQuasithin 3 (by decide) (by decide))).coprime_dvd_right
        (card_dvd_of_le hle)
    rwa [card_map_of_injective N.subtype_injective] at hh
  obtain ⟨_,⟨c⟩⟩ := ha.quasisimple_of_component_three_free_centralizer hcomp hc
  change subspaceCommutator ρ ⊤ Bq = ⊤ at hmov
  have hi := c.card360_moved_irrPlus hcard
  rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hBq,hmov] at hi
  have hi' : IsIrrPlus ρ Bq ⊤ := (IsIrrPlus.subgroupOf_iff ρ Bq N hBq _).mp hi
  intro A hAU hn
  let I : Submodule (ZMod 2) (Additive U) := (A.subgroupOf U).toAddSubgroup.toZModSubmodule 2
  have hI : Bq ≤ subspaceStabilizer ρ I := by
    apply le_subspaceStabilizer
    rintro b ⟨k,hk,rfl⟩ v hv
    change ((ρ (q k) v).toMul : G) ∈ A
    rw [NormalElementaryQuotient.representation_apply]
    exact (mem_normalizer_iff.mp (hn hk) _).mp hv
  rcases hi'.eq_or_le_fixedSpace ρ hI le_top with he | hc
  · left
    apply le_antisymm hAU
    intro a ha
    have hh : Additive.ofMul (⟨a,ha⟩ : U) ∈ I := he.symm ▸ Submodule.mem_top
    exact hh
  · right
    intro a ha k hk
    have hh := hc (show Additive.ofMul (⟨a,hAU ha⟩ : U) ∈ I from ha)
      ⟨q k,mem_map_of_mem q hk⟩
    have hh' := congrArg (fun w : Additive U => w.toMul.val) hh
    change ((NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      (q k) (Additive.ofMul ⟨a,hAU ha⟩)).toMul : G) = a at hh'
    rw [NormalElementaryQuotient.representation_apply] at hh'
    exact mul_inv_eq_iff_eq_mul.mp hh'

variable {T : Sylow 2 G} {L K V : Subgroup G}

/-- The full A₆ centralizer has the same moved module and seed orbit as K. -/
theorem ordinary_six_full_orbit_eq
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    let H := centralizer ({z.val} : Set G)
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    ⁅conjugateSpanBy Z H,K⁆ = ⁅conjugateSpanBy Z K,K⁆ ∧
      conjugateSpanBy Z H = conjugateSpanBy Z K ∧
      H ≤ normalizer ((⁅conjugateSpanBy Z K,K⁆ : Subgroup G) : Set G) := by
  have hKz := hK.1
  let H := centralizer ({z.val} : Set G)
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := ⁅conjugateSpanBy Z K,K⁆
  let Q := ⁅conjugateSpanBy Z H,K⁆
  let A := K.subgroupOf H
  let B := Q.subgroupOf H
  let B₀ := U.subgroupOf H
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have hTH := Solvable.original_sylow_le_centralizer hzT
  have hTK := hTH.trans hHN
  let S := T.subtype hTH
  obtain ⟨_,hrQ,_,hsplit,hmove,hne,hUQ,hQW,hnQ,_⟩ := component_full_orbit h₀ h structural
    D m hindex z hzT hzL hKz hHN hKM
  have hQH : Q ≤ H := hQW.trans (Solvable.centralizerOmegaOrbit_le hzT)
  have hUH : U ≤ H := hUQ.trans hQH
  obtain ⟨DK,_,_,_,_,_,_,_,_,_⟩ := ordinary_six_component_geometry h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
  let : A.Normal := normal_subgroupOf_of_le_normalizer hHN
  let : B.Normal := hrQ.normal
  let : IsElementaryAbelian 2 B := hrQ.elementary
  let a := subgroupOfEquivOfLe hKz
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let b := subgroupOfEquivOfLe hQH
  let := component_quotient_quasisimple h1332 hfK
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv aq.symm
  have hcomp : A.IsCComponent := by
    have ht : (⊤ : Subgroup K).IsCComponent := by
      have hh := hfK.1.1.subgroupOf_of_le (le_refl K) (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)
      simpa only [subgroupOf_self] using hh
    have htA : (⊤ : Subgroup A).IsCComponent := by
      simpa only [map_top_of_surjective a.symm.toMonoidHom a.symm.surjective] using ht.map_equiv a.symm
    have hh := htA.map_subtype (inferInstance : A.Normal).isSubnormal
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
    h₀.qtke.involution_centralizer_sqtk (orderOf_eq_prime
      ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1)
  have hgenA : ⁅A,elementaryAbelianMaxJ (S : Subgroup H)⁆ = A := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hKz,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    change ⁅K,elementaryAbelianMaxJ (((T : Subgroup G).subgroupOf H).map H.subtype)⁆ = K
    rw [map_subgroupOf_eq_of_le hTH]
    exact component_thompson_generation (D := D) h₀ h structural h1332 hzT hHN hKM hfK
  have hBmove : ⁅B,A⁆ = B := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hQH,map_subgroupOf_eq_of_le hKz]
    exact hmove
  have hBne : B ≠ ⊥ := by
    intro hh
    have hm := congrArg (map H.subtype) hh
    rw [map_subgroupOf_eq_of_le hQH,Subgroup.map_bot] at hm
    exact hne hm
  have hmin := full_six_reduced_component_minimal S A B hSQ hrQ hcomp hqA
    (aq.trans eK) hgenA hBmove hBne
  have hB₀B : B₀ ≤ B := comap_mono hUQ
  have hn : A ≤ normalizer (B₀ : Set H) := by
    intro k hk
    apply mem_normalizer_iff.mpr
    intro v
    exact mem_normalizer_iff.mp (DK.normalizes hk) v.val
  have hB₀move : ⁅B₀,A⁆ = B₀ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hKz]
    exact component_moved_eq_commutator h₀ hzT hz1 hKz hTK
  have hB₀ne : B₀ ≠ ⊥ := by
    intro hh
    have hm := congrArg (map H.subtype) hh
    rw [map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hm
    exact DK.ne_bot hm
  have heq : B₀ = B := (hmin B₀ hB₀B hn).resolve_right (by
    intro hc
    have hh := commutator_eq_bot_iff_le_centralizer.mpr hc
    rw [hB₀move] at hh
    exact hB₀ne hh)
  have hU : U = Q := by
    have hm := congrArg (map H.subtype) heq
    change (U.subgroupOf H).map H.subtype = (Q.subgroupOf H).map H.subtype at hm
    rwa [map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hQH] at hm
  have hseed := component_seed_split h₀ hzT hz1 hKz hTK
  rw [component_full_fixed_line h structural z.val hz1 hzT hindex K hKz hKM] at hseed
  refine ⟨hU.symm,?_,?_⟩
  · exact hsplit.trans ((congrArg (fun W : Subgroup G => W ⊔ zpowers z.val) hU.symm).trans hseed.symm)
  · change H ≤ normalizer (U : Set G)
    rw [hU]
    exact hnQ

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
