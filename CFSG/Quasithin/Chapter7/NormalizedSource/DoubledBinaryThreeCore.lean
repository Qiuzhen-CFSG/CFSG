module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.Block
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MSRestriction

/-!
# Whole commutator-core recognition in the surviving binary-three branch

The original cubic base supplies the genuine MS2(a) witness on KQ, and
characteristic-normalizer control supplies MS3. The order-64 subgroup
[Omega_1 Z(O_2(KQ)), K] is fully moved by K. If the full commutator core
were nonabelian, characteristic replacement would carry this subgroup into
the replacement central omega group. The proved MS93 common reduction
identifies its moving part with the natural binary three-space, of order
eight, a contradiction. This argument retains the fixed factor and needs
no bound on its order or ambient centrality.

The genuine abelian MS recognition and fixed-kernel bounds then make the
whole commutator core elementary of order 64, equal to the original star
moved subgroup, and give two equal natural copies with literal component
conjugation. The Chapter12 companion applies this to the original chosen
paired-plane orbit. The whole ambient two-core is not identified here.

Source: Aschbacher--Smith, proof after 7.7.10, printed p.709, C.1.31--34,
pp.135--137; Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of
rank two (1993), Sections 3--4 and 7, especially the characteristic
replacement on pp.932--933. Sources: refs/quasithin.pdf and
refs/Pushing up weak BN-pairs of rank two.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeCore
open ChapterC.BinaryMS ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
variable {J : Type*} [Group J] [Finite J] {κ : GroupClass} {K R : Subgroup J}

/-- Characteristic replacement preserves a fully moved central omega subgroup.
The nonabelian source reduction allows only a natural three-space there. -/
theorem abelian_of_large_moving_omega
    (h : ChapterC.BinaryMS.Input κ K R) (A : Subgroup J)
    (hA : A ≤ Stellmacher.omegaOneCenterAmbient (pCore 2 J))
    (hm : ⁅A,K⁆ = A) (hc : 8 < Nat.card A) :
    IsMulCommutative (commutatorCore K) := by
  by_contra hn
  obtain ⟨s⟩ := exists_setup h hn
  obtain ⟨common⟩ := s.commonFacts hn
  let M := s.reduction.overgroup
  let A0 := A.subgroupOf M
  let K0 := K.subgroupOf M
  let f := embedM s.reduction.radical
  have hAK : A ≤ commutatorCore K := by
    rw [←hm]
    exact commutator_mono (fun a ha =>
      ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (hA ha)).1) le_rfl
  have hAM : A ≤ M := hAK.trans (h.commutatorCore_le.trans ((map_subtype_le _).trans le_sup_left))
  have hA0 : A0 ≤ omegaCenter (pCore 2 M) := by
    intro a ha
    obtain ⟨hac,hpow,hcomm⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (hA ha)
    apply mem_omegaCenter_iff.mpr
    refine ⟨?_,Subtype.ext hpow,?_⟩
    · rw [s.reduction.core_eq h]
      exact hac
    · intro y hy
      apply Subtype.ext
      apply hcomm
      rwa [s.reduction.core_eq h] at hy
  have hm0 : ⁅A0,K0⁆ = A0 := by
    apply map_injective M.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hAM,
      map_subgroupOf_eq_of_le (show K ≤ M from le_sup_left),hm]
  have hXZ : A0.map f ≤ Z s.reduction.radical (alpha s.reduction.radical) := by
    rw [←common.X_eq_Z _ rfl]
    change A0.map f ≤ omegaCenter (Q s.reduction.radical (alpha s.reduction.radical))
    rw [Q_alpha _ s.source.two_group s.source.core_le,omegaCenter_map _ f (embedM_injective _)]
    exact map_mono hA0
  have hU : A0.map f ≤ U s.reduction.radical (alpha s.reduction.radical) := by
    rw [←hm0,map_commutator]
    exact commutator_mono hXZ (by rw [s.Ltilde_embedded])
  have hcard : Nat.card (U s.reduction.radical (alpha s.reduction.radical)) = 8 := by
    rw [Nat.card_congr common.natural.equiv.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp
  let : Finite (U s.reduction.radical (alpha s.reduction.radical)) :=
    Finite.of_equiv (Multiplicative (Fin 3 → ZMod 2)) common.natural.equiv.toEquiv.symm
  have hb := card_le_of_le hU
  rw [card_map_of_injective (embedM_injective _),hcard,
    Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv] at hb
  omega


/-- A moving central omega subgroup of order 64 forces the whole
commutator core to be exactly that subgroup, with two natural copies. -/
theorem doubled_core_of_moving_omega
    (h : ChapterC.BinaryMS.Input κ K R) (A : Subgroup J)
    (hA : A ≤ Stellmacher.omegaOneCenterAmbient (pCore 2 J))
    (hm : ⁅A,K⁆ = A) (hc : Nat.card A = 64) :
    A = commutatorCore K ∧
    ∃ (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (f : commutatorCore K ≃* Multiplicative (Fin 2 → Fin 3 → ZMod 2)),
      ∀ k x i, (f (h.coreConjugate k x)).toAdd i =
        Representation.specialLinearNatural 3 (e (QuotientGroup.mk' (pCore 2 K) k))
          ((f x).toAdd i) := by
  have hab := abelian_of_large_moving_omega h A hA hm (by omega)
  have hAK : A ≤ commutatorCore K := by
    rw [←hm]
    exact commutator_mono (fun a ha =>
      ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (hA ha)).1) le_rfl
  have hb := card_le_of_le hAK
  rw [hc] at hb
  obtain ⟨m,hmul,⟨q⟩⟩ := AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient
    (h := h) hab
  have hk := h.abelianCore_fixedKernel_bounds hab hmul q
  have hs := q.card
  rcases hmul with rfl | rfl
  · norm_num only [Nat.mul_one, Nat.reducePow] at hs
    omega
  · have hd : Nat.card (commutatorCore K) = 64 := by
      rw [hk.2 rfl] at hs
      norm_num at hs
      exact hs
    have hi : Function.Injective q.projection := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [q.kernel]
      exact Subgroup.card_eq_one.mp (hk.2 rfl)
    exact ⟨eq_of_le_of_card_ge hAK (by omega),q.quotientEquiv,
      MulEquiv.ofBijective q.projection ⟨hi,q.surjective⟩,q.equivariant⟩

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {H C Q M : Subgroup G}

/-- All genuine binary MS hypotheses on the literal component-radical join.
The odd-index witness is the original local base. -/
def binaryMSInput (h : Input κ H Q M C)
    (hr : ChapterC.MSOddIndexRadical (Q.subgroupOf H))
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ChapterC.BinaryMS.Input κ (C.subgroupOf (C ⊔ Q)) (Q.subgroupOf (C ⊔ Q)) := by
  let J := C ⊔ Q
  let K := C.subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer h.normalizes)
  let eK : K ≃* C := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  refine {
    sqtk := (source_join_input h).setup.sqtk
    fitting := source_join_fitting h
    product := ?_
    component := (source_join_input h).component.2
    radical := msOddIndexRadical_join_from_source h hr
    characteristic := join_msCharacteristic_from_source h
    quotientEquiv := (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans e }
  intro j
  have hg : K ⊔ Q.subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  exact mem_sup_of_normal_left.mp (hg.ge (mem_top j))

open Representation Representation.BinaryOffender ChapterB.QuasisimpleSource

omit [Finite G] in
/-- The original B.5 two-copy moved section has order 64 before quotienting.
This is the subgroup on which MS characteristic replacement is applied. -/
theorem star_moved_card
    {A : Subgroup (StarQuotient C Q)} (hCA : starImage C Q C ≤ A)
    (s : MovedSection ((starRepresentation C Q).comp A.subtype)
      ((starImage C Q C).subgroupOf A))
    (F : BinaryField) (hF : F.degree = 1)
    (hm : IsRepeatedLinearNatural (s.space.toRepresentation.comp
      ((starImage C Q C).subgroupOf A).subtype) F 3 2) :
    Nat.card (⁅starV C Q,C.subgroupOf (C ⊔ Q)⁆ : Subgroup (C ⊔ Q : Subgroup G)) = 64 := by
  let U := starV C Q
  let K := C.subgroupOf (C ⊔ Q)
  let B := ⁅U,K⁆
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective
    (inclusion (commutator_le_left U K)) (inclusion_injective _)
  let q := QuotientGroup.mk' (starKernel C Q)
  have hs : s.space.toSubmodule = subspaceCommutator (starRepresentation C Q) ⊤ (K.map q) := by
    rw [s.space_eq]
    change subspaceCommutator ((starRepresentation C Q).comp A.subtype) ⊤
      ((starImage C Q C).subgroupOf A) = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCA]
    rfl
  let d := (NormalElementaryQuotient.movedEquiv U q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) K).trans (LinearEquiv.ofEq _ _ hs.symm)
  obtain ⟨a⟩ := hm
  change Nat.card (Additive B) = _
  rw [Nat.card_congr (d.trans a.linearEquiv).toEquiv]
  rw [Nat.card_fun,Nat.card_fun,Nat.card_fin,Nat.card_fin,F.card_eq,hF]
  norm_num

/-- Whole commutator-core recognition from the actual star moved section.
Every MS premise is supplied by the original source input and local base. -/
theorem whole_core_from_source
    (h : Input κ H Q M C)
    (hr : ChapterC.MSOddIndexRadical (Q.subgroupOf H))
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    {A : Subgroup (StarQuotient C Q)} (hCA : starImage C Q C ≤ A)
    (s : MovedSection ((starRepresentation C Q).comp A.subtype)
      ((starImage C Q C).subgroupOf A))
    (F : BinaryField) (hF : F.degree = 1)
    (hm : IsRepeatedLinearNatural (s.space.toRepresentation.comp
      ((starImage C Q C).subgroupOf A).subtype) F 3 2) :
    let b := binaryMSInput h hr e
    ⁅starV C Q,C.subgroupOf (C ⊔ Q)⁆ = commutatorCore (C.subgroupOf (C ⊔ Q)) ∧
    ∃ (e' : ((C.subgroupOf (C ⊔ Q)) ⧸ pCore 2 (C.subgroupOf (C ⊔ Q))) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (f : commutatorCore (C.subgroupOf (C ⊔ Q)) ≃* Multiplicative (Fin 2 → Fin 3 → ZMod 2)),
      ∀ k x i, (f (b.coreConjugate k x)).toAdd i =
        specialLinearNatural 3 (e' (QuotientGroup.mk' _ k)) ((f x).toAdd i) := by
  let b := binaryMSInput h hr e
  let U := starV C Q
  let K := C.subgroupOf (C ⊔ Q)
  have hp : IsPPerfect 2 K := by
    change IsPPerfect 2 (C.subgroupOf (C ⊔ Q))
    rw [←b.residual_eq]
    exact isPPerfect_pResidual 2
  have hid : ⁅⁅U,K⁆,K⁆ = ⁅U,K⁆ :=
    commutator_isPPerfect_idempotent K U hp (IsElementaryAbelian.isPGroup 2 U)
      le_normalizer_of_normal
  exact doubled_core_of_moving_omega b ⁅U,K⁆ (commutator_le_left U K) hid
    (star_moved_card hCA s F hF hm)


/-- Actual group coordinates on the full original commutator core, with
its literal component conjugation and its equality with the star moved group. -/
@[expose] def WholeCoreConclusion (κ : GroupClass) (C Q : Subgroup G) : Prop :=
  ∃ b : ChapterC.BinaryMS.Input κ (C.subgroupOf (C ⊔ Q)) (Q.subgroupOf (C ⊔ Q)),
    ⁅starV C Q,C.subgroupOf (C ⊔ Q)⁆ = commutatorCore (C.subgroupOf (C ⊔ Q)) ∧
    IsElementaryAbelian 2 (commutatorCore (C.subgroupOf (C ⊔ Q))) ∧
    Nat.card (commutatorCore (C.subgroupOf (C ⊔ Q))) = 64 ∧
    ∃ (e : ((C.subgroupOf (C ⊔ Q)) ⧸ pCore 2 (C.subgroupOf (C ⊔ Q))) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (f : commutatorCore (C.subgroupOf (C ⊔ Q)) ≃* Multiplicative (Fin 2 → Fin 3 → ZMod 2)),
      ∀ k x i, (f (b.coreConjugate k x)).toAdd i =
        specialLinearNatural 3 (e (QuotientGroup.mk' _ k)) ((f x).toAdd i)

/-- Package the genuine MS input and whole-core recognition for the
Chapter12 application on the same component, radical and moved section. -/
theorem whole_core_conclusion
    (h : Input κ H Q M C)
    (hr : ChapterC.MSOddIndexRadical (Q.subgroupOf H))
    (e : (C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    {A : Subgroup (StarQuotient C Q)} (hCA : starImage C Q C ≤ A)
    (s : MovedSection ((starRepresentation C Q).comp A.subtype)
      ((starImage C Q C).subgroupOf A))
    (F : BinaryField) (hF : F.degree = 1)
    (hm : IsRepeatedLinearNatural (s.space.toRepresentation.comp
      ((starImage C Q C).subgroupOf A).subtype) F 3 2) : WholeCoreConclusion κ C Q := by
  obtain ⟨he,e',f,hf⟩ := whole_core_from_source h hr e hCA s F hF hm
  refine ⟨binaryMSInput h hr e,he,?_,?_,e',f,hf⟩
  · rw [←he]
    exact IsElementaryAbelian.of_injective
      (inclusion (commutator_le_left (starV C Q) (C.subgroupOf (C ⊔ Q))))
      (inclusion_injective _)
  · rw [←he]
    exact star_moved_card hCA s F hF hm


/-- The recognized core has the same elementary structure and order after
its literal inclusion into the original ambient group. -/
theorem ambient_core_conclusion (h : WholeCoreConclusion κ C Q) :
    IsElementaryAbelian 2 (⁅(C ⊔ Q).pCoreIn 2,C⁆ : Subgroup G) ∧
    Nat.card (⁅(C ⊔ Q).pCoreIn 2,C⁆ : Subgroup G) = 64 := by
  obtain ⟨b,he,hel,hcard,e,f,hf⟩ := h
  let D := commutatorCore (C.subgroupOf (C ⊔ Q))
  have hmap : D.map (C ⊔ Q : Subgroup G).subtype =
      (⁅(C ⊔ Q).pCoreIn 2,C⁆ : Subgroup G) := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show C ≤ C ⊔ Q from le_sup_left)]
    rfl
  let := hel
  constructor
  · rw [←hmap]
    exact IsElementaryAbelian.map _
  · rw [←hmap,card_map_of_injective (C ⊔ Q : Subgroup G).subtype_injective]
    exact hcard

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeCore
