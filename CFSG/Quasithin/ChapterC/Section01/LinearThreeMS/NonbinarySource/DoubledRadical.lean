module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.RadicalInitial
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.SylowSections
public import Theory.Representation.SL3DoubledNaturalOffenders.Localization
public import Theory.Representation.SL3DoubledNaturalOffenders.AllFields

/-!
# The whole doubled-core radical inequality in every nonbinary degree

Let Q=[O₂(KR),K] carry an actual doubled-natural section model, with the
original full SL₃ quotient marking. The Sylow-omega splitting identifies
its centralizer in KR with the centralizer of C_Q(S). Consequently the
literal radical comparison passes to Q's faithful centralizer-quotient
action, even when its normal two-subgroup is nontrivial. This comparison
holds also at field four.

In every nonbinary field degree, the doubled-natural normalizer estimate places
every offender inside the actual component image. MS3 supplies such an
offender from the original R, and the common-axis versus point-radical
calculation proves R ≠ O₂(C_KR(Ω₁Z(S))). Thus the doubled row of C.1.34
requires no extra centrality premise once its whole-core model is known.
The original Chapter4 nonblock and Chapter11 point consumers apply this
result to their literal cores and Sylow subgroups.

The even-degree localization retains the full cubic center, including at
field four. This does not construct the whole-core model or settle the
nonabelian central/Frattini rows or field-four covering descent. Source: Aschbacher--Smith C.1.34(2), printed pp.136--137, and
B.5.9--10, printed pp.107--109.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.DoubledRadical
open Chapter1.RadicalExclusions.ModelReduction.FullSieve SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "T" => R.subgroupOf (K ⊔ R)
local notation "Q" => (⁅pCore 2 (K ⊔ R : Subgroup G),K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G))

omit [Finite G] [Finite F] [CharP F 2] in
private theorem core_commutative
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3))) :
    IsMulCommutative (msQ K R) := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,_,a,_⟩ := hm
  let b := QuotientGroup.quotientBot.symm.trans a
  exact IsMulCommutative.of_comm (fun x y => b.injective (by rw [map_mul,map_mul,mul_comm]))

private theorem whole_model
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hc : IsMulCommutative (msQ K R))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3))) :
    letI := component_normal h hn
    letI := abelian_joinCore_elementary h hn hc
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    let B := (L).map (QuotientGroup.mk' (centralizer (Q : Set J)))
    ∃ mark : B ≃* SL(3,F), ∃ E : Additive Q ≃ₗ[ZMod 2] (Fin 2 → Fin 3 → F),
      ∀ b : B, ∀ v, E (wholeCoreRepresentation h hn hc b v) =
        SL3DoubledNaturalOffenders.representation F (mark b) (E v) := by
  let := component_normal h hn
  let := abelian_joinCore_elementary h hn hc
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let q := QuotientGroup.mk' (centralizer (Q : Set J))
  let B := (L).map q
  let ρ := wholeCoreRepresentation h hn hc
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,_,_,_,a,ha⟩ := hm
  let a₀ : msQ K R ≃* Multiplicative ((Fin 3 → F) × (Fin 3 → F)) :=
    QuotientGroup.quotientBot.symm.trans a
  let c : Q ≃* msQ K R :=
    ((Q).equivMapOfInjective (J).subtype (J).subtype_injective).trans
      (MulEquiv.subgroupCongr commutator_map_eq_msQ)
  let E₀ : Additive Q ≃ₗ[ZMod 2] ((Fin 3 → F) × (Fin 3 → F)) :=
    { (c.trans a₀).toAdditiveLeft with map_smul' := ZMod.map_smul (c.trans a₀).toAdditiveLeft }
  let E := E₀.trans (LinearEquiv.finTwoArrow (ZMod 2) (Fin 3 → F)).symm
  have hE (k : L) (v : Additive Q) : E (ρ (q k) v) =
      SL3DoubledNaturalOffenders.representation F
        (linearThreeActor e ⟨k,k.property⟩) (E v) := by
    have hh := ha (⟨k,k.property⟩ : K) (c v.toMul) (c (ρ (q k) v).toMul)
      (congrArg (J).subtype (wholeCoreRepresentation_apply h hn hc k v))
    apply (LinearEquiv.finTwoArrow (ZMod 2) (Fin 3 → F)).injective
    change E₀ (ρ (q k) v) =
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3))
        (linearThreeActor e ⟨k,k.property⟩) (E₀ v)
    exact hh
  let τ : Representation (ZMod 2) (J ⧸ centralizer (Q : Set J)) (Fin 2 → Fin 3 → F) :=
    E.conjRingEquiv.toMonoidHom.comp ρ
  let f := τ.asGroupHom
  have hf : Function.Injective f := by
    intro x y he
    exact E.conjRingEquiv.injective.comp (wholeCoreRepresentation_injective h hn hc)
      (congrArg Units.val he)
  have hk (k : L) : f (q k) =
      (SL3DoubledNaturalOffenders.representation F).asGroupHom
        (linearThreeActor e ⟨k,k.property⟩) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change E (ρ (q k) (E.symm v)) = _
    rw [hE,E.apply_symm_apply]
    rfl
  have hB : B.map f = SL3DoubledNaturalOffenders.component F := by
    apply le_antisymm
    · rintro _ ⟨_,⟨k,hk',rfl⟩,rfl⟩
      exact ⟨linearThreeActor e ⟨k,hk'⟩,(hk ⟨k,hk'⟩).symm⟩
    · rintro _ ⟨g,rfl⟩
      obtain ⟨k,hkg⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
      let l : L := ⟨⟨k,mem_sup_left k.property⟩,k.property⟩
      refine ⟨q l,mem_map_of_mem q l.property,?_⟩
      exact (hk l).trans (congrArg (SL3DoubledNaturalOffenders.representation F).asGroupHom hkg)
  have hrep : Function.Injective (SL3DoubledNaturalOffenders.representation F).asGroupHom := by
    intro a b hab
    exact SL3DoubledNaturalOffenders.representation_injective F (congrArg Units.val hab)
  let t := MonoidHom.ofInjective hrep
  let mark : B ≃* SL(3,F) :=
    ((B.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hB)).trans t.symm
  refine ⟨mark,E,?_⟩
  intro b v
  have hb : (SL3DoubledNaturalOffenders.representation F).asGroupHom (mark b) = f b :=
    congrArg Subtype.val (t.apply_symm_apply ((MulEquiv.subgroupCongr hB) (B.equivMapOfInjective f hf b)))
  have he := LinearMap.congr_fun (congrArg Units.val hb) (E v)
  change _ = E (ρ b (E.symm (E v))) at he
  rw [E.symm_apply_apply] at he
  exact he.symm


include h hn

private theorem centralizer_subgroupOf
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)))
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    (J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G)).subgroupOf J =
      centralizer ((Q ⊓ centralizer (S.subgroupOf J : Set J) : Subgroup J) : Set J) := by
  have hSJ : S ≤ J := (Chapter1.isSylowIn_iff.mp hS).2.1
  let U := msQ K R ⊓ centralizer (S : Set G)
  have hR : R ≤ centralizer (U : Set G) := by
    intro r hr u hu
    exact (hu.2 r (hRS hr)).symm
  have hC : J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G) =
      J ⊓ centralizer (U : Set G) := by
    rw [doubled_sylow_centralizer h hn hS hRS e hm]
    apply le_antisymm
    · apply sup_le
      · intro x hx
        exact ⟨mem_sup_left hx.1,hx.2⟩
      · exact le_inf le_sup_right hR
    · rintro x ⟨hx,hxc⟩
      obtain ⟨k,hk,r,hr,rfl⟩ := product h hn x hx
      have hkc : k ∈ centralizer (U : Set G) := by
        have hh := (centralizer _).mul_mem hxc ((centralizer _).inv_mem (hR hr))
        simpa only [mul_inv_cancel_right] using hh
      exact mul_mem_sup ⟨hk,hkc⟩ hr
  have hQ (x : J) : (x : G) ∈ msQ K R ↔ x ∈ Q := by
    rw [←commutator_map_eq_msQ]
    exact mem_map_iff_mem (J).subtype_injective
  rw [hC]
  ext x
  constructor
  · rintro ⟨_,hc⟩ y ⟨hy,hyS⟩
    exact Subtype.ext (hc y ⟨(hQ y).mpr hy,
      fun s hs => congrArg (J).subtype (hyS ⟨s,hSJ hs⟩ hs)⟩)
  · intro hc
    refine ⟨x.property,?_⟩
    rintro y ⟨hy,hyS⟩
    have hyJ : y ∈ J := (msQ_le_joinCore.trans (pCoreIn_le 2 J)) hy
    exact congrArg (J).subtype (hc ⟨y,hyJ⟩ ⟨(hQ ⟨y,hyJ⟩).mp hy,
      fun s hs => Subtype.ext (hyS s hs)⟩)

/-- The radical comparison for an actual doubled whole core passes exactly
through its own centralizer quotient, including at field four. -/
theorem notCentralizerCore_iff_whole_action
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (hc : IsMulCommutative (msQ K R))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)))
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    letI := component_normal h hn
    letI := abelian_joinCore_elementary h hn hc
    let q := QuotientGroup.mk' (centralizer (Q : Set J))
    MSNotCentralizerCore K R S ↔
      (T).map q ≠ (NormalElementaryQuotient.fixedSpaceFixer (wholeCoreRepresentation h hn hc)
        ((S.subgroupOf J).map q)).pCoreIn 2 := by
  let := component_normal h hn
  let := abelian_joinCore_elementary h hn hc
  let q := QuotientGroup.mk' (centralizer (Q : Set J))
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.of_injective (inclusion (wholeCore_join_centralizer_le h hn))
      (inclusion_injective _)
  have hRT : q.ker ≤ T := by
    rw [QuotientGroup.ker_mk']
    exact (wholeCore_join_centralizer_le h hn).trans (join_oddIndex h hn).twoCore_le
  have ht := NormalElementaryQuotient.radical_eq_fixed_core_iff Q q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hk (S.subgroupOf J) T hRT
  rw [←centralizer_subgroupOf h hn e hm hS hRS] at ht
  have htransport : R = (J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G)).pCoreIn 2 ↔
      T = ((J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G)).subgroupOf J).pCoreIn 2 := by
    have hm : (((J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G)).subgroupOf J).pCoreIn 2).map (J).subtype =
        (J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G)).pCoreIn 2 := by
      rw [map_pCoreIn_of_injective 2 _ _ (J).subtype_injective,
        map_subgroupOf_eq_of_le inf_le_left]
    constructor
    · intro he
      apply map_injective (J).subtype_injective
      rw [map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right),hm]
      exact he
    · intro he
      have hh := congrArg (fun A : Subgroup J => A.map (J).subtype) he
      rwa [map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right),hm] at hh
  rw [wholeCoreRepresentation_eq]
  exact not_congr (htransport.trans ht)

/-- In odd field degree a doubled whole-core section supplies the actual
Sylow radical inequality, without assuming centrality in O₂(KR). -/
theorem notCentralizerCore_of_doubled (ho : Odd n)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)))
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    MSNotCentralizerCore K R S := by
  let hc := core_commutative e hm
  let := component_normal h hn
  let := abelian_joinCore_elementary h hn hc
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let q := QuotientGroup.mk' (centralizer (Q : Set J))
  let B := (L).map q
  let : B.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let ρ := wholeCoreRepresentation h hn hc
  obtain ⟨mark,E,hE⟩ := whole_model h hn e hc hm
  obtain ⟨A,hA,_,hbest,_,_⟩ := NoncoreOffenders.abelian_core_bestOffenders h hn hc T le_rfl
  have hAB : A.map q ≤ B := SL3DoubledNaturalOffenders.offender_le_normal_component
    ρ (wholeCoreRepresentation_injective h hn hc) B h.field_card (by omega) ho
    mark E hE (hbest.isOffender ρ)
  let D : BinaryField := { Carrier := F, degree := n, degree_pos := by omega, card_eq := h.field_card }
  let U : Subrepresentation (ρ.comp B.subtype) := ⊤
  let a : ActionEquiv U.toRepresentation (repeated (linearNatural D 3) 2) := {
    groupEquiv := mark
    linearEquiv := (LinearEquiv.ofTop U.toSubmodule rfl).trans E
    intertwines := fun b v => hE b v.val }
  obtain ⟨P,hP⟩ := hS
  have hPS : (P : Subgroup J) = S.subgroupOf J := by
    rw [←hP]
    exact (comap_map_eq_self_of_injective (J).subtype_injective _).symm
  let P' := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hP' : (P' : Subgroup (J ⧸ centralizer (Q : Set J))) = (S.subgroupOf J).map q := by
    change (P : Subgroup J).map q = _
    rw [hPS]
  have hRP : (T).map q ≤ P' := by
    rw [hP']
    exact map_mono (comap_mono hRS)
  have hi := RadicalGeometry.radical_ne_fixerCore_of_double D ρ B U a
    (by exact top_sup_eq _) P' ((T).map q) hRP hbest (map_mono hA.1) hAB
  rw [hP'] at hi
  exact (notCentralizerCore_iff_whole_action h hn e hc hm ⟨P,hP⟩ hRS).mpr hi

/-- The whole doubled row of C.1.34 is complete in odd field degree. -/
theorem moduleAlternatives_of_doubled (ho : Odd n)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)))
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    MSModuleAlternatives K R S n F e :=
  Or.inr (Or.inl ⟨hm,notCentralizerCore_of_doubled h hn ho e hm hS hRS⟩)

/-- In every nonbinary field degree a doubled whole-core section supplies the actual
Sylow radical inequality, without assuming centrality in O₂(KR). -/
theorem notCentralizerCore_of_doubled_all_degrees
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)))
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    MSNotCentralizerCore K R S := by
  let hc := core_commutative e hm
  let := component_normal h hn
  let := abelian_joinCore_elementary h hn hc
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let q := QuotientGroup.mk' (centralizer (Q : Set J))
  let B := (L).map q
  let : B.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let ρ := wholeCoreRepresentation h hn hc
  obtain ⟨mark,E,hE⟩ := whole_model h hn e hc hm
  obtain ⟨A,hA,_,hbest,_,_⟩ := NoncoreOffenders.abelian_core_bestOffenders h hn hc T le_rfl
  have hAB : A.map q ≤ B := SL3DoubledNaturalOffenders.AllFields.offender_le_normal_component
    ρ (wholeCoreRepresentation_injective h hn hc) B h.field_card hn
    mark E hE (hbest.isOffender ρ)
  let D : BinaryField := { Carrier := F, degree := n, degree_pos := by omega, card_eq := h.field_card }
  let U : Subrepresentation (ρ.comp B.subtype) := ⊤
  let a : ActionEquiv U.toRepresentation (repeated (linearNatural D 3) 2) := {
    groupEquiv := mark
    linearEquiv := (LinearEquiv.ofTop U.toSubmodule rfl).trans E
    intertwines := fun b v => hE b v.val }
  obtain ⟨P,hP⟩ := hS
  have hPS : (P : Subgroup J) = S.subgroupOf J := by
    rw [←hP]
    exact (comap_map_eq_self_of_injective (J).subtype_injective _).symm
  let P' := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hP' : (P' : Subgroup (J ⧸ centralizer (Q : Set J))) = (S.subgroupOf J).map q := by
    change (P : Subgroup J).map q = _
    rw [hPS]
  have hRP : (T).map q ≤ P' := by
    rw [hP']
    exact map_mono (comap_mono hRS)
  have hi := RadicalGeometry.radical_ne_fixerCore_of_double D ρ B U a
    (by exact top_sup_eq _) P' ((T).map q) hRP hbest (map_mono hA.1) hAB
  rw [hP'] at hi
  exact (notCentralizerCore_iff_whole_action h hn e hc hm ⟨P,hP⟩ hRS).mpr hi

/-- The whole doubled row of C.1.34 is complete at every nonbinary field, including field four. -/
theorem moduleAlternatives_of_doubled_all_degrees
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)))
    {S : Subgroup G} (hS : Chapter1.IsSylowIn 2 S J) (hRS : R ≤ S) :
    MSModuleAlternatives K R S n F e :=
  Or.inr (Or.inl ⟨hm,notCentralizerCore_of_doubled_all_degrees h hn e hm hS hRS⟩)

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.DoubledRadical
