module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralCore
public import Theory.SpecificGroups.SL3.PerfectCentralCover
public import Theory.Representation.BinaryOffender.ConjugationGeneration

/-!
# Whole-core component descent outside field four

For an abelian Q=[O₂(KR),K], conjugation by O₂(KR) commutes with
conjugation by K. The actual component image therefore maps onto the
original full SL₃ quotient with central two-group kernel. The whole-core
centralizer bound proves that this projection is well defined. Away from
field four, the proved ordinary scalar-cover theorem supplies a surjection
in the reverse direction, so finiteness makes the original projection
injective. Hence Q centralizes the literal intrinsic O₂(K).

Transport gives a faithful binary SL₃ representation on the entire Q,
with the original quotient marking, literal conjugation and full commutator
generation. Both the original Chapter 4 nonblock configuration and the
Chapter 11 escaping point use this descent. The perfect central cover is
constructed also at field four; eliminating its exceptional kernel remains
open. No centrality in the larger O₂(KR), descended offender, whole-module
recognition, nonabelian sections or Sylow radical inequality is asserted.

Source: Aschbacher--Smith C.1.31--34, printed pp.135--137, I.1.3,
printed p.407, and original 4.3.8--10 and 11.1.5. The ordinary-cover theorem
uses the proved Steinberg presentation in PSL3.OrdinaryCenterRecognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ComponentDescent
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "Q" => (⁅pCore 2 (K ⊔ R : Subgroup G),K.subgroupOf (K ⊔ R)⁆ : Subgroup (K ⊔ R : Subgroup G))

omit [CharP F 2] in
/-- The actual component action on the whole commutator core. -/
def componentAction : L →* MulAut Q := by
  let := component_normal h hn
  exact (MulAut.conjNormal : J →* MulAut Q).comp (L).subtype

omit [CharP F 2] in
theorem componentAction_apply (k : L) (x : Q) :
    ((componentAction h hn k x : Q) : J) = k * (x : J) * (k : J)⁻¹ := by
  unfold componentAction
  rfl

include h hn
private theorem action_kernel_le : (componentAction h hn).ker ≤ pCore 2 L := by
  rw [pCore_subnormal_eq_comap 2 h.component.2.subnormal]
  intro k hk
  apply wholeCore_join_centralizer_le h hn
  intro x hx
  have he := congrArg (fun a : MulAut Q => (a ⟨x,hx⟩ : J)) hk
  change (k : J) * x * (k : J)⁻¹ = x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The whole-core component image projects onto the original full SL₃ quotient. -/
def componentProjection (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    (componentAction h hn).range →* SL(3,F) :=
  (componentAction h hn).rangeRestrict.liftOfSurjective
    (componentAction h hn).rangeRestrict_surjective
    ⟨(joinQuotientEquiv (R := R) e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)), by
      intro k hk
      have hk' : k ∈ (componentAction h hn).ker := by
        simpa only [MonoidHom.ker_rangeRestrict] using hk
      change joinQuotientEquiv e (QuotientGroup.mk' (pCore 2 L) k) = 1
      rw [MulEquiv.map_eq_one_iff]
      exact (QuotientGroup.eq_one_iff k).mpr (action_kernel_le h hn hk')⟩

theorem componentProjection_apply (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (k : L) :
    componentProjection h hn e ((componentAction h hn).rangeRestrict k) =
      e (QuotientGroup.mk' (pCore 2 K) ⟨k,k.property⟩) := by
  simp only [componentProjection,MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
  rfl

theorem componentProjection_surjective (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    Function.Surjective (componentProjection h hn e) := by
  intro g
  obtain ⟨k,hk⟩ := (joinQuotientEquiv (R := R) e).surjective.comp
    (QuotientGroup.mk'_surjective (pCore 2 L)) g
  exact ⟨(componentAction h hn).rangeRestrict k,(componentProjection_apply h hn e k).trans hk⟩

theorem componentProjection_kernel (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    (componentProjection h hn e).ker = (pCore 2 L).map (componentAction h hn).rangeRestrict := by
  ext a
  obtain ⟨k,rfl⟩ := (componentAction h hn).rangeRestrict_surjective a
  have hk : componentProjection h hn e ((componentAction h hn).rangeRestrict k) =
      joinQuotientEquiv e (QuotientGroup.mk' (pCore 2 L) k) := componentProjection_apply h hn e k
  constructor
  · intro he
    apply mem_map_of_mem
    change componentProjection h hn e ((componentAction h hn).rangeRestrict k) = 1 at he
    rw [hk,MulEquiv.map_eq_one_iff] at he
    exact (QuotientGroup.eq_one_iff k).mp he
  · rintro ⟨l,hl,he⟩
    change componentProjection h hn e ((componentAction h hn).rangeRestrict k) = 1
    rw [←he,componentProjection_apply]
    change joinQuotientEquiv e (QuotientGroup.mk' (pCore 2 L) l) = 1
    rw [MulEquiv.map_eq_one_iff]
    exact (QuotientGroup.eq_one_iff l).mpr hl

omit h hn [Finite G] [Field F] [Finite F] [CharP F 2] in
private theorem joinCore_abelian (hc : IsMulCommutative (msQ K R)) : IsMulCommutative Q := by
  let := hc
  let a := ((Q).equivMapOfInjective (J).subtype (J).subtype_injective).trans
    (MulEquiv.subgroupCongr commutator_map_eq_msQ)
  exact IsMulCommutative.of_comm (fun x y => a.injective (by rw [map_mul,map_mul,mul_comm]))

/-- Abelianity makes the entire remaining component kernel central. The
possible scalar center of SL₃ is retained. -/
theorem componentProjection_kernel_central (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hc : IsMulCommutative (msQ K R)) :
    (componentProjection h hn e).ker ≤ center (componentAction h hn).range := by
  let := component_normal h hn
  let a : J →* MulAut Q := MulAut.conjNormal
  have hz : ⁅(pCore 2 J).map a,(L).map a⁆ = ⊥ := by
    rw [←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro q hq
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change q * (x : J) * q⁻¹ = x
    rw [← (le_centralizer_iff_isMulCommutative.mpr (joinCore_abelian hc)) hq x x.property,
      mul_inv_cancel_right]
  rw [componentProjection_kernel]
  rintro b ⟨k,hk,rfl⟩
  rw [mem_center_iff]
  intro c
  obtain ⟨l,rfl⟩ := (componentAction h hn).rangeRestrict_surjective c
  apply Subtype.ext
  have hkN : (k : J) ∈ pCore 2 J := by
    have := (pCore_subnormal_eq_comap 2 h.component.2.subnormal).le hk
    exact this
  exact (commutator_eq_bot_iff_le_centralizer.mp hz)
    (mem_map_of_mem a hkN) (a l) (mem_map_of_mem a l.property)

/-- The exact projection kernel remains a two-group, also at field four. -/
theorem componentProjection_kernel_isPGroup (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    IsPGroup 2 (componentProjection h hn e).ker := by
  rw [componentProjection_kernel]
  exact pCore_isPGroup.map _

/-- For an abelian whole core, the actual action image is a perfect central
cover of the full marked SL₃, including at field four. -/
def componentCover (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hc : IsMulCommutative (msQ K R)) :
    PerfectCentralCovering.Cover (componentAction h hn).range SL(3,F) where
  toMonoidHom := componentProjection h hn e
  surjective := componentProjection_surjective h hn e
  isPerfect := by
    let := h.component.2.perfect
    exact Group.IsPerfect.range _
  ker_le_center := componentProjection_kernel_central h hn e hc

/-- Outside the exceptional field four, no kernel remains in the component
projection. The assertion is about the original map, not an unmarked isomorphism. -/
theorem componentProjection_injective (h4 : n ≠ 2)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (hc : IsMulCommutative (msQ K R)) :
    Function.Injective (componentProjection h hn e) := by
  let f := componentCover h hn e hc
  let := f.isPerfect
  have hq2 : Nat.card F ≠ 2 := by
    rw [h.field_card]
    have hh : 2^1 < 2^n := Nat.pow_lt_pow_right (by decide) hn
    omega
  have hq4 : Nat.card F ≠ 4 := by
    rw [h.field_card]
    have hh : 2^2 < 2^n := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  obtain ⟨k,hk,_⟩ := Matrix.PSL3.OrdinaryCenterRecognition.exists_scalar_lift hq2 hq4
    f.quotientCenterEquiv
  exact (f.surjective.bijective_of_nat_card_le (Nat.card_le_card_of_surjective k hk)).1

/-- The whole core centralizes the actual intrinsic O₂(K), without an extra
centrality premise, away from the exceptional field four. -/
theorem abelian_msQ_centralizes_componentCore (h4 : n ≠ 2)
    (hc : IsMulCommutative (msQ K R)) :
    msQ K R ≤ centralizer (K.pCoreIn 2 : Set G) := by
  let e := Classical.choice h.model
  have hinj := componentProjection_injective h hn h4 e hc
  intro x hx k hk
  obtain ⟨l,hl,rfl⟩ := hk
  let ll : L := ⟨⟨l,mem_sup_left l.property⟩,l.property⟩
  have hl' : ll ∈ pCore 2 L := by
    let b : L ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
    have he := pCore_map_iso 2 b
    have hh : l ∈ (pCore 2 L).map b.toMonoidHom := he.symm ▸ hl
    obtain ⟨y,hy,he⟩ := hh
    have hey : y = ll := b.injective he
    exact hey ▸ hy
  have ha : (componentAction h hn).rangeRestrict ll = 1 := by
    apply hinj
    rw [map_one]
    exact (componentProjection_kernel h hn e).ge (mem_map_of_mem _ hl')
  have hx' : x ∈ (Q).map (J).subtype := (commutator_map_eq_msQ (K := K) (R := R)).symm ▸ hx
  obtain ⟨q,hq,rfl⟩ := hx'
  have he := congrArg (fun a : (componentAction h hn).range =>
    (((a : MulAut Q) ⟨q,hq⟩ : Q) : J)) ha
  change (ll : J) * q * (ll : J)⁻¹ = q at he
  exact congrArg (J).subtype (mul_inv_eq_iff_eq_mul.mp he)


/-- The component action image is identified by its original quotient map. -/
def componentEquiv (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hc : IsMulCommutative (msQ K R)) : (componentAction h hn).range ≃* SL(3,F) :=
  MulEquiv.ofBijective (componentProjection h hn e)
    ⟨componentProjection_injective h hn h4 e hc,componentProjection_surjective h hn e⟩

theorem componentEquiv_apply (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hc : IsMulCommutative (msQ K R)) (k : L) :
    componentEquiv h hn h4 e hc ((componentAction h hn).rangeRestrict k) =
      e (QuotientGroup.mk' (pCore 2 K) ⟨k,k.property⟩) := by
  unfold componentEquiv
  exact componentProjection_apply h hn e k

omit h hn [Finite G] [Field F] [Finite F] [CharP F 2] in
private def originalCoreEquiv : Q ≃* msQ K R :=
  ((Q).equivMapOfInjective (J).subtype (J).subtype_injective).trans
    (MulEquiv.subgroupCongr commutator_map_eq_msQ)

/-- The full marked SL₃ acts on the original whole core. -/
def descendedAction (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hc : IsMulCommutative (msQ K R)) : SL(3,F) →* MulAut (msQ K R) :=
  (MulAut.congr originalCoreEquiv).toMonoidHom.comp
    ((componentAction h hn).range.subtype.comp (componentEquiv h hn h4 e hc).symm.toMonoidHom)

/-- Descent retains literal conjugation by every original component element. -/
theorem descendedAction_apply (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hc : IsMulCommutative (msQ K R)) (k : K) (x : msQ K R) :
    (descendedAction h hn h4 e hc (linearThreeActor e k) x : G) =
      k * (x : G) * (k : G)⁻¹ := by
  let ll : L := ⟨⟨k,mem_sup_left k.property⟩,k.property⟩
  have he : (componentEquiv h hn h4 e hc).symm (linearThreeActor e k) =
      (componentAction h hn).rangeRestrict ll := by
    apply (componentEquiv h hn h4 e hc).injective
    rw [MulEquiv.apply_symm_apply,componentEquiv_apply]
    rfl
  unfold descendedAction
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,he,MulAut.congr_apply]
  have hx : (((originalCoreEquiv.symm x : Q) : J) : G) = x :=
    congrArg (fun y : msQ K R => (y : G)) (originalCoreEquiv.apply_symm_apply x)
  change (((componentAction h hn ll (originalCoreEquiv.symm x) : Q) : J) : G) = _
  rw [componentAction_apply]
  change (k : G) * (((originalCoreEquiv.symm x : Q) : J) : G) * (k : G)⁻¹ = _
  rw [hx]

/-- No scalar or two-core kernel is lost by the full marked whole-core action. -/
theorem descendedAction_injective (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hc : IsMulCommutative (msQ K R)) :
    Function.Injective (descendedAction h hn h4 e hc) :=
  (MulAut.congr originalCoreEquiv).injective.comp
    ((componentAction h hn).range.subtype_injective.comp (componentEquiv h hn h4 e hc).symm.injective)

/-- The original abelian whole core carries a faithful binary representation
of the specified full SL₃; offender descent is a separate obligation. -/
def descendedRepresentation (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hc : IsMulCommutative (msQ K R)) :
    letI := abelian_msQ_elementary h hn hc
    Representation (ZMod 2) SL(3,F) (Additive (msQ K R)) := by
  let := abelian_msQ_elementary h hn hc
  exact {
    toFun := fun g => (descendedAction h hn h4 e hc g).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by
      apply LinearMap.ext
      intro v
      change Additive.ofMul (descendedAction h hn h4 e hc 1 v.toMul) = v
      rw [map_one]
      rfl
    map_mul' := by
      intro a b
      apply LinearMap.ext
      intro v
      change Additive.ofMul (descendedAction h hn h4 e hc (a*b) v.toMul) = _
      rw [map_mul]
      rfl }

theorem descendedRepresentation_apply (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hc : IsMulCommutative (msQ K R)) (k : K) (v : Additive (msQ K R)) :
    letI := abelian_msQ_elementary h hn hc
    ((descendedRepresentation h hn h4 e hc (linearThreeActor e k) v).toMul : G) =
      k * (v.toMul : G) * (k : G)⁻¹ := by
  let := abelian_msQ_elementary h hn hc
  exact descendedAction_apply h hn h4 e hc k v.toMul

theorem descendedRepresentation_injective (h4 : n ≠ 2)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (hc : IsMulCommutative (msQ K R)) :
    letI := abelian_msQ_elementary h hn hc
    Function.Injective (descendedRepresentation h hn h4 e hc) := by
  let := abelian_msQ_elementary h hn hc
  intro a b hab
  apply descendedAction_injective h hn h4 e hc
  apply MulEquiv.ext
  intro x
  exact congrArg (fun f : Module.End (ZMod 2) (Additive (msQ K R)) =>
    (f (Additive.ofMul x)).toMul) hab


/-- The descended representation is generated by its actual component
commutators; its core has not been replaced by an initial section. -/
theorem descendedRepresentation_full_commutator (h4 : n ≠ 2)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) (hc : IsMulCommutative (msQ K R)) :
    letI := abelian_msQ_elementary h hn hc
    Representation.BinaryOffender.subspaceCommutator
      (descendedRepresentation h hn h4 e hc) ⊤ ⊤ = ⊤ := by
  let := abelian_msQ_elementary h hn hc
  have hnQ : K ≤ normalizer (msQ K R : Set G) := by
    rw [←msQ_idempotent h hn]
    exact normalizer_commutator_ge_right _ _
  have hh := Representation.BinaryOffender.commutator_eq_top_of_conjugation
    (descendedRepresentation h hn h4 e hc) (msQ K R) K hnQ
    (linearThreeActor e) (MonoidHom.id _) Function.surjective_id
    (fun k x => Additive.toMul.injective (Subtype.ext
      (descendedRepresentation_apply h hn h4 e hc k (Additive.ofMul x))))
    (by rw [commutator_comm]; exact msQ_idempotent h hn)
  have he : (linearThreeActor e).range = ⊤ := MonoidHom.range_eq_top.mpr
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  rwa [he] at hh

/-- An application interface on the literal whole core and original marking. -/
theorem exists_descendedAction (h4 : n ≠ 2) (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hc : IsMulCommutative (msQ K R)) :
    ∃ a : SL(3,F) →* MulAut (msQ K R), Function.Injective a ∧
      ∀ (k : K) (x : msQ K R), (a (linearThreeActor e k) x : G) =
        k * (x : G) * (k : G)⁻¹ :=
  ⟨descendedAction h hn h4 e hc,descendedAction_injective h hn h4 e hc,
    descendedAction_apply h hn h4 e hc⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ComponentDescent
