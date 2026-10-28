module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Coordinates for the intrinsic block moving section

An equality between the embedded intrinsic commutator core and an ambient
moved subgroup identifies the actual block quotient with its canonical
moved/fixed section. The maps retain conjugation and its full fixed central
attachment. Irr-plus and a natural action identification then give the exact
irreducibility interval and block model, without splitting the central layer.

Source: Aschbacher--Smith C.1.7 and MS93 (3.2), (3.6).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BlockMovingSection
open ChapterB.QuasisimpleSource
variable {H J : Type*} [Group H] [Group J]
  (X K : Subgroup H) [X.Normal] [IsElementaryAbelian 2 X]
  (q : H →* J) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (X : Set H))
  (he : (blockU K).map K.subtype = ⁅X,K⁆)

local notation "ρ" => NormalElementaryQuotient.representation X q hq hker
local notation "C" => K.map q
local notation "s" => MovedSection.ofNormal ρ C

variable [(K.map q).Normal]

theorem mem_space (v : Additive X) :
    v ∈ (s).space.toSubmodule ↔ (v.toMul : H) ∈ ⁅X,K⁆ := by
  change v ∈ subspaceCommutator ρ ⊤ C ↔ _
  rw [← NormalElementaryQuotient.commutatorSpace_eq X q hq hker K]
  rfl

include he in
omit [X.Normal] [IsElementaryAbelian 2 X] in
theorem intrinsic_mem_commutator (v : blockU K) : (v.val.val : H) ∈ ⁅X,K⁆ := by
  rw [← he]
  exact mem_map_of_mem K.subtype v.property

include he in
/-- Literal coordinates from the intrinsic commutator core to the ambient moved space. -/
@[expose] noncomputable def coreEquiv : blockU K ≃* Multiplicative (s).space.toSubmodule := by
  let f : blockU K →* Multiplicative (s).space.toSubmodule := {
    toFun := fun v => Multiplicative.ofAdd ⟨Additive.ofMul
      ⟨v.val.val,(commutator_le_left X K) (intrinsic_mem_commutator X K he v)⟩,
      (mem_space X K q hq hker _).mpr (intrinsic_mem_commutator X K he v)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  apply MulEquiv.ofBijective f
  constructor
  · intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : Multiplicative (s).space.toSubmodule =>
      (x.toAdd.val.toMul : H)) h
  · intro v
    have hv := (mem_space X K q hq hker v.toAdd.val).mp v.toAdd.property
    rw [← he] at hv
    obtain ⟨x,hx,hxv⟩ := hv
    refine ⟨⟨x,hx⟩,?_⟩
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Additive.toMul.injective
    exact Subtype.ext hxv

@[simp] theorem coreEquiv_val (v : blockU K) :
    (((coreEquiv X K q hq hker he v).toAdd.val).toMul : H) = v.val.val := rfl

/-- The coordinate map retains the original conjugation. -/
theorem coreEquiv_conjugate (k : K) (v : blockU K) :
    (coreEquiv X K q hq hker he (blockConjugate K k v)).toAdd =
      (s).space.toRepresentation (q k) (coreEquiv X K q hq hker he v).toAdd := by
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coreEquiv_val]
  change (k : H) * v.val.val * (k : H)⁻¹ =
    ((ρ (q k) (coreEquiv X K q hq hker he v).toAdd.val).toMul : H)
  rw [NormalElementaryQuotient.representation_apply,coreEquiv_val]


/-- Fixed coordinates are exactly the intrinsic central subgroup. -/
theorem coreEquiv_fixed_iff (v : blockU K) :
    (coreEquiv X K q hq hker he v).toAdd ∈ (s).central.toSubmodule ↔
      v ∈ blockFixed K := by
  change (∀ c : C, (s).space.toRepresentation c
    (coreEquiv X K q hq hker he v).toAdd =
      (coreEquiv X K q hq hker he v).toAdd) ↔ (v : K) ∈ center K
  constructor
  · intro hv
    rw [mem_center_iff]
    intro k
    have hh := (coreEquiv_conjugate X K q hq hker he k v).trans
      (hv (q.subgroupMap K k))
    have hh' : blockConjugate K k v = v :=
      (coreEquiv X K q hq hker he).injective
        (Multiplicative.toAdd.injective hh)
    have hk := congrArg (fun z : blockU K => (z : K)) hh'
    exact mul_inv_eq_iff_eq_mul.mp hk
  · intro hv c
    obtain ⟨k,rfl⟩ := q.subgroupMap_surjective K c
    change (s).space.toRepresentation (q k)
      (coreEquiv X K q hq hker he v).toAdd = _
    rw [← coreEquiv_conjugate X K q hq hker he k v]
    congr 2
    apply Subtype.ext
    change k * (v : K) * k⁻¹ = (v : K)
    rw [mem_center_iff.mp hv k,mul_inv_cancel_right]

/-- Projection onto the actual moved/fixed quotient, from the intrinsic core. -/
@[expose] noncomputable def centralProjection :
    blockU K →* Multiplicative ((s).space.toSubmodule ⧸ (s).central.toSubmodule) :=
  ((s).central.toSubmodule.mkQ.toAddMonoidHom.toMultiplicative).comp
    (coreEquiv X K q hq hker he).toMonoidHom

theorem centralProjection_surjective :
    Function.Surjective (centralProjection X K q hq hker he) := by
  intro w
  obtain ⟨v,hv⟩ := (s).central.toSubmodule.mkQ_surjective w.toAdd
  obtain ⟨u,hu⟩ := (coreEquiv X K q hq hker he).surjective (Multiplicative.ofAdd v)
  refine ⟨u,?_⟩
  change Multiplicative.ofAdd ((s).central.toSubmodule.mkQ
    (coreEquiv X K q hq hker he u).toAdd) = w
  rw [hu]
  exact congrArg Multiplicative.ofAdd hv

theorem centralProjection_kernel :
    (centralProjection X K q hq hker he).ker = blockFixed K := by
  ext v
  change (s).central.toSubmodule.mkQ (coreEquiv X K q hq hker he v).toAdd = 0 ↔ _
  change Submodule.Quotient.mk (coreEquiv X K q hq hker he v).toAdd = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact coreEquiv_fixed_iff X K q hq hker he v

theorem centralProjection_conjugate (k : K) (v : blockU K) :
    (centralProjection X K q hq hker he (blockConjugate K k v)).toAdd =
      (s).central.quotientRepresentation (q k) (centralProjection X K q hq hker he v).toAdd := by
  change (s).central.toSubmodule.mkQ
    (coreEquiv X K q hq hker he (blockConjugate K k v)).toAdd = _
  rw [coreEquiv_conjugate]
  rfl

/-- The actual intrinsic block module is the canonical moved/fixed section. -/
@[expose] noncomputable def moduleEquiv :
    BlockModule K ≃* Multiplicative ((s).space.toSubmodule ⧸ (s).central.toSubmodule) :=
  (QuotientGroup.quotientMulEquivOfEq
    (centralProjection_kernel X K q hq hker he).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (centralProjection X K q hq hker he)
        (centralProjection_surjective X K q hq hker he))

@[simp] theorem moduleEquiv_mk (v : blockU K) :
    moduleEquiv X K q hq hker he (QuotientGroup.mk' (blockFixed K) v) =
      centralProjection X K q hq hker he v := rfl


include he in
/-- Irr-plus on the containing module gives the exact intrinsic normal interval. -/
theorem irreducible_of_moving
    (hi : IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C)) : BlockModuleIrreducible K := by
  let τ := (s).space.toRepresentation.comp (C).subtype
  let f := q.subgroupMap K
  let e := coreEquiv X K q hq hker he
  let j : Multiplicative (s).space.toSubmodule →* K :=
    (blockU K).subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := (blockU K).subtype_injective.comp e.symm.injective
  have hr : j.range = blockU K := by
    apply le_antisymm
    · rintro _ ⟨v,rfl⟩
      exact (e.symm v).property
    · intro k hk
      exact ⟨e ⟨k,hk⟩,congrArg (blockU K).subtype (e.symm_apply_apply _)⟩
  have hi' : IsIrrPlus τ ⊤ ⊤ := by
    let et : C ≃* (⊤ : Subgroup C) := Subgroup.topEquiv.symm
    apply hi.of_intertwining ρ τ et.toMonoidHom et.surjective
      (s).space.toSubmodule.subtype (s).space.toSubmodule.subtype_injective
    · intro c v
      rfl
    · rw [Submodule.map_top,Submodule.range_subtype]
      rfl
  have haction : ∀ k w, j (Multiplicative.ofAdd (τ (f k) w)) =
      k * j (Multiplicative.ofAdd w) * k⁻¹ := by
    intro k w
    obtain ⟨v,hv⟩ := e.surjective (Multiplicative.ofAdd w)
    have hv' : (e v).toAdd = w := congrArg Multiplicative.toAdd hv
    rw [← hv']
    change j (Multiplicative.ofAdd ((s).space.toRepresentation (q k) (e v).toAdd)) = _
    dsimp only [e]
    rw [← coreEquiv_conjugate X K q hq hker he k v]
    change ((e.symm (e (blockConjugate K k v))) : K) =
      k * ((e.symm (e v)) : K) * k⁻¹
    rw [e.symm_apply_apply,e.symm_apply_apply]
    rfl
  have hfixed (w : (s).space.toSubmodule) : w ∈ fixedSpace τ ⊤ ↔
      j (Multiplicative.ofAdd w) ∈ center K := by
    constructor
    · intro hw
      rw [mem_center_iff]
      intro k
      have hh := congrArg (fun v => j (Multiplicative.ofAdd v)) (hw ⟨f k,mem_top _⟩)
      change j (Multiplicative.ofAdd (τ (f k) w)) = j (Multiplicative.ofAdd w) at hh
      rw [haction] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hw c
      obtain ⟨k,hk⟩ := q.subgroupMap_surjective K c.val
      apply Multiplicative.ofAdd.injective
      apply hj
      change j (Multiplicative.ofAdd (τ c.val w)) = j (Multiplicative.ofAdd w)
      rw [← hk,haction,mem_center_iff.mp hw k,mul_inv_cancel_right]
  refine ⟨lt_of_le_of_ne inf_le_left ?_,?_⟩
  · intro hh
    apply hi'.not_le_fixedSpace τ
    intro w _
    apply (hfixed w).mpr
    exact (hh.ge (hr ▸ show j (Multiplicative.ofAdd w) ∈ j.range from ⟨_,rfl⟩)).2
  · intro N hN hlo hhi
    let W : Submodule (ZMod 2) (s).space.toSubmodule :=
      AddSubgroup.toZModSubmodule 2 (N.comap j).toAddSubgroup'
    have hW : (⊤ : Subgroup C) ≤ subspaceStabilizer τ W := by
      apply le_subspaceStabilizer
      intro c _ w hw
      obtain ⟨k,rfl⟩ := q.subgroupMap_surjective K c
      change j (Multiplicative.ofAdd (τ (f k) w)) ∈ N
      rw [haction]
      exact hN.conj_mem _ hw k
    rcases hi'.eq_or_le_fixedSpace τ hW le_top with htop | hfix
    · right
      apply le_antisymm hhi
      intro u hu
      obtain ⟨w,rfl⟩ := (show u ∈ j.range from hr.symm ▸ hu)
      exact (show w.toAdd ∈ W from htop ▸ Submodule.mem_top)
    · left
      apply le_antisymm _ hlo
      intro u hu
      refine ⟨hhi hu,?_⟩
      obtain ⟨w,rfl⟩ := (show u ∈ j.range from hr.symm ▸ hhi hu)
      exact (hfixed w.toAdd).mp (hfix hu)

variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]

include he in
/-- An action identification of the canonical moving section gives a literal
block model, preserving the specified quotient map and conjugation. -/
theorem model_of_moving
    (eK : (K ⧸ pCore 2 K) ≃* C)
    (hcompat : ∀ k : K, eK (QuotientGroup.mk' (pCore 2 K) k) = q.subgroupMap K k)
    (σ : Representation (ZMod 2) A V)
    (E : ActionEquiv ((s).central.quotientRepresentation.comp (C).subtype) σ) :
    IsLinearBlockModel K σ := by
  let r : A →* MulAut (Multiplicative V) := {
    toFun := fun a => (LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom a)).toAddEquiv.toMultiplicative
    map_one' := by ext v; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun σ.map_one v.toAdd)
    map_mul' := fun a b => by ext v; exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun (σ.map_mul a b) v.toAdd) }
  refine ⟨r,⟨{
    quotientIso := eK.trans E.groupEquiv
    moduleIso := (moduleEquiv X K q hq hker he).trans E.linearEquiv.toAddEquiv.toMultiplicative
    intertwining := ?_ }⟩,fun _ _ => rfl⟩
  intro k v
  change Multiplicative.ofAdd (E.linearEquiv
    (moduleEquiv X K q hq hker he (QuotientGroup.mk' _ (blockConjugate K k v))).toAdd) = _
  rw [moduleEquiv_mk]
  apply Multiplicative.toAdd.injective
  change E.linearEquiv (centralProjection X K q hq hker he (blockConjugate K k v)).toAdd =
    σ (E.groupEquiv (eK (QuotientGroup.mk' (pCore 2 K) k)))
      (E.linearEquiv (moduleEquiv X K q hq hker he (QuotientGroup.mk' _ v)).toAdd)
  rw [moduleEquiv_mk,centralProjection_conjugate,hcompat]
  exact E.intertwines (q.subgroupMap K k) _

end CFSG.Quasithin.ChapterC.BlockMovingSection
