module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# Original subgroup coordinates for a marked moved cover

The canonical moved space of a quotient conjugation action embeds in the
original group with image exactly its subgroup commutator. This embedding
retains actual conjugation. The fixed kernel of its marked cover maps to
the intersection of that commutator with the component centralizer.
No intrinsic-core equality or splitting of the central attachment is used.

Source: MS93 (3.2)(vi), (1.5)(ii).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ElementaryMovedCover
variable {H J : Type*} [Group H] [Group J]
  (X K : Subgroup H) [X.Normal] [IsElementaryAbelian 2 X]
  (q : H →* J) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (X : Set H)) [(K.map q).Normal]
local notation "ρ" => NormalElementaryQuotient.representation X q hq hker
local notation "s" => MovedSection.ofNormal ρ (K.map q)

noncomputable def embedding : Multiplicative (s).space.toSubmodule →* H where
  toFun v := v.toAdd.val.toMul.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem embedding_injective : Function.Injective (embedding X K q hq hker) := by
  intro v w h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  apply Additive.toMul.injective
  exact Subtype.ext h

theorem embedding_range : (embedding X K q hq hker).range = ⁅X,K⁆ := by
  ext x
  constructor
  · rintro ⟨v,rfl⟩
    have hv := v.toAdd.property
    change v.toAdd.val ∈ subspaceCommutator ρ ⊤ (K.map q) at hv
    rw [←NormalElementaryQuotient.commutatorSpace_eq X q hq hker K] at hv
    exact hv
  · intro hx
    let v : (s).space.toSubmodule := ⟨Additive.ofMul
      ⟨x,(commutator_le_left X K) hx⟩,by
        change _ ∈ subspaceCommutator ρ ⊤ (K.map q)
        rw [←NormalElementaryQuotient.commutatorSpace_eq X q hq hker K]
        exact hx⟩
    exact ⟨Multiplicative.ofAdd v,rfl⟩

theorem embedding_conjugate (g : H) (v : (s).space.toSubmodule) :
    embedding X K q hq hker (Multiplicative.ofAdd
      ((s).space.toRepresentation (q g) v)) =
      g * embedding X K q hq hker (Multiplicative.ofAdd v) * g⁻¹ :=
  NormalElementaryQuotient.representation_apply X q hq hker g v.val

theorem central_iff (v : (s).space.toSubmodule) :
    v ∈ (s).central.toSubmodule ↔
      embedding X K q hq hker (Multiplicative.ofAdd v) ∈ centralizer (K : Set H) := by
  change (∀ c : K.map q, (s).space.toRepresentation c v = v) ↔ _
  constructor
  · intro hv k hk
    have hh := congrArg (fun w => embedding X K q hq hker (Multiplicative.ofAdd w))
      (hv (q.subgroupMap K ⟨k,hk⟩))
    change embedding X K q hq hker (Multiplicative.ofAdd
      ((s).space.toRepresentation (q k) v)) = _ at hh
    rw [embedding_conjugate] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro hv c
    obtain ⟨k,rfl⟩ := q.subgroupMap_surjective K c
    apply Multiplicative.ofAdd.injective
    apply embedding_injective X K q hq hker
    change embedding X K q hq hker (Multiplicative.ofAdd
      ((s).space.toRepresentation (q k) v)) = _
    rw [embedding_conjugate,hv k k.property,mul_inv_cancel_right]

variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  {τ : Representation (ZMod 2) A W}

theorem cover_action_conjugate
    (e : ActionEquiv ((s).action.comp (K.map q).subtype) τ)
    (k : K) (v : (s).space.toSubmodule) :
    embedding X K q hq hker (Multiplicative.ofAdd
      (MovedSection.coverAction s e (e.groupEquiv (q.subgroupMap K k)) v)) =
      (k:H) * embedding X K q hq hker (Multiplicative.ofAdd v) * (k:H)⁻¹ := by
  change embedding X K q hq hker (Multiplicative.ofAdd
    ((s).space.toRepresentation (e.groupEquiv.symm
      (e.groupEquiv (q.subgroupMap K k))) v)) = _
  rw [e.groupEquiv.symm_apply_apply]
  exact embedding_conjugate X K q hq hker k v

theorem cover_kernel_iff
    (e : ActionEquiv ((s).action.comp (K.map q).subtype) τ)
    (v : (s).space.toSubmodule) :
    MovedSection.coverProjection s e v = 0 ↔
      embedding X K q hq hker (Multiplicative.ofAdd v) ∈ centralizer (K : Set H) := by
  change e.linearEquiv ((s).central.toSubmodule.mkQ v) = 0 ↔ _
  rw [←e.linearEquiv.map_zero,e.linearEquiv.injective.eq_iff]
  change Submodule.Quotient.mk v = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact central_iff X K q hq hker v

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ElementaryMovedCover
