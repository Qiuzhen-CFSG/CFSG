module

public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.Quotient.Card

/-!
# Binary representations of centralizer quotients

A surjection whose kernel is the centralizer of a normal elementary abelian
subgroup induces a faithful binary representation on that subgroup. We identify
its fixed vectors with the relative centralizer. The Thompson-specific
offender bound is developed in `Stellmacher.CentralizerQuotientRepresentation`.

For a subspace coming from an actual subgroup, the preimage of its action
stabilizer is its ambient normalizer. Restricting the quotient map gives a
surjection from the normalizer inside any chosen subgroup onto the corresponding
action stabilizer. Thus quotients of the action stabilizer lift through the
possibly nontrivial action kernel.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), final proof of Theorem 15.3.1, printed p.1155.

-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace Representation.NormalElementaryQuotient
variable {G H : Type*} [Group G] [Group H]
  (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
  (q : G →* H) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (V : Set G))

include hker in
omit [IsElementaryAbelian 2 V] in
private theorem kernel_le_conjugation : q.ker ≤ (MulAut.conjNormal : G →* MulAut V).ker := by
  intro g hg
  rw [hker] at hg
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change g * (v : G) * g⁻¹ = v
  rw [← hg v v.property, mul_inv_cancel_right]

/-- Conjugation descended along the given centralizer quotient. -/
noncomputable def conjugationAut : H →* MulAut V :=
  q.liftOfSurjective hq ⟨MulAut.conjNormal, by exact kernel_le_conjugation V q hker⟩

omit [IsElementaryAbelian 2 V] in
/-- A quotient element represented by `g` acts by conjugation by `g`. -/
theorem conjugationAut_apply (g : G) (v : V) :
    ((conjugationAut V q hq hker (q g)) v : G) = g * (v : G) * g⁻¹ := by
  unfold conjugationAut
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- The descended action as a binary linear representation on the same group. -/
noncomputable def representation : Representation (ZMod 2) H (Additive V) where
  toFun h := (conjugationAut V q hq hker h).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul ((conjugationAut V q hq hker 1) v.toMul) = v
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul ((conjugationAut V q hq hker (a * b)) v.toMul) = _
    rw [map_mul]
    rfl

/-- The linear action agrees with ambient conjugation. -/
theorem representation_apply (g : G) (v : Additive V) :
    ((representation V q hq hker (q g) v).toMul : G) = g * (v.toMul : G) * g⁻¹ :=
  conjugationAut_apply V q hq hker g v.toMul

/-- The exact centralizer kernel makes the descended representation faithful. -/
theorem representation_injective : Function.Injective (representation V q hq hker) := by
  apply (representation V q hq hker).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro h hh
  obtain ⟨g, rfl⟩ := hq h
  have hg : g ∈ q.ker := by
    rw [hker]
    intro v hv
    have he := congrArg (fun f : Module.End (ZMod 2) (Additive V) =>
      ((f (Additive.ofMul ⟨v, hv⟩)).toMul : G)) hh
    change ((representation V q hq hker (q g) (Additive.ofMul ⟨v, hv⟩)).toMul : G) = v at he
    rw [representation_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  exact hg

open BinaryOffender

/-- Fixed vectors of the image of `A` are precisely the elements centralizing `A`. -/
theorem mem_fixedSpace_image (A : Subgroup G) (v : Additive V) :
    v ∈ fixedSpace (representation V q hq hker) (A.map q) ↔
      (v.toMul : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro hv a ha
    have h := congrArg (fun w : Additive V => (w.toMul : G))
      (hv ⟨q a, mem_map_of_mem q ha⟩)
    change ((representation V q hq hker (q a) v).toMul : G) = (v.toMul : G) at h
    rw [representation_apply] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · intro hv a
    obtain ⟨b, hb, hab⟩ := a.property
    change representation V q hq hker (a : H) v = v
    rw [← hab]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [representation_apply, hv b hb, mul_inv_cancel_right]

/-- Fixed vectors and the ambient relative centralizer have the same underlying set. -/
noncomputable def fixedSpaceEquiv (A : Subgroup G) :
    fixedSpace (representation V q hq hker) (A.map q) ≃
      (V ⊓ centralizer (A : Set G) : Subgroup G) where
  toFun v := ⟨v.val.toMul, v.val.toMul.property,
    (mem_fixedSpace_image V q hq hker A v.val).mp v.property⟩
  invFun v := ⟨Additive.ofMul ⟨v, v.property.1⟩,
    (mem_fixedSpace_image V q hq hker A _).mpr v.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The binary subspace underlying a subgroup of the normal elementary group. -/
noncomputable def subspace (P : Subgroup V) : Submodule (ZMod 2) (Additive V) :=
  AddSubgroup.toZModSubmodule 2 P.toAddSubgroup

/-- The preimage of the actual action stabilizer is the ambient normalizer. -/
theorem stabilizer_comap (P : Subgroup V) :
    (subspaceStabilizer (representation V q hq hker) (subspace V P)).comap q =
      normalizer (P.map V.subtype : Set G) := by
  ext g
  change (∀ v : Additive V, representation V q hq hker (q g) v ∈ subspace V P ↔
    v ∈ subspace V P) ↔ g ∈ normalizer (P.map V.subtype : Set G)
  rw [mem_normalizer_iff]
  constructor
  · intro hg x
    constructor
    · rintro ⟨v, hv, rfl⟩
      let w := representation V q hq hker (q g) (Additive.ofMul v)
      refine ⟨w.toMul, (hg (Additive.ofMul v)).mpr hv, ?_⟩
      exact representation_apply V q hq hker g (Additive.ofMul v)
    · intro hx
      have hv : x ∈ V := by
        have hconj : g * x * g⁻¹ ∈ V := (map_subtype_le P) hx
        have hi := (inferInstance : V.Normal).conj_mem _ hconj g⁻¹
        have he : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
        exact he ▸ hi
      let v : V := ⟨x, hv⟩
      refine ⟨v, (hg (Additive.ofMul v)).mp ?_, rfl⟩
      have hw : ((representation V q hq hker (q g) (Additive.ofMul v)).toMul : G) ∈
          P.map V.subtype := by rw [representation_apply]; exact hx
      obtain ⟨w, hw, he⟩ := hw
      have he' : w = (representation V q hq hker (q g) (Additive.ofMul v)).toMul :=
        Subtype.ext he
      exact he' ▸ hw
  · intro hg v
    change (representation V q hq hker (q g) v).toMul ∈ P ↔ v.toMul ∈ P
    have hm (w : V) : (w : G) ∈ P.map V.subtype ↔ w ∈ P := by
      constructor
      · rintro ⟨z, hz, he⟩
        exact (Subtype.ext he : z = w) ▸ hz
      · intro hw; exact mem_map_of_mem _ hw
    rw [← hm, ← hm, representation_apply]
    exact (hg (v.toMul : G)).symm

/-- Restriction of the quotient map to the normalizer in a chosen subgroup. -/
noncomputable def normalizerProjection (X : Subgroup G) (P : Subgroup V) :
    (X ⊓ normalizer (P.map V.subtype : Set G) : Subgroup G) →*
      (X.map q ⊓ subspaceStabilizer (representation V q hq hker) (subspace V P) : Subgroup H) :=
  (q.comp (X ⊓ normalizer (P.map V.subtype : Set G)).subtype).codRestrict _ (by
    intro x
    refine ⟨mem_map_of_mem q x.property.1, ?_⟩
    exact (congrArg (fun K : Subgroup G => (x : G) ∈ K)
      (stabilizer_comap V q hq hker P)).mpr x.property.2)

/-- Stabilizer elements lift even when the action kernel is nontrivial. -/
theorem normalizerProjection_surjective (X : Subgroup G) (P : Subgroup V) :
    Function.Surjective (normalizerProjection V q hq hker X P) := by
  rintro ⟨h, hX, hP⟩
  obtain ⟨x, hx, rfl⟩ := hX
  have hn : x ∈ normalizer (P.map V.subtype : Set G) := by
    rw [← stabilizer_comap V q hq hker P]
    exact hP
  exact ⟨⟨x, hx, hn⟩, rfl⟩

/-- A quotient of the action stabilizer lifts to a quotient of the actual normalizer. -/
theorem exists_surjective_normalizer_hom (X : Subgroup G) (P : Subgroup V)
    {K : Type*} [Group K]
    (f : (X.map q ⊓ subspaceStabilizer (representation V q hq hker) (subspace V P) : Subgroup H) →* K)
    (hf : Function.Surjective f) :
    ∃ F : (X ⊓ normalizer (P.map V.subtype : Set G) : Subgroup G) →* K,
      Function.Surjective F :=
  ⟨f.comp (normalizerProjection V q hq hker X P),
    hf.comp (normalizerProjection_surjective V q hq hker X P)⟩

end Representation.NormalElementaryQuotient

namespace Subgroup
variable {G : Type*} [Group G]

/-- Restricting an ambient normalizer intersection to a local overgroup
preserves its actual group, provided both subgroups lie in that overgroup. -/
noncomputable def localNormalizerIntersectionEquiv (L X P : Subgroup G)
    (hX : X ≤ L) (hP : P ≤ L) :
    (X.subgroupOf L ⊓ normalizer (P.subgroupOf L : Set L) : Subgroup L) ≃*
      (X ⊓ normalizer (P : Set G) : Subgroup G) := by
  have he : (X ⊓ normalizer (P : Set G)).subgroupOf L =
      X.subgroupOf L ⊓ normalizer (P.subgroupOf L : Set L) := by
    rw [← subgroupOf_normalizer_eq hP]
    rfl
  exact (MulEquiv.subgroupCongr he.symm).trans
    (subgroupOfEquivOfLe (inf_le_left.trans hX))

end Subgroup
