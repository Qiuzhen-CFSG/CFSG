module
public import Theory.Representation.BinaryTensorThree.Normalizer
public import Theory.Representation.BinaryTensorThree.SylowMarking
public import Theory.Representation.BinaryOffender.NormalizerNonFF
public import Theory.Representation.BinaryOffender.DisjointSectionBudget

/-!
# Tensor sections and the original elementary-actor budget

The full linear normalizer of the binary three-by-three tensor base is its
concrete wreath group, whose action is non-FF. Equivariant normal-model
transport gives non-FF for every marked tensor action image, even when its
ambient group has a kernel. If an elementary actor has trivial intersection
with the centralizer of the marked normal product, its action on each tensor
section is faithful. Two disjoint such sections exceed twice its rank.

The restriction theorem retains the same original actor and normal product
inside any intermediate subgroup preserving the two sections. It is used
on the original terminal U/Z in the14.6.22 support argument.
Source: Aschbacher--Smith D.3.9, F.9.18(2--5), printed pp.199--200,325--326.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryTensorThree

/-- The faithful tensor action of the two natural factors. -/
@[expose] def baseRepresentation : Representation (ZMod 2) (Factor × Factor) Space :=
  action.comp baseEmbedding

/-- Over the binary field the tensor base has no scalar kernel. -/
theorem baseRepresentation_faithful : Function.Injective baseRepresentation := by
  intro x y hxy
  apply baseAction_injective
  exact LinearEquiv.toLinearMap_injective hxy

/-- The entire linear normalizer of the tensor base is non-FF. -/
theorem not_isFFModule_base_normalizer :
    ¬ IsFFModule (normalizerRepresentation baseRepresentation) := by
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Space
  have hi : (actionImage baseRepresentation).map e.toMonoidHom = baseAction.range := by
    ext g
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      exact ⟨x,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨baseRepresentation.asGroupHom x,⟨x,rfl⟩,rfl⟩
  have hn (g : linearNormalizer baseRepresentation) : e g.val ∈ tensorGroup := by
    rw [←normalizer_baseAction_range,←hi]
    exact (le_normalizer_map e.toMonoidHom) (mem_map_of_mem e.toMonoidHom g.property)
  let f : linearNormalizer baseRepresentation →* Group :=
    (e.toMonoidHom.comp (linearNormalizer baseRepresentation).subtype).codRestrict _ hn
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (e.injective (congrArg Subtype.val hxy))
  intro h
  exact action_notFF (h.map_equivariant _ _ f hf (LinearEquiv.refl _ _) (fun _ _ => rfl))

/-- A normal tensor marking excludes FF for the faithful action image. -/
theorem not_isFFModule_image_of_marked_tensor
    {H V : Type*} [_root_.Group H] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (N : Subgroup H) [N.Normal]
    (f : N →* Factor × Factor) (hf : Function.Surjective f)
    (b : Representation.Equiv (ρ.comp N.subtype) (baseRepresentation.comp f)) :
    ¬ IsFFModule (imageRepresentation ρ) := by
  let : N.subtype.range.Normal := by rw [range_subtype]; infer_instance
  exact not_isFFModule_image_of_marked_normal_range ρ N.subtype
    baseRepresentation f hf b not_isFFModule_base_normalizer

variable {D V : Type*} [_root_.Group D] [AddCommGroup V] [Module (ZMod 2) V]

private theorem faithful_on_marked_tensor
    (σ : Representation (ZMod 2) D V) (N : Subgroup D)
    (e : N ≃* Factor × Factor)
    (b : Representation.Equiv (σ.comp N.subtype) (baseRepresentation.comp e.toMonoidHom)) :
    ∀ n ∈ N, (∀ v, σ n v = v) → n = 1 := by
  intro n hn hf
  have he : e ⟨n,hn⟩ = 1 := by
    apply baseRepresentation_faithful
    rw [map_one]
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := b.toLinearEquiv.surjective w
    have h := Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap ⟨n,hn⟩ v
    change b.toLinearEquiv (σ n v) = baseRepresentation (e ⟨n,hn⟩) (b.toLinearEquiv v) at h
    exact (h.symm.trans (congrArg b.toLinearEquiv (hf v)))
  exact congrArg Subtype.val (e.injective (he.trans e.map_one.symm))

private theorem actor_faithful_on_marked_tensor
    (σ : Representation (ZMod 2) D V) (N A : Subgroup D) [N.Normal]
    (e : N ≃* Factor × Factor)
    (b : Representation.Equiv (σ.comp N.subtype) (baseRepresentation.comp e.toMonoidHom))
    (hAC : A ⊓ centralizer (N : Set D) = ⊥) :
    ∀ a ∈ A, (∀ v, σ a v = v) → a = 1 := by
  have hf := actor_faithful_on_section σ N A ⊤ (by intro n hn v; simp)
    (fun n hn h => faithful_on_marked_tensor σ N e b n hn (fun v => h v Submodule.mem_top))
    (by rw [normalizer_eq_top]; exact le_top) hAC
  exact fun a ha h => hf a ha (fun v _ => h v)

/-- Two disjoint marked tensor sections exceed the same actor's two-rank budget. -/
theorem twice_rank_lt_fixedCodim_of_disjoint_marked_tensors
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (N A : Subgroup D) [N.Normal]
    (hA : IsElementaryTwo A) (hAC : A ⊓ centralizer (N : Set D) = ⊥)
    (U W : Subrepresentation ρ) (hd : Disjoint U.toSubmodule W.toSubmodule)
    (eU eW : N ≃* Factor × Factor)
    (bU : Representation.Equiv (U.toRepresentation.comp N.subtype)
      (baseRepresentation.comp eU.toMonoidHom))
    (bW : Representation.Equiv (W.toRepresentation.comp N.subtype)
      (baseRepresentation.comp eW.toMonoidHom)) :
    2 * rank A < fixedCodim ρ A := by
  exact twice_rank_lt_fixedCodim_of_disjoint_nonFF_subrepresentations ρ U W hd hA
    (fun a ha h => actor_faithful_on_marked_tensor U.toRepresentation N A eU bU hAC a ha h)
    (fun a ha h => actor_faithful_on_marked_tensor W.toRepresentation N A eW bW hAC a ha h)
    (not_isFFModule_image_of_marked_tensor U.toRepresentation N eU.toMonoidHom eU.surjective bU)
    (not_isFFModule_image_of_marked_tensor W.toRepresentation N eW.toMonoidHom eW.surjective bW)

/-- The tensor obstruction retains the original actor under subgroup restriction. -/
theorem twice_rank_lt_fixedCodim_of_restricted_marked_tensors
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (N A : Subgroup D) [N.Normal]
    (hA : IsElementaryTwo A) (hAC : A ⊓ centralizer (N : Set D) = ⊥)
    (J : Subgroup D) (hAJ : A ≤ J) (hNJ : N ≤ J)
    (U W : Subrepresentation (ρ.comp J.subtype))
    (hd : Disjoint U.toSubmodule W.toSubmodule)
    (eU eW : N.subgroupOf J ≃* Factor × Factor)
    (bU : Representation.Equiv (U.toRepresentation.comp (N.subgroupOf J).subtype)
      (baseRepresentation.comp eU.toMonoidHom))
    (bW : Representation.Equiv (W.toRepresentation.comp (N.subgroupOf J).subtype)
      (baseRepresentation.comp eW.toMonoidHom)) :
    2 * rank A < fixedCodim ρ A := by
  let : IsElementaryAbelian 2 A := hA.2
  have hA' : IsElementaryTwo (A.subgroupOf J) := by
    refine ⟨?_, IsElementaryAbelian.subgroupOf hAJ⟩
    intro hz
    apply hA.1
    rw [←map_subgroupOf_eq_of_le hAJ,hz,Subgroup.map_bot]
  have hAC' : A.subgroupOf J ⊓ centralizer (N.subgroupOf J : Set J) = ⊥ := by
    apply bot_unique
    rintro a ⟨ha,hc⟩
    apply mem_bot.mpr
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hAC]
    refine ⟨ha,fun n hn => ?_⟩
    exact congrArg Subtype.val (hc ⟨n,hNJ hn⟩ hn)
  have hb := twice_rank_lt_fixedCodim_of_disjoint_marked_tensors (ρ.comp J.subtype)
    (N.subgroupOf J) (A.subgroupOf J) hA' hAC' U W hd eU eW bU bW
  rwa [rank_subgroupOf hAJ,fixedCodim_subgroupOf ρ hAJ] at hb

end BinaryTensorThree
