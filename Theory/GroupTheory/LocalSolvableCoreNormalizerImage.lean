module
public import Theory.GroupTheory.LocalSolvableCoreNormalizer
public import Theory.GroupTheory.SylowSubgroupNormalizerImage
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Images of local solvable-core normalizer residuals

A surjection with solvable kernel carries the normalizer of a Sylow intersection
with the solvable radical onto the corresponding normalizer in the quotient.
Its perfect residual therefore has exactly the expected image. The other two
lemmas identify the intrinsic normalizer with its ambient subgroup and retain
the literal map through an intermediate subgroup.

These transports are used for the residual N_J(T ∩ O_{2,2′,2}(J))^∞ in
Aschbacher--Smith, Proposition 9.3.1, printed p.732.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.LocalSolvableCoreNormalizer

private theorem residual_image
    {X Y : Type*} [Group X] [Group Y] [Finite X]
    (U : Subgroup X) (f : X →* Y) :
    ((solvableResidual U).map U.subtype).map f =
      (solvableResidual (U.map f)).map (U.map f).subtype := by
  have he := congrArg (map (U.map f).subtype)
    (map_solvableResidual_eq (f.subgroupMap U) (f.subgroupMap_surjective U))
  have hc : (U.map f).subtype.comp (f.subgroupMap U) = f.comp U.subtype := by
    ext x
    rfl
  simpa only [map_map,hc] using he

theorem radical_normalizer_residual_map
    {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (P : Sylow 2 X) (f : X →* Y) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker] :
    ((solvableResidual (normalizer (((P : Subgroup X) ⊓ solvableRadical X : Subgroup X) : Set X))).map
      (normalizer (((P : Subgroup X) ⊓ solvableRadical X : Subgroup X) : Set X)).subtype).map f =
      (solvableResidual (normalizer (((P.mapSurjective hf : Subgroup Y) ⊓ solvableRadical Y : Subgroup Y) : Set Y))).map
        (normalizer (((P.mapSurjective hf : Subgroup Y) ⊓ solvableRadical Y : Subgroup Y) : Set Y)).subtype := by
  have hk : f.ker ≤ solvableRadical X := le_solvableRadical _ inferInstance inferInstance
  have hR := comap_solvableRadical_eq_of_solvable_ker f hf
  have hmap : ((P : Subgroup X) ⊓ solvableRadical X).map f =
      (P.mapSurjective hf : Subgroup Y) ⊓ solvableRadical Y := by
    rw [← hR]
    ext y
    constructor
    · rintro ⟨x,⟨hx,hR⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,hR⟩
    · rintro ⟨⟨x,hx,rfl⟩,hR⟩
      exact ⟨x,⟨hx,hR⟩,rfl⟩
  rw [residual_image, P.normalizer_map_of_contains_kernel_intersection
    ((P : Subgroup X) ⊓ solvableRadical X) inf_le_left f hf (inf_le_inf_left _ hk), hmap]

theorem intrinsic_localNormalizerResidual
    {X : Type*} [Group X] [Finite X]
    (J S : Subgroup X) (R : Subgroup J) :
    ((solvableResidual (normalizer (((S.subgroupOf J) ⊓ R : Subgroup J) : Set J))).map
      (normalizer (((S.subgroupOf J) ⊓ R : Subgroup J) : Set J)).subtype).map J.subtype =
      localNormalizerResidual J (S ⊓ R.map J.subtype) := by
  have hQ : (S ⊓ R.map J.subtype).subgroupOf J = S.subgroupOf J ⊓ R := by
    ext x
    simp only [mem_subgroupOf, mem_inf, mem_map, Subtype.exists]
    constructor
    · rintro ⟨hs,y,hy,hr,he⟩
      have hh : (⟨y,hy⟩ : J) = x := Subtype.ext he
      exact ⟨hs,hh ▸ hr⟩
    · rintro ⟨hs,hr⟩
      exact ⟨hs,x,x.property,hr,rfl⟩
  have hQJ : S ⊓ R.map J.subtype ≤ J := inf_le_right.trans (map_subtype_le R)
  have hn : (normalizer (((S.subgroupOf J) ⊓ R : Subgroup J) : Set J)).map J.subtype =
      J ⊓ normalizer ((S ⊓ R.map J.subtype : Subgroup X) : Set X) := by
    rw [← hQ, ← subgroupOf_normalizer_eq hQJ, subgroupOf_map_subtype, inf_comm]
  rw [residual_image,hn]
  rfl

theorem subgroup_image_ambient_quotient
    {X Y : Type*} [Group X] [Group Y]
    (N J : Subgroup X) (hJN : J ≤ N) (q : N →* Y) (U : Subgroup J) :
    ((U.map J.subtype).subgroupOf N).map q =
      ((U.map ((q.subgroupMap (J.subgroupOf N)).comp
        (subgroupOfEquivOfLe hJN).symm.toMonoidHom)).map
          ((J.subgroupOf N).map q).subtype) := by
  let j : J.subgroupOf N ≃* J := subgroupOfEquivOfLe hJN
  let i : J →* N := (J.subgroupOf N).subtype.comp j.symm.toMonoidHom
  have hi : N.subtype.comp i = J.subtype := by ext x; rfl
  have hU : (U.map J.subtype).subgroupOf N = U.map i := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le U).trans hJN), map_map, hi]
  rw [hU,map_map,map_map]
  rfl

end Theory.GroupTheory.LocalSolvableCoreNormalizer
