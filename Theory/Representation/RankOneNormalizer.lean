module
public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Irreducible subgroups normalized by a rank-one operator

Conjugation by the normalizing operator acts on the commuting division
algebra of the irreducible subgroup. For an endomorphism f, the difference
between its conjugate and itself has image in W + f(W), where W is the
one-dimensional displacement space. In dimension greater than two this
difference cannot be injective, so Schur's lemma makes it zero. Thus f
preserves W and its eigenvalue there forces f to be a scalar.

The literal normal-subgroup and image-normalizer applications prove absolute
irreducibility over the original coefficient field. This removes the
extension-field natural branch in the degree-four inspection of
Aschbacher--Smith G.4.1, printed p.342, after G.4.9 supplies irreducibility.
-/

@[expose] public noncomputable section
namespace Representation.RankOneNormalizer
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (ρ : Representation F G V) [ρ.IsIrreducible]

private def conjugateEnd (α : G ≃* G) (T : V ≃ₗ[F] V)
    (hT : ∀g v,T (ρ g v)=ρ (α g) (T v)) (f : ρ.End) : ρ.End where
  toLinearMap := T.toLinearMap.comp (f.toLinearMap.comp T.symm.toLinearMap)
  isIntertwining' g := by
    ext v
    have hi : T.symm (ρ g v)=ρ (α.symm g) (T.symm v) := by
      apply T.injective
      simpa using (hT (α.symm g) (T.symm v)).symm
    change T (f (T.symm (ρ g v)))=ρ g (T (f (T.symm v)))
    rw [hi,IntertwiningMap.isIntertwining]
    simpa using hT (α.symm g) (f (T.symm v))

private theorem conjugateEnd_eq (α : G ≃* G) (T : V ≃ₗ[F] V)
    (hT : ∀g v,T (ρ g v)=ρ (α g) (T v))
    (hd : 2 < Module.finrank F V)
    (hr : Module.finrank F (LinearMap.range (T.toLinearMap-1))=1)
    (f : ρ.End) : conjugateEnd ρ α T hT f=f := by
  let W := LinearMap.range (T.toLinearMap-1)
  let d := conjugateEnd ρ α T hT f-f
  have hrange : LinearMap.range d.toLinearMap ≤ W ⊔ W.map f.toLinearMap := by
    rintro _ ⟨v,rfl⟩
    have hfirst : T (f (T.symm v))-f (T.symm v) ∈ W := ⟨f (T.symm v),rfl⟩
    have hsecond : f (T (T.symm v)-T.symm v) ∈ W.map f.toLinearMap :=
      ⟨_,⟨T.symm v,rfl⟩,rfl⟩
    have hs := (W ⊔ W.map f.toLinearMap).sub_mem
      (show _ ∈ W ⊔ W.map f.toLinearMap from (show W ≤ W ⊔ W.map f.toLinearMap from le_sup_left) hfirst)
      (show _ ∈ W ⊔ W.map f.toLinearMap from (show W.map f.toLinearMap ≤ W ⊔ W.map f.toLinearMap from le_sup_right) hsecond)
    convert hs using 1
    change T (f (T.symm v))-f v = _
    rw [map_sub,T.apply_symm_apply]
    abel
  have hb : Module.finrank F (LinearMap.range d.toLinearMap) ≤ 2 := by
    have h1 := Submodule.finrank_mono hrange
    have h2 := Submodule.finrank_add_le_finrank_add_finrank W (W.map f.toLinearMap)
    have h3 := Submodule.finrank_map_le f.toLinearMap W
    change Module.finrank F W=1 at hr
    omega
  rcases IsIrreducible.injective_or_eq_zero d with hi|hz
  · have he := LinearMap.finrank_range_of_inj hi
    omega
  · exact sub_eq_zero.mp hz
/-- A rank-one normalizer of an irreducible action in dimension greater than
 two forces its entire commuting algebra to be scalar. -/
theorem end_scalar_of_rank_one_normalizer
    (α : G ≃* G) (T : V ≃ₗ[F] V)
    (hT : ∀g v,T (ρ g v)=ρ (α g) (T v))
    (hd : 2 < Module.finrank F V)
    (hr : Module.finrank F (LinearMap.range (T.toLinearMap-1))=1)
    (f : ρ.End) : ∃c:F,f=algebraMap F ρ.End c := by
  have he := conjugateEnd_eq ρ α T hT hd hr f
  have hf (v:V) : f (T v)=T (f v) := by
    have hh := congrArg (fun e:ρ.End=>e (T v)) he
    change T (f (T.symm (T v)))=f (T v) at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh.symm
  let W := LinearMap.range (T.toLinearMap-1)
  have hW : W≠⊥ := by
    intro h
    change Module.finrank F W=1 at hr
    rw [h,finrank_bot] at hr
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hfv : f v∈W := by
    obtain ⟨w,rfl⟩ := hv
    refine ⟨f w,?_⟩
    change T (f w)-f w=f (T w-w)
    rw [map_sub,hf]
  have hline := eq_span_singleton_of_mem_of_finrank_eq_one hr hv hv0
  change f v∈LinearMap.range (T.toLinearMap-1) at hfv
  rw [hline] at hfv
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hfv
  refine ⟨c,?_⟩
  have hz : f-algebraMap F ρ.End c=0 := by
    rcases IsIrreducible.injective_or_eq_zero (f-algebraMap F ρ.End c) with hi|hz
    · have hh : (f-algebraMap F ρ.End c) v=(f-algebraMap F ρ.End c) 0 := by
        change f v-c•v=_
        rw [hc,sub_self,map_zero]
      exact (hv0 (hi hh)).elim
    · exact hz
  exact sub_eq_zero.mp hz

/-- Absolute irreducibility is inherited by an irreducible normal subgroup
when a rank-one linear normalizer acts on a space of dimension greater than two. -/
theorem absolutelyIrreducible_of_rank_one_normalizer
    (α : G ≃* G) (T : V ≃ₗ[F] V)
    (hT : ∀g v,T (ρ g v)=ρ (α g) (T v))
    (hd : 2 < Module.finrank F V)
    (hr : Module.finrank F (LinearMap.range (T.toLinearMap-1))=1) :
    ρ.IsAbsolutelyIrreducible := by
  apply (isAbsolutelyIrreducible_iff_surjective ρ).mpr
  intro f
  obtain ⟨c,hc⟩ := end_scalar_of_rank_one_normalizer ρ α T hT hd hr f
  exact ⟨c,hc.symm⟩
omit [ρ.IsIrreducible] in
/-- The literal image normalizer suffices; relative normality in a selected
larger group is unnecessary. -/
theorem subgroup_absolutelyIrreducible_of_rank_one_normalizer
    {A : Type*} [Group A] (σ : Representation F A V)
    (N : Subgroup A) [IsIrreducible (σ.comp N.subtype)]
    (t : A) (ht : t∈Subgroup.normalizer (N:Set A))
    (hd : 2 < Module.finrank F V)
    (hr : Module.finrank F (LinearMap.range (σ t-1))=1) :
    IsAbsolutelyIrreducible (σ.comp N.subtype) := by
  let T : V≃ₗ[F]V := {
    toLinearMap := σ t
    invFun := σ t⁻¹
    left_inv := σ.inv_self_apply t
    right_inv := σ.self_inv_apply t }
  apply absolutelyIrreducible_of_rank_one_normalizer (σ.comp N.subtype)
    (N.normalizerMonoidHom ⟨t,ht⟩) T _ hd hr
  intro g v
  change σ t (σ g v)=σ (t*(g:A)*t⁻¹) (σ t v)
  simp only [map_mul,Module.End.mul_apply,Representation.inv_self_apply]

omit [ρ.IsIrreducible] in
/-- Literal restriction to a normal subgroup, retaining the original action
and the original rank-one element in the larger group. -/
theorem restriction_absolutelyIrreducible_of_rank_one
    {A : Type*} [Group A] (σ : Representation F A V)
    (N : Subgroup A) [N.Normal] [IsIrreducible (σ.comp N.subtype)]
    (t : A) (hd : 2 < Module.finrank F V)
    (hr : Module.finrank F (LinearMap.range (σ t-1))=1) :
    IsAbsolutelyIrreducible (σ.comp N.subtype) := by
  let T : V≃ₗ[F]V := {
    toLinearMap := σ t
    invFun := σ t⁻¹
    left_inv := σ.inv_self_apply t
    right_inv := σ.self_inv_apply t }
  apply absolutelyIrreducible_of_rank_one_normalizer (σ.comp N.subtype)
    (MulAut.conjNormal t) T _ hd hr
  intro g v
  change σ t (σ g v)=σ ((MulAut.conjNormal t g):A) (σ t v)
  rw [MulAut.conjNormal_apply]
  simp only [map_mul,Module.End.mul_apply,Representation.inv_self_apply]
end Representation.RankOneNormalizer
