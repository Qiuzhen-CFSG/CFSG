module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.Geometry
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModuleContract

/-!
# Literal action comparisons in the nonsplit B.5.6 endgame

On V₂=C_V(G₁), the G₂-fixed vectors are exactly the globally fixed vectors.
The original quotient map consequently identifies V₂/C_V₂(G₂) with the
image of V₂ in V/C_V(G). The same construction applies to every submodule
of V₂ supplementing C_V(G), including the ambient moved space [V,G₂].

If the factor module supplied by B.5.11 is its own moved space, its fixed
supplement gives [V,G₂]+C_V(G)=V₂. The quotient comparisons then retain the
actual natural SL₂ action on the reduced ambient moved space. No transfer
of offender generation from V₂ to V is used or asserted.

The four-space transport reconstructs every B.4.8(3) clause from the full
universal EarlierB48Three input. Its applicability uses the transported
indecomposability, dimension, natural moved space and faithfulness. This
input remains owned by qt-b-04-natural-extensions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(3),
printed p.91, and the final proof of B.5.6, printed p.110.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
universe u v w z
variable {D : Type u} {E : Type w} [Group D] [Group E]
  {U : Type v} {T : Type z} [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup T] [Module (ZMod 2) T]
  {σ : Representation (ZMod 2) D U} {τ : Representation (ZMod 2) E T}

private def pullback (e : ActionEquiv σ τ) (N : Subrepresentation τ) : Subrepresentation σ where
  toSubmodule := N.toSubmodule.comap e.linearEquiv.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change e.linearEquiv (σ g v) ∈ N
    rw [e.intertwines]
    exact N.apply_mem_toSubmodule _ hv

private theorem indecomposable_transport (e : ActionEquiv σ τ) (h : IsIndecomposable σ) :
    IsIndecomposable τ := by
  let := h.1
  refine ⟨e.linearEquiv.injective.nontrivial, fun A B hc => ?_⟩
  have hc' : IsCompl (pullback e A).toSubmodule (pullback e B).toSubmodule :=
    (Submodule.orderIsoMapComap e.linearEquiv).symm.isCompl hc
  have hz (N : Subrepresentation τ) (hn : pullback e N = ⊥) : N = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    obtain ⟨x,rfl⟩ := e.linearEquiv.surjective v
    have hx : x ∈ pullback e N := hv
    rw [hn] at hx
    simpa using congrArg e.linearEquiv (show x = 0 from hx)
  exact (h.2 _ _ hc').imp (hz A) (hz B)

private noncomputable def pullbackEquiv (e : ActionEquiv σ τ) (N : Subrepresentation τ) :
    ActionEquiv (pullback e N).toRepresentation N.toRepresentation where
  groupEquiv := e.groupEquiv
  linearEquiv :=
    { toFun := fun x => ⟨e.linearEquiv x,x.property⟩
      invFun := fun y => ⟨e.linearEquiv.symm y,by
        change e.linearEquiv (e.linearEquiv.symm y) ∈ N
        simp only [e.linearEquiv.apply_symm_apply]; exact y.property⟩
      left_inv := fun x => Subtype.ext (e.linearEquiv.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.linearEquiv.apply_symm_apply y)
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun a x => Subtype.ext (map_smul _ _ _) }
  intertwines g x := Subtype.ext (e.intertwines g x)

private theorem pullback_moved (e : ActionEquiv σ τ) (N : Subrepresentation τ)
    (hn : N.toSubmodule = moved τ ⊤) :
    (pullback e N).toSubmodule = moved σ ⊤ := by
  apply (Submodule.orderIsoMapComap e.linearEquiv).injective
  change ((N.toSubmodule.comap e.linearEquiv.toLinearMap).map e.linearEquiv.toLinearMap) = _
  rw [Submodule.map_comap_eq_of_surjective e.linearEquiv.surjective, hn]
  have hh := subspaceCommutator_map_embedding τ σ e.groupEquiv.symm.toMonoidHom
    e.linearEquiv.toLinearMap (fun g v => by
      simpa using (e.intertwines (e.groupEquiv.symm g) v).symm) ⊤ ⊤
  change moved τ ⊤ = (moved σ ⊤).map e.linearEquiv.toLinearMap
  simpa only [Submodule.map_top, LinearEquiv.range, Subgroup.map_top_of_surjective e.groupEquiv.symm.toMonoidHom
    e.groupEquiv.symm.surjective] using hh

private theorem faithful_of_natural (N : Subrepresentation σ)
    (e : ActionEquiv N.toRepresentation (linearNatural BinaryField.two 3)) :
    Function.Injective σ := by
  intro g h he
  apply e.groupEquiv.injective
  apply specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
  have hw : N.toRepresentation g w = N.toRepresentation h w := by
    exact Subtype.ext (LinearMap.congr_fun he w)
  exact (e.intertwines g w).symm.trans ((congrArg e.linearEquiv hw).trans (e.intertwines h w))

theorem four_source_transport [Finite D] [FiniteDimensional (ZMod 2) U]
    (h48 : EarlierB48Three.{u,v}) (e : ActionEquiv σ τ) (q : FourDimensionalSource τ) :
    Nonempty (FourDimensionalSource σ) := by
  let N := pullback e q.space
  let p := pullbackEquiv e q.space
  let n : ActionEquiv N.toRepresentation (linearNatural BinaryField.two 3) :=
    ⟨p.groupEquiv.trans q.natural.groupEquiv,p.linearEquiv.trans q.natural.linearEquiv,
      fun g v => (congrArg q.natural.linearEquiv (p.intertwines g v)).trans
        (q.natural.intertwines _ _)⟩
  have hn := pullback_moved e q.space q.space_eq
  have hi := indecomposable_transport (actionSymm e) q.indecomposable
  have hd := e.linearEquiv.finrank_eq.trans q.dimension
  obtain ⟨ho,hq,ha⟩ := h48 D U σ (faithful_of_natural N n) hi hd N hn n
  exact ⟨⟨hd,hi,N,hn,n,ho,hq,ha⟩⟩

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}
open ComponentReduction

theorem second_invariants_iff (c : Conclusion ρ) (v : c.productConfiguration.fixed) :
    v ∈ (Representation.invariants (secondAction c)) ↔ (v : V) ∈ ρ.invariants := by
  constructor
  · intro hv g
    obtain ⟨a,b,rfl⟩ := c.productConfiguration.product.exists_mul g
    have ha : ρ (a : G) v = v := by
      have hm := v.property
      change (v : V) ∈ c.productConfiguration.fixed.toSubmodule at hm
      rw [c.productConfiguration.fixed_eq] at hm
      exact hm a
    have hb : ρ (b : G) v = v := congrArg Subtype.val (hv b)
    rw [map_mul, Module.End.mul_apply, hb, ha]
  · intro hv b
    exact Subtype.ext (hv b)

theorem second_supplement_of_moved_factor (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hm : f.space.toSubmodule = moved (secondAction c) ⊤) :
    moved ρ (second c) ⊔ ρ.invariants = c.productConfiguration.fixed.toSubmodule := by
  apply le_antisymm (sup_le (second_moved_le_fixed c he) (invariants_le_fixed c))
  have hmv : moved (secondAction c) ⊤ ≤
      (moved ρ (second c)).comap c.productConfiguration.fixed.toSubmodule.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b,_,v,_,rfl⟩
    exact Submodule.subset_span ⟨b,b.property,v,Submodule.mem_top,rfl⟩
  intro v hv
  have ht : (⟨v,hv⟩ : c.productConfiguration.fixed.toSubmodule) ∈
      f.space.toSubmodule ⊔ Representation.invariants (secondAction c) := by
    rw [f.supplement]
    trivial
  obtain ⟨a,ha,z,hz,haz⟩ := Submodule.mem_sup.mp ht
  rw [hm] at ha
  exact Submodule.mem_sup.mpr ⟨a,hmv ha,z,(second_invariants_iff c z).mp hz,
    congrArg Subtype.val haz⟩

noncomputable def secondQuotientEquiv (c : Conclusion ρ) :
    ActionEquiv (reducedAction (secondAction c))
      (((fixed ρ).quotientImage c.productConfiguration.fixed).toRepresentation.comp
        (second c).subtype) := by
  let Q := (fixed ρ).quotientImage c.productConfiguration.fixed
  let f : c.productConfiguration.fixed.toSubmodule →ₗ[ZMod 2] Q.toSubmodule :=
    { toFun := fun v => ⟨ρ.invariants.mkQ v,⟨v,v.property,rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  have hf : (Representation.invariants (secondAction c)) = f.ker := by
    ext v
    rw [second_invariants_iff]
    change (v : V) ∈ ρ.invariants ↔ f v = 0
    rw [Subtype.ext_iff]
    exact (Submodule.Quotient.mk_eq_zero ρ.invariants).symm
  let fbar := (Representation.invariants (secondAction c)).liftQ f hf.le
  have hi : Function.Injective fbar := by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot' _ _ hf
  have hs : Function.Surjective fbar := by
    rintro ⟨q,v,hv,rfl⟩
    exact ⟨(Representation.invariants (secondAction c)).mkQ ⟨v,hv⟩,rfl⟩
  refine ⟨MulEquiv.refl _,LinearEquiv.ofBijective fbar ⟨hi,hs⟩,?_⟩
  intro g v
  induction v using Submodule.Quotient.induction_on
  rfl

noncomputable def factorQuotientEquiv (c : Conclusion ρ)
    (f : FactorModuleConclusion (secondAction c)) :
    ActionEquiv (((fixed (secondAction c)).quotientImage f.space).toRepresentation.comp
      (⊤ : Subgroup (second c)).subtype)
      (((fixed ρ).quotientImage c.productConfiguration.fixed).toRepresentation.comp
        (second c).subtype) := by
  let Q := (fixed (secondAction c)).quotientImage f.space
  have hQ : Q = ⊤ := (Subrepresentation.quotientImage_eq_top_iff _ _).mpr (by
    simpa only [fixed, sup_comm] using f.supplement)
  let j : Q.toSubmodule ≃ₗ[ZMod 2] _ := LinearEquiv.ofBijective Q.toSubmodule.subtype
    ⟨Q.toSubmodule.subtype_injective,by
      intro v
      exact ⟨⟨v,by rw [hQ]; trivial⟩,rfl⟩⟩
  let e := secondQuotientEquiv c
  exact ⟨Subgroup.topEquiv,j.trans e.linearEquiv,
    fun g v => by
      change e.linearEquiv ((reducedAction (secondAction c)) g.val v.val) = _
      exact e.intertwines g.val v.val⟩

noncomputable def secondSubspaceQuotientEquiv (c : Conclusion ρ) (U : Subrepresentation ρ)
    (hU : U.toSubmodule ≤ c.productConfiguration.fixed.toSubmodule)
    (hs : U.toSubmodule ⊔ ρ.invariants = c.productConfiguration.fixed.toSubmodule) :
    ActionEquiv (reducedAction (U.toRepresentation.comp (second c).subtype))
      (((fixed ρ).quotientImage c.productConfiguration.fixed).toRepresentation.comp
        (second c).subtype) := by
  let Q := (fixed ρ).quotientImage c.productConfiguration.fixed
  let σ := U.toRepresentation.comp (second c).subtype
  let f : U.toSubmodule →ₗ[ZMod 2] Q.toSubmodule :=
    { toFun := fun v => ⟨ρ.invariants.mkQ v,⟨v,hU v.property,rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  have hv (v : U.toSubmodule) : v ∈ Representation.invariants σ ↔ (v : V) ∈ ρ.invariants := by
    rw [← second_invariants_iff c ⟨v,hU v.property⟩]
    constructor
    · intro h g
      exact Subtype.ext (congrArg (fun x : U.toSubmodule => (x : V)) (h g))
    · intro h g
      exact Subtype.ext (congrArg
        (fun x : c.productConfiguration.fixed.toSubmodule => (x : V)) (h g))
  have hf : Representation.invariants σ = f.ker := by
    ext v
    rw [hv]
    change (v : V) ∈ ρ.invariants ↔ f v = 0
    rw [Subtype.ext_iff]
    exact (Submodule.Quotient.mk_eq_zero ρ.invariants).symm
  let fbar := (Representation.invariants σ).liftQ f hf.le
  have hi : Function.Injective fbar := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' _ _ hf)
  have hsurj : Function.Surjective fbar := by
    rintro ⟨q,v,hv,rfl⟩
    rw [← hs] at hv
    obtain ⟨a,ha,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
    refine ⟨(Representation.invariants σ).mkQ ⟨a,ha⟩,Subtype.ext ?_⟩
    change ρ.invariants.mkQ a = ρ.invariants.mkQ (a+z)
    rw [map_add,show ρ.invariants.mkQ z = 0 from
      (Submodule.Quotient.mk_eq_zero ρ.invariants).mpr hz,add_zero]
  refine ⟨MulEquiv.refl _,LinearEquiv.ofBijective fbar ⟨hi,hsurj⟩,?_⟩
  intro g v
  induction v using Submodule.Quotient.induction_on
  rfl

noncomputable def secondMovedFactorEquiv (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hm : f.space.toSubmodule = moved (secondAction c) ⊤) :
    ActionEquiv (reducedAction ((secondMoved c).toRepresentation.comp (second c).subtype))
      (((fixed (secondAction c)).quotientImage f.space).toRepresentation.comp
        (⊤ : Subgroup (second c)).subtype) := by
  let e := secondSubspaceQuotientEquiv c (secondMoved c) (second_moved_le_fixed c he)
    (second_supplement_of_moved_factor c he f hm)
  let p := actionSymm (factorQuotientEquiv c f)
  exact ⟨e.groupEquiv.trans p.groupEquiv,e.linearEquiv.trans p.linearEquiv,
    fun g v => (congrArg p.linearEquiv (e.intertwines g v)).trans (p.intertwines _ _)⟩

theorem linearTwo_secondCase (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (hm : f.space.toSubmodule = moved (secondAction c) ⊤) (F : BinaryField)
    (hn : IsLinearNatural (((fixed (secondAction c)).quotientImage f.space).toRepresentation.comp
      (⊤ : Subgroup (second c)).subtype) F 2) : HyperplaneSecondCase ρ (second c) (secondMoved c) := by
  obtain ⟨n⟩ := hn
  let e := secondMovedFactorEquiv c he f hm
  exact .linearTwo F ⟨⟨e.groupEquiv.trans n.groupEquiv,e.linearEquiv.trans n.linearEquiv,
    fun g v => (congrArg n.linearEquiv (e.intertwines g v)).trans (n.intertwines _ _)⟩⟩

end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
