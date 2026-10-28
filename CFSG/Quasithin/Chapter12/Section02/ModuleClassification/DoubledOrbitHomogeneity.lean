module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.Representation.Quotient
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedEquivalence
public import Theory.Representation.BinaryOffender.SmallMovedProducts

/-!
# Selecting the nonhomogeneous row on a doubled source module

Two different irreducible constituents cannot occur in a homogeneous module:
a nonzero coordinate projection would identify each with the common simple
constituent. If their product has no fixed vectors, both constituents are
fully moved. The literal B.5.1 moved quotient is therefore the whole module,
and clause (3) selects the natural-plus-dual action in degree four or five.
The component projection is kept throughout the argument.

DoubledOrbitRows applies this result to the actual offender subgroup of the
linear-normalizer supplement and then to the original Chapter 12 orbit.
Source: Aschbacher--Smith, B.5.1(3), printed p.99 / PDF110, used in 12.2.2,
printed p.795.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit
variable {P H U Z W : Type*} [Group P] [Group H]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup Z] [Module (ZMod 2) Z]
  [AddCommGroup W] [Module (ZMod 2) W]

private theorem moved_top_of_irreducible
    (α : Representation (ZMod 2) P U) [IsIrreducible α]
    (hz : α.invariants = ⊥) : moved α ⊤ = ⊤ := by
  let s := MovedSection.ofNormal α ⊤
  rcases eq_bot_or_eq_top s.space with hb | ht
  · have hm : moved α ⊤ = ⊥ := s.space_eq.symm.trans
      (congrArg Subrepresentation.toSubmodule hb)
    have hall : ∀ u : U, u = 0 := by
      intro u
      apply hz.le
      intro g
      apply sub_eq_zero.mp
      have hg : α g u - u ∈ moved α ⊤ :=
        Submodule.subset_span ⟨g, Subgroup.mem_top g, u, Submodule.mem_top, rfl⟩
      exact hm.le hg
    let := Subrepresentation.irreducible_module_nontrivial α
    obtain ⟨x,hx⟩ := exists_ne (0 : U)
    exact (hx (hall x)).elim
  · exact s.space_eq.symm.trans (congrArg Subrepresentation.toSubmodule ht)

/-- Two noncentral irreducible summands fill the moved space for any actor
mapping onto their component action. -/
theorem moved_top_of_pair
    (ρ : Representation (ZMod 2) H W) (K : Subgroup H) (q : P →* K)
    (α : Representation (ZMod 2) P U) (β : Representation (ZMod 2) P Z)
    [IsIrreducible α] [IsIrreducible β]
    (hz : fixedSpace ρ K = ⊥) (e : W ≃ₗ[ZMod 2] (U × Z))
    (hq : Function.Surjective q)
    (he : ∀ g w, e (ρ (q g) w) = (α.prod β) g (e w)) :
    moved ρ K = ⊤ := by
  have hp : (α.prod β).invariants = ⊥ := by
    apply bot_unique
    intro v hv
    have hi : e.symm v ∈ fixedSpace ρ K := by
      intro k
      obtain ⟨g,rfl⟩ := hq k
      apply e.injective
      change e (ρ (q g) (e.symm v)) = e (e.symm v)
      rw [he, e.apply_symm_apply, hv g]
    have hi0 : e.symm v = 0 := hz.le hi
    simpa using congrArg e hi0
  have ha : α.invariants = ⊥ := by
    apply bot_unique
    intro u hu
    have hv : (u, (0 : Z)) ∈ (α.prod β).invariants := by
      intro g
      exact Prod.ext (hu g) ((β g).map_zero)
    exact congrArg Prod.fst (show (u, (0 : Z)) = 0 from hp.le hv)
  have hb : β.invariants = ⊥ := by
    apply bot_unique
    intro z hz
    have hv : ((0 : U), z) ∈ (α.prod β).invariants := by
      intro g
      exact Prod.ext ((α g).map_zero) (hz g)
    exact congrArg Prod.snd (show ((0 : U), z) = 0 from hp.le hv)
  have hm : moved (α.prod β) ⊤ = ⊤ := by
    change subspaceCommutator (α.prod β) ⊤ ⊤ = ⊤
    rw [subspaceCommutator_prod]
    change (moved α ⊤).prod (moved β ⊤) = ⊤
    rw [moved_top_of_irreducible α ha, moved_top_of_irreducible β hb,
      Submodule.prod_top]
  have hle : moved (α.prod β) ⊤ ≤ (moved ρ K).comap e.symm.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    change e.symm ((α.prod β) g v - v) ∈ moved ρ K
    have hi : e.symm ((α.prod β) g v) = ρ (q g) (e.symm v) := by
      apply e.injective
      rw [e.apply_symm_apply, he, e.apply_symm_apply]
    rw [map_sub, hi]
    exact Submodule.subset_span ⟨q g, (q g).property, e.symm v, Submodule.mem_top, rfl⟩
  apply top_unique
  intro w _
  have hw := hle (hm.symm ▸ (Submodule.mem_top : e w ∈ (⊤ : Submodule (ZMod 2) (U × Z))))
  simpa only [Submodule.mem_comap, LinearEquiv.coe_coe, e.symm_apply_apply] using hw

private theorem equiv_of_repeated_embedding
    (α : Representation (ZMod 2) P U) (β : Representation (ZMod 2) P Z)
    [IsIrreducible α] [IsIrreducible β] {r : ℕ}
    (f : U →ₗ[ZMod 2] (Fin r → Z)) (hf : Function.Injective f)
    (he : ∀ g u, f (α g u) = repeated β r g (f u)) :
    Nonempty (α.Equiv β) := by
  let := Subrepresentation.irreducible_module_nontrivial α
  obtain ⟨u,hu⟩ := exists_ne (0 : U)
  have hfu : f u ≠ 0 := fun hz => hu (hf (hz.trans f.map_zero.symm))
  obtain ⟨i,hi⟩ : ∃ i : Fin r, f u i ≠ 0 := by
    by_contra! h
    exact hfu (funext h)
  let p : α.IntertwiningMap β :=
    ((LinearMap.proj i).comp f).intertwiningMap_of_isIntertwiningMap _ _
      (fun g u => congrFun (he g u) i)
  have hp : p ≠ 0 := fun hz => hi (DFunLike.congr_fun hz u)
  exact ⟨p.ofBijective ((IsIrreducible.bijective_or_eq_zero p).resolve_right hp)⟩

/-- A homogeneous component action cannot contain two different simple types,
including after pullback through the original component projection. -/
theorem not_homogeneous_of_pair
    (σ : Representation (ZMod 2) H W) (q : P →* H) (hq : Function.Surjective q)
    (α : Representation (ZMod 2) P U) (β : Representation (ZMod 2) P Z)
    [IsIrreducible α] [IsIrreducible β]
    (hne : ¬ Nonempty (α.Equiv β)) (e : W ≃ₗ[ZMod 2] (U × Z))
    (he : ∀ g w, e (σ (q g) w) = (α.prod β) g (e w)) :
    ¬ IsHomogeneousAction σ := by
  rintro ⟨r,_,N,hN,f,hf⟩
  let τ := N.toRepresentation.comp q
  let : IsIrreducible τ := (irreducible_comp_surjective_iff q hq _).mpr hN
  let a := f.toLinearMap.comp (e.symm.toLinearMap.comp (LinearMap.inl _ _ _))
  let b := f.toLinearMap.comp (e.symm.toLinearMap.comp (LinearMap.inr _ _ _))
  have ha : Function.Injective a := f.injective.comp (e.symm.injective.comp
    (fun _ _ h => congrArg Prod.fst h))
  have hb : Function.Injective b := f.injective.comp (e.symm.injective.comp
    (fun _ _ h => congrArg Prod.snd h))
  have hi (g : P) (v : U × Z) :
      e.symm ((α.prod β) g v) = σ (q g) (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  have hai (g : P) (u : U) : a (α g u) = repeated τ r g (a u) := by
    have hi' := hi g (u,0)
    change e.symm (α g u, β g 0) = _ at hi'
    rw [map_zero] at hi'
    change f (e.symm (α g u,0)) = _
    rw [hi',hf]
    rfl
  have hbi (g : P) (z : Z) : b (β g z) = repeated τ r g (b z) := by
    have hi' := hi g (0,z)
    change e.symm (α g 0, β g z) = _ at hi'
    rw [map_zero] at hi'
    change f (e.symm (0,β g z)) = _
    rw [hi',hf]
    rfl
  obtain ⟨ea⟩ := equiv_of_repeated_embedding α τ a ha hai
  obtain ⟨eb⟩ := equiv_of_repeated_embedding β τ b hb hbi
  exact hne ⟨ea.trans eb.symm⟩
/-- B.5.1(3) selects its natural-plus-dual alternative on a faithful pair of
nonisomorphic noncentral simple constituents, without an ambient model premise. -/
theorem naturalDual_of_source_pair
    (ρ : Representation (ZMod 2) H W) (K : Subgroup H)
    (c : CFSG.Quasithin.ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ K)
    (q : P →* K) (hq : Function.Surjective q)
    (α : Representation (ZMod 2) P U) (β : Representation (ZMod 2) P Z)
    [IsIrreducible α] [IsIrreducible β]
    (hne : ¬ Nonempty (α.Equiv β)) (hz : fixedSpace ρ K = ⊥)
    (e : W ≃ₗ[ZMod 2] (U × Z))
    (he : ∀ g w, e (ρ (q g) w) = (α.prod β) g (e w)) :
    ∃ n, (n = 4 ∨ n = 5) ∧ IsNaturalPlusDual (ρ.comp K.subtype) n := by
  have hm := moved_top_of_pair ρ K q α β hz e hq he
  let s := c.sectionData
  rcases c.clause_three with hh | ⟨n,hn,⟨a⟩⟩
  · let f := s.fullProjectionEquiv hm hz
    have hi (g : P) (v : s.space.toSubmodule ⧸ s.central.toSubmodule) :
        f.symm ((MovedSection.action ρ s) (q g) v) = ρ (q g) (f.symm v) := by
      apply f.injective
      change _ = s.fullProjection hm (ρ (q g) (f.symm v))
      rw [s.fullProjection_intertwines]
      exact f.apply_symm_apply _ |>.trans
        (congrArg ((MovedSection.action ρ s) (q g)) (f.apply_symm_apply v)).symm
    exact (not_homogeneous_of_pair ((MovedSection.action ρ s).comp K.subtype) q hq α β hne
      (f.symm.trans e) (fun g v => by
        change e (f.symm ((MovedSection.action ρ s) (q g) v)) = _
        rw [hi,he]
        rfl) hh).elim
  · have hs : s.space.toSubmodule = ⊤ := s.space_eq.trans hm
    let f : s.space.toSubmodule ≃ₗ[ZMod 2] W :=
      LinearEquiv.ofBijective s.space.toSubmodule.subtype
        ⟨Subtype.val_injective,fun w => ⟨⟨w,hs ▸ Submodule.mem_top⟩,rfl⟩⟩
    refine ⟨n,hn,⟨⟨a.groupEquiv, f.symm.trans a.linearEquiv, ?_⟩⟩⟩
    intro g w
    have hi : f.symm (ρ g w) = s.space.toRepresentation g (f.symm w) := by
      apply f.injective
      exact (f.apply_symm_apply _).trans (congrArg (ρ g) (f.apply_symm_apply w)).symm
    change a.linearEquiv (f.symm (ρ g w)) = _
    rw [hi]
    exact a.intertwines g (f.symm w)
end CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit
