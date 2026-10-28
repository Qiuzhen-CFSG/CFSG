module
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.NormalElementaryQuotient

/-!
# Literal subgroup coordinates for a central cover

A linear change of coordinates preserves a central cover: surjectivity,
fixed kernel, and generation by commutators all transport through the
linear equivalence. For an embedded binary module this realizes the cover
on the additive group of its literal subgroup image, preserves conjugation,
and identifies the mapped linear kernel with the subgroup centralizer.

The graph-vertex cover in MS93 (3.2)(vi) is the motivating application.
-/

@[expose] public section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace Representation.OneCohomology
variable {A W V T G : Type*} [Group A] [Group G]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup T] [Module (ZMod 2) T]
  (ρ : Representation (ZMod 2) A W) (τ : Representation (ZMod 2) A T)

noncomputable def coordinateAction (e : W ≃ₗ[ZMod 2] V) :
    Representation (ZMod 2) A V := e.conjRingEquiv.toMonoidHom.comp ρ
noncomputable def coordinateProjection (p : ρ.IntertwiningMap τ) (e : W ≃ₗ[ZMod 2] V) :
    (coordinateAction ρ e).IntertwiningMap τ :=
  (p.toLinearMap.comp e.symm.toLinearMap).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g v
    change p (e.symm (e (ρ g (e.symm v)))) = τ g (p (e.symm v))
    rw [e.symm_apply_apply,p.isIntertwining])

theorem coordinateProjection_isCover (p : ρ.IntertwiningMap τ) (hp : IsCover p)
    (e : W ≃ₗ[ZMod 2] V) : IsCover (coordinateProjection ρ τ p e) := by
  refine ⟨hp.1.comp e.symm.surjective,?_,?_⟩
  · intro v hv g
    change e (ρ g (e.symm v)) = v
    exact (congrArg e (hp.2.1 hv g)).trans (e.apply_symm_apply v)
  · have hle : Coinvariants.ker ρ ≤
        (Coinvariants.ker (coordinateAction ρ e)).comap e.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,v⟩,rfl⟩
      change e (ρ g v-v) ∈ Coinvariants.ker (coordinateAction ρ e)
      have h := Coinvariants.sub_mem_ker (ρ := coordinateAction ρ e) g (e v)
      change e (ρ g (e.symm (e v))) - e v ∈ Coinvariants.ker (coordinateAction ρ e) at h
      rw [e.symm_apply_apply] at h
      simpa only [map_sub] using h
    apply top_unique
    intro v _
    have h := hle (hp.2.2 ▸ (show e.symm v ∈ (⊤ : Submodule (ZMod 2) W) from Submodule.mem_top))
    simpa only [Submodule.mem_comap,LinearEquiv.coe_coe,e.apply_symm_apply] using h

theorem exists_subgroup_cover
    (p : ρ.IntertwiningMap τ) (hp : IsCover p)
    (U L : Subgroup G) [IsElementaryAbelian 2 U]
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjU : j.range=U)
    (f : L →* A)
    (hact : ∀ (k : L) (v : W), j (Multiplicative.ofAdd (ρ (f k) v)) =
      (k:G)*j (Multiplicative.ofAdd v)*(k:G)⁻¹)
    (hker : ∀ v : W, p v=0 ↔ j (Multiplicative.ofAdd v) ∈ centralizer (L:Set G)) :
    ∃ σ : Representation (ZMod 2) A (Additive U),
      ∃ p' : σ.IntertwiningMap τ, IsCover p' ∧
        (∀ (k : L) (u : U), ((σ (f k) (Additive.ofMul u)).toMul : G) =
          (k:G)*u*(k:G)⁻¹) ∧
        p'.toLinearMap.ker.toAddSubgroup.toSubgroup'.map U.subtype = U ⊓ centralizer (L:Set G) := by
  let jU : Multiplicative W →* U := j.codRestrict U (fun v => hjU ▸ ⟨v,rfl⟩)
  have hjU' : Function.Bijective jU := by
    refine ⟨fun x y h => hj (congrArg Subtype.val h),?_⟩
    intro u
    obtain ⟨v,hv⟩ := show (u:G) ∈ j.range from hjU.symm ▸ u.property
    exact ⟨v,Subtype.ext hv⟩
  let b : W →+ Additive U := AddMonoidHom.toMultiplicativeLeft.symm jU
  let E : W ≃ₗ[ZMod 2] Additive U := LinearEquiv.ofBijective (b.toZModLinearMap 2) hjU'
  have hE (v : W) : ((E v).toMul : G) = j (Multiplicative.ofAdd v) := rfl
  refine ⟨coordinateAction ρ E,coordinateProjection ρ τ p E,
    coordinateProjection_isCover ρ τ p hp E,?_,?_⟩
  · intro k u
    change ((E (ρ (f k) (E.symm (Additive.ofMul u)))).toMul : G) = _
    rw [hE,hact,←hE,E.apply_symm_apply]
    rfl
  · ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      refine ⟨u.property,?_⟩
      change p (E.symm (Additive.ofMul u))=0 at hu
      have hh := (hker _).mp hu
      rwa [←hE,E.apply_symm_apply] at hh
    · rintro ⟨hU,hC⟩
      refine ⟨⟨x,hU⟩,?_,rfl⟩
      change p (E.symm (Additive.ofMul (⟨x,hU⟩:U)))=0
      apply (hker _).mpr
      rwa [←hE,E.apply_symm_apply]
end Representation.OneCohomology
