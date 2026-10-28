module
public import Theory.Representation.BinaryOffender.NormalizerNonFF

/-!
# No strong offenders from a marked normal model

Coordinates for a normal marked subgroup embed a faithful ambient action in
its model's full linear normalizer. Fixed codimension and elementary rank
are unchanged by this embedding. Passing to the faithful action image first
allows arbitrary kernels in the original section.

This is the strong-offender form of the normalizer transport in
Aschbacher--Smith B.1.11--13, printed pp.72--73; its natural SL₂ application
supplies the chief-section costs in D.3.21(3), printed p.205.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryOffender
variable {H K P V W : Type*} [Group H] [Group K] [Group P]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- A marked normal model transfers the full-normalizer strong-offender exclusion. -/
theorem not_strong_of_marked_normal_range
    (ρ : Representation (ZMod 2) H V) (hρ : Function.Injective ρ)
    (i : K →* H) [i.range.Normal]
    (μ : Representation (ZMod 2) P W) (f : K →* P) (hf : Function.Surjective f)
    (b : Representation.Equiv (ρ.comp i) (μ.comp f))
    (hμ : ¬ IsStrongFFModule (normalizerRepresentation μ)) : ¬ IsStrongFFModule ρ := by
  let E := b.toLinearEquiv
  let γ : Representation (ZMod 2) H W := E.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : H) (v : V) : E (ρ g v) = γ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hres (k : K) : γ (i k) = μ (f k) := by
    ext w
    obtain ⟨v,rfl⟩ := E.surjective w
    rw [← he]
    exact Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap k v
  have himage : i.range.map γ.asGroupHom = actionImage μ := by
    ext z
    constructor
    · rintro ⟨_,⟨k,rfl⟩,rfl⟩
      exact ⟨f k,Units.ext (hres k).symm⟩
    · rintro ⟨p,rfl⟩
      obtain ⟨k,rfl⟩ := hf p
      exact ⟨i k,⟨k,rfl⟩,Units.ext (hres k)⟩
  have hn (g : H) : γ.asGroupHom g ∈ linearNormalizer μ := by
    change γ.asGroupHom g ∈ normalizer (actionImage μ : Set _)
    rw [← himage]
    exact i.range.le_normalizer_map γ.asGroupHom
      (mem_map_of_mem _ (show g ∈ normalizer (i.range : Set H) from
        le_normalizer_of_normal (mem_top g)))
  let j : H →* linearNormalizer μ := γ.asGroupHom.codRestrict _ hn
  have hj : Function.Injective j := by
    intro x y hxy
    exact hγ (congrArg (fun z : linearNormalizer μ => z.val.val) hxy)
  rintro ⟨A,hA,hs⟩
  apply hμ
  refine ⟨A.map j,(IsOffender.map_equivariant ρ (normalizerRepresentation μ)
    j hj E he ⟨hA,hs.le⟩).1,?_⟩
  rw [←fixedCodim_map_equivariant ρ (normalizerRepresentation μ) j E he,
    rank_map_injective j hj]
  exact hs

/-- The same exclusion holds on the faithful image of a possibly unfaithful section. -/
theorem image_not_strong_of_marked_normal_range
    (ρ : Representation (ZMod 2) H V) (i : K →* H) [i.range.Normal]
    (μ : Representation (ZMod 2) P W) (f : K →* P) (hf : Function.Surjective f)
    (b : Representation.Equiv (ρ.comp i) (μ.comp f))
    (hμ : ¬ IsStrongFFModule (normalizerRepresentation μ)) :
    ¬ IsStrongFFModule (imageRepresentation ρ) := by
  let j : K →* actionImage ρ := (actionHom ρ).comp i
  have hj : j.range = i.range.map (actionHom ρ) := MonoidHom.range_comp _ _
  let : j.range.Normal := by
    rw [hj]
    exact Subgroup.Normal.map inferInstance (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective
  let b' : Representation.Equiv ((imageRepresentation ρ).comp j) (μ.comp f) :=
    { __ := b.toLinearEquiv
      isIntertwining' k := by
        ext v
        exact Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap k v }
  exact not_strong_of_marked_normal_range (imageRepresentation ρ)
    (imageRepresentation_injective ρ) j μ f hf b' hμ
end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G K V W : Type*} [Group G] [Group K]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
/-- A faithful action on a normal quotient detects the actor on every faithful model section. -/
theorem faithful_actor_of_marked_normal_action
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
    (μ : Representation (ZMod 2) K W) (hμ : Function.Injective μ)
    (q : N →* K) (hq : Function.Surjective q) (α : G →* MulAut K)
    (hα : ∀ (a : G) (k : N), q (MulAut.conjNormal a k) = α a (q k))
    (b : Representation.Equiv (ρ.comp N.subtype) (μ.comp q))
    (A : Subgroup G) (hf : Function.Injective (α.comp A.subtype)) :
    ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1 := by
  intro a ha hv
  have hr : ρ a = 1 := by ext v; exact hv v
  have hrinv : ρ a⁻¹ = 1 := by
    have hh := ρ.map_mul a a⁻¹
    rw [mul_inv_cancel,map_one,hr,one_mul] at hh
    exact hh.symm
  have he (k : N) : μ (q (MulAut.conjNormal a k)) =
      μ (q k) := by
    have hc : ρ ((MulAut.conjNormal a k : N) : G) = ρ (k : G) := by
      change ρ (a * (k : G) * a⁻¹) = _
      simp only [map_mul,hr,hrinv,one_mul,mul_one]
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := b.toLinearEquiv.surjective v
    have hl := LinearMap.congr_fun (b.isIntertwining' (MulAut.conjNormal a k)) w
    have hk := LinearMap.congr_fun (b.isIntertwining' k) w
    exact hl.symm.trans ((congrArg b.toLinearEquiv (LinearMap.congr_fun hc w)).trans hk)
  have hαa : α a = 1 := by
    apply DFunLike.ext
    intro g
    obtain ⟨k,rfl⟩ := hq g
    exact (hα a k).symm.trans (hμ (he k))
  have haa := hf (show (α.comp A.subtype) ⟨a,ha⟩ = (α.comp A.subtype) 1 from
    hαa.trans (map_one _).symm)
  exact congrArg (fun z : A => (z : G)) haa
end Representation.BinaryOffender

