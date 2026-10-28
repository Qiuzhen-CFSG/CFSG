module
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.QuadraticImageBound

/-!
# Quadratic ratios under equivariant action embeddings

An injective change of actors and an equivariant linear equivalence preserve
quadratic elementary actors and their ratios. For an arbitrary actor map into
a faithful action, the map factors injectively through the literal action image.
Thus restricting the faithful actor cannot decrease the global quadratic ratio.

This supplies the conjugate-generator comparison in Aschbacher–Smith D.1.3(b),
printed pp.173–174, without a numerical comparison hypothesis.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)

theorem quadratic_map_equivariant (f : G →* D)
    (E : V ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    {A : Subgroup G} (hA : IsQuadratic ρ A) : IsQuadratic σ (A.map f) := by
  rintro a ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩ w
  obtain ⟨v,rfl⟩ := E.surjective w
  have h := congrArg E (hA a ha b hb v)
  simpa only [hE, map_sub] using h

theorem quadraticRatio_le_of_injective_equivariant (f : G →* D)
    (hf : Function.Injective f) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v)) :
    quadraticRatio σ ≤ quadraticRatio ρ := by
  refine le_iInf fun A => le_iInf fun hA => ?_
  let : IsElementaryAbelian 2 A := hA.1.2
  have ha : IsElementaryTwo (A.map f) := by
    refine ⟨?_, IsElementaryAbelian.map f⟩
    intro hb
    exact hA.1.1 (Subgroup.map_injective hf (by simpa only [Subgroup.map_bot] using hb))
  have h : quadraticRatio σ ≤ actionRatio σ (A.map f) := iInf_le_of_le (A.map f) (iInf_le_of_le
    ⟨ha, quadratic_map_equivariant ρ σ f E hE hA.2⟩ le_rfl)
  apply h.trans
  rw [actionRatio, actionRatio, ← fixedCodim_map_equivariant ρ σ f E hE,
    rank_map_injective f hf]

theorem quadraticRatio_le_image_of_equivariant
    (f : G →* D) (hσ : Function.Injective σ)
    (E : V ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (ρ g v) = σ (f g) (E v)) :
    quadraticRatio σ ≤ quadraticRatio (imageRepresentation ρ) := by
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hk : q.ker ≤ f.ker := by
    intro g hg
    apply hσ
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    have hg' : ρ g = 1 := by
      have hh : g ∈ (actionHom ρ).ker := hg
      rw [actionHom_ker_eq] at hh
      exact hh
    simpa only [map_one, Module.End.one_apply, hg'] using (hE g v).symm
  let ψ := q.liftOfSurjective hq ⟨f,hk⟩
  have hψ (g : G) : ψ (q g) = f g := q.liftOfRightInverse_comp_apply _ _ _ g
  have heψ : ∀ a v, E (imageRepresentation ρ a v) = σ (ψ a) (E v) := by
    intro a v
    obtain ⟨g,rfl⟩ := hq a
    rw [hψ]
    exact hE g v
  have hi : Function.Injective ψ := by
    intro a b hab
    apply imageRepresentation_injective ρ
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [heψ,heψ,hab]
  exact quadraticRatio_le_of_injective_equivariant _ _ ψ hi E heψ
end Representation.BinaryOffender
