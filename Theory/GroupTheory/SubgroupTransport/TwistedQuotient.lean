module
public import Theory.GroupTheory.SylowTwistedGeneratingPair.Formula
public import Theory.GroupTheory.SubgroupTransport.Restriction
public import Theory.GroupTheory.PCoreSurjective

/-!
# Conjugacy twists through a marked quotient

The exact induced-automorphism formula makes partial twist images commute
with the original quotient map in the required direction. A two-group
kernel preserves the full two-core preimage, so escape after two twists
survives in the actual quotient with the same marked subgroup.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas 6.4--6.6,
pp.53--54. Used for the original-degree invariant-kernel reduction.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.SubgroupTransport
variable {G J : Type*} [Group G] [Group J]

/-- A compatible automorphism on the actual image transports every
conjugacy-twist image into the corresponding image downstairs. -/
theorem twisted_image_map_le (f : G →* J) (S : Subgroup G)
    (β : MulAut S) (γ : MulAut (S.map f))
    (hγ : ∀ x : S, γ (f.subgroupMap S x) = f.subgroupMap S (β x))
    (g : G) (A : Subgroup G) :
    (image (twistedConjugacy S β g) A).map f ≤
      image (twistedConjugacy (S.map f) γ (f g)) (A.map f) := by
  have he (x : S) :
      f (ambientHom (twistedConjugacy S β g) x) =
        ambientHom (twistedConjugacy (S.map f) γ (f g)) (f.subgroupMap S x) := by
    rw [twistedConjugacy_eq,twistedConjugacy_eq]
    change f (g * (β x : G) * g⁻¹) =
      f g * (γ (f.subgroupMap S x) : J) * (f g)⁻¹
    rw [hγ]
    exact (map_mul f _ _).trans (by rw [map_mul,map_inv]; rfl)
  rintro y ⟨z,⟨x,hx,rfl⟩,rfl⟩
  exact ⟨f.subgroupMap S x,mem_map_of_mem f hx,(he x).symm⟩

/-- Two-step escape survives a quotient with two-group kernel, for the
literal induced automorphism, original conjugator and marked subgroup. -/
theorem twice_twisted_escape_map [Finite G] [Finite J]
    (f : G →* J) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Subgroup G) (β : MulAut S) (γ : MulAut (S.map f))
    (hγ : ∀ x : S, γ (f.subgroupMap S x) = f.subgroupMap S (β x))
    (g : G) (Z : Subgroup G)
    (hescape : ¬ (image (twistedConjugacy S β g))^[2] Z ≤ pCore 2 G) :
    ¬ (image (twistedConjugacy (S.map f) γ (f g)))^[2] (Z.map f) ≤ pCore 2 J := by
  intro hbad
  apply hescape
  rw [←f.comap_pCore_of_ker_isPGroup hf hk]
  apply map_le_iff_le_comap.mp
  have h₁ := twisted_image_map_le f S β γ hγ g Z
  have h₂ := twisted_image_map_le f S β γ hγ g (image (twistedConjugacy S β g) Z)
  exact (h₂.trans (image_mono _ h₁)).trans hbad
end Theory.GroupTheory.SubgroupTransport
