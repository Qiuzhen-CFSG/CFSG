module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme.Models

/-!
# Lifting literal binary-block permutations to the syntheme model

A permutation of the six pairs `(i,b)` whose first coordinate is a prescribed
permutation of the three blocks has a unique expression in the existing
syntheme model. The translation bit at the target block `i` is the second
coordinate of the image of `(σ⁻¹ i,0)`. Injectivity on the two-point fibers
proves the affine formula; injectivity of the established model embedding
then makes pointwise lifts of an action into a homomorphism.

Both the six-point action and the three-block action are retained literally.
The source consumer is the branch-frame construction in Goldschmidt,
*Automorphisms of trivalent graphs* (1980), §6, for the M₁₂ amalgam.
The model itself is the three-block stabilizer used in Aschbacher–Smith I.5.7.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymmetricSix.SynthemeCalculation

theorem coordinateHom_injective : Function.Injective coordinateHom := by
  intro g h hh
  apply modelHom_injective
  exact congrArg (fun f => (Equiv.permCongrHom letterEquiv) f) hh

def blockModel (π : Equiv.Perm (Fin 3 × ZMod 2)) (σ : Three) : Model :=
  ⟨Multiplicative.ofAdd (fun i => (π (σ⁻¹ i, 0)).2), σ⟩

theorem blockModel_right (π : Equiv.Perm (Fin 3 × ZMod 2)) (σ : Three) :
    (blockModel π σ).right = σ := rfl

theorem coordinateHom_blockModel (π : Equiv.Perm (Fin 3 × ZMod 2)) (σ : Three)
    (hπ : ∀ i b, (π (i,b)).1 = σ i) : coordinateHom (blockModel π σ) = π := by
  apply Equiv.ext
  rintro ⟨i,b⟩
  apply Prod.ext
  · exact (hπ i b).symm
  · dsimp [blockModel, coordinateHom]
    have hb : (π (i,b)).2 = b + (π (i,0)).2 := by
      rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) b with rfl | rfl
      · simp
      · have hne : π (i,1) ≠ π (i,0) := by
          intro hh
          have := π.injective hh
          simp at this
        have hbits : (π (i,1)).2 ≠ (π (i,0)).2 := by
          intro hh
          apply hne
          apply Prod.ext
          · exact (hπ i 1).trans (hπ i 0).symm
          · exact hh
        have hval : (π (i,1)).2 = (π (i,0)).2 + 1 :=
          (show ∀ a b : ZMod 2, a ≠ b → a = b + 1 by decide) _ _ hbits
        simpa [add_comm] using hval
    simpa using hb.symm

theorem existsUnique_blockModel (π : Equiv.Perm (Fin 3 × ZMod 2)) (σ : Three)
    (hπ : ∀ i b, (π (i,b)).1 = σ i) :
    ∃! m : Model, coordinateHom m = π ∧ m.right = σ := by
  refine ⟨blockModel π σ, ⟨coordinateHom_blockModel π σ hπ, rfl⟩, ?_⟩
  intro m hm
  exact coordinateHom_injective (hm.1.trans (coordinateHom_blockModel π σ hπ).symm)

variable {G : Type*} [Group G]

def blockActionHom (ρ : G →* Equiv.Perm (Fin 3 × ZMod 2)) (β : G →* Three)
    (h : ∀ g i b, (ρ g (i,b)).1 = β g i) : G →* Model where
  toFun g := blockModel (ρ g) (β g)
  map_one' := by
    apply coordinateHom_injective
    rw [coordinateHom_blockModel _ _ (h 1), map_one, map_one]
  map_mul' g k := by
    apply coordinateHom_injective
    rw [coordinateHom_blockModel _ _ (h (g*k)), map_mul coordinateHom,
      coordinateHom_blockModel _ _ (h g), coordinateHom_blockModel _ _ (h k), map_mul]

theorem coordinateHom_blockActionHom (ρ : G →* Equiv.Perm (Fin 3 × ZMod 2))
    (β : G →* Three) (h : ∀ g i b, (ρ g (i,b)).1 = β g i) (g : G) :
    coordinateHom (blockActionHom ρ β h g) = ρ g := coordinateHom_blockModel _ _ (h g)

theorem blockActionHom_right (ρ : G →* Equiv.Perm (Fin 3 × ZMod 2))
    (β : G →* Three) (h : ∀ g i b, (ρ g (i,b)).1 = β g i) (g : G) :
    (blockActionHom ρ β h g).right = β g := rfl

theorem coordinateHom_comp_blockActionHom (ρ : G →* Equiv.Perm (Fin 3 × ZMod 2))
    (β : G →* Three) (h : ∀ g i b, (ρ g (i,b)).1 = β g i) :
    coordinateHom.comp (blockActionHom ρ β h) = ρ := by
  ext g : 1
  exact coordinateHom_blockActionHom ρ β h g

theorem rightHom_comp_blockActionHom (ρ : G →* Equiv.Perm (Fin 3 × ZMod 2))
    (β : G →* Three) (h : ∀ g i b, (ρ g (i,b)).1 = β g i) :
    (SemidirectProduct.rightHom : Model →* Three).comp (blockActionHom ρ β h) = β := by
  rfl

end Theory.SpecificGroups.SymmetricSix.SynthemeCalculation
