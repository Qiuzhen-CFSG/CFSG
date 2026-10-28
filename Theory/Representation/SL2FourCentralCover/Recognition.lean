module

public import Theory.Representation.SL2FourCentralCover
public import Theory.Representation.FirstCohomologyDuality.SimpleCover

/-!
# Recognition of natural SL₂(4) covers

Transitivity on the fifteen nonzero natural vectors proves simplicity of
the quotient. A commutator-generated extension with fixed kernel is therefore
indecomposable. In dimension six the universal-cover surjection is an
equivalence, retaining its original projection onto the natural module.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.73(3), printed pp.1076–1077. These implications do not infer
commutator generation from dimension or assume indecomposability.
-/

public section
noncomputable section
open Representation Representation.OneCohomology

namespace Representation.SL2FourCentralCover
open SL2FourNatural
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) SL W}

/-- A cover of the marked binary natural module is indecomposable. -/
theorem indecomposable_of_natural_cover
    (p : σ.IntertwiningMap naturalRepresentation) (hp : IsCover p)
    (A B : Submodule (ZMod 2) W)
    (hA : ∀ g v, v ∈ A → σ g v ∈ A)
    (hB : ∀ g v, v ∈ B → σ g v ∈ B)
    (hAB : IsCompl A B) : A = ⊥ ∨ B = ⊥ := by
  apply indecomposable_of_cover_of_simple p hp ?_ A B hA hB hAB
  intro X hX
  by_cases hx : X = ⊥
  · exact Or.inl hx
  right
  obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · simpa only [hw] using X.zero_mem
  obtain ⟨g, hg⟩ := transitive_nonzero v w hne hw
  exact hg ▸ hX g v hv

/-- Six-dimensional covers are the universal cover, with the same natural projection. -/
theorem exists_equiv_of_six_dimensional_cover [FiniteDimensional (ZMod 2) W]
    (p : σ.IntertwiningMap naturalRepresentation) (hp : IsCover p)
    (hdim : Module.finrank (ZMod 2) W = 6) :
    ∃ e : binaryAction.Equiv σ, ∀ w, p (e w) = projection w := by
  obtain ⟨q, hq, he⟩ := exists_quotient p hp
  have hi : Function.Injective q :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (binary_finrank.trans hdim.symm)).mpr hq
  let e := LinearEquiv.ofBijective q.toLinearMap ⟨hi, hq⟩
  exact ⟨Representation.Equiv.mk e q.isIntertwining', he⟩

end Representation.SL2FourCentralCover
