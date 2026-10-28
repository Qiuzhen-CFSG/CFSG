module
public import CFSG.Quasithin.ChapterE.Section04.Basic

/-!
# Bounding the fixed-space parameter on an invariant submodule

An injective equivariant map identifies fixed vectors in the smaller module
with the fixed vectors in its image. Equality of fixed spaces in the whole
module therefore implies equality in the smaller module. This transports
an upper bound from a faithful moved submodule to the whole module, as used
in Aschbacher–Smith 12.4.1, printed p.812.
-/
public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- Fixed-space equalities restrict to any equivariantly embedded submodule. -/
theorem fixedSpaceFamily_of_equivariant_embedding
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (f : W →ₗ[ZMod 2] V) (hf : Function.Injective f)
    (he : ∀ g w, f (σ g w) = ρ g (f w))
    {k : ℕ} {A : Subgroup G} (hA : A ∈ fixedSpaceFamily ρ k) :
    A ∈ fixedSpaceFamily σ k := by
  refine ⟨hA.1,hA.2.1,?_⟩
  intro B hBA hB
  apply le_antisymm (fixedSpace_antitone σ hBA)
  intro w hw a
  apply hf
  change f (σ (a : G) w) = f w
  rw [he]
  have hw' : f w ∈ fixedSpace ρ B := by
    intro b
    change ρ (b : G) (f w) = f w
    exact (he b w).symm.trans (congrArg f (hw b))
  have hwA : f w ∈ fixedSpace ρ A := (hA.2.2 B hBA hB).symm ▸ hw'
  exact hwA a

/-- A bound on an invariant submodule bounds the parameter of the whole module. -/
theorem moduleA_le_of_equivariant_embedding
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (f : W →ₗ[ZMod 2] V) (hf : Function.Injective f)
    (he : ∀ g w, f (σ g w) = ρ g (f w)) : moduleA ρ ≤ moduleA σ := by
  apply iSup_le
  intro k
  apply iSup_le
  rintro ⟨A,hA⟩
  exact le_moduleA_of_mem σ (fixedSpaceFamily_of_equivariant_embedding ρ σ f hf he hA)
end CFSG.Quasithin.ChapterE
