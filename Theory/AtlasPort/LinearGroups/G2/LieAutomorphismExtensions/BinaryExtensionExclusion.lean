module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# No further extension of the full binary G₂ amalgam

The proved identification G₂(2) ≃ Aut(G₂(2)′) uses the actual conjugation
map. Restricting any automorphism of full G₂(2) to its characteristic derived
subgroup, and using faithful conjugation there, shows that it is inner.
Thus full G₂(2) is complete. More directly, any faithful action on the derived
subgroup extending this full-group action already has the full group as its
image. With the source intersection convention this also fixes both marked
parabolics and their whole overlap.

The derived group of order 6048 is not identified with the full group of order
12096. The imported `binaryAut_preserves_marked_types` establishes trivial
Dynkin action in the inherited G₂ marking, with one common derived-group
conjugation for both types. It uses neither a different U₃(3) diagram marking
nor an assumption that automorphisms extend from an abstract amalgam.

Source: Aschbacher--Smith, F.1.12, printed pp.263--264, and Definition F.4.3,
printed p.274. These are consequences of the concrete automorphism theorem;
the source's larger weak-BN-pair classification remains a separate assembly.
-/

@[expose] public section

namespace Atlas.G2.LieAutomorphismExtensions
open LieParabolicSetup

/-- Restricting an automorphism to the actual derived subgroup intertwines conjugation. -/
theorem binaryConjugation_naturality (a : MulAut (Model (ZMod 2)))
    (g : Model (ZMod 2)) :
    binaryConjugation (a g) = MulAut.characteristic BinaryDerived a *
      binaryConjugation g * (MulAut.characteristic BinaryDerived a)⁻¹ := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change a g * x.val * (a g)⁻¹ = a (g * a.symm x.val * g⁻¹)
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]

/-- Every automorphism of full G₂(2) is inner, using its faithful action on G₂(2)′. -/
theorem binaryFullConjugation_surjective :
    Function.Surjective (MulAut.conj : Model (ZMod 2) →* MulAut (Model (ZMod 2))) := by
  intro a
  obtain ⟨g, hg⟩ := binaryConjugation_surjective (MulAut.characteristic BinaryDerived a)
  refine ⟨g, ?_⟩
  apply MulEquiv.ext
  intro x
  apply binaryConjugation_injective
  rw [binaryConjugation_naturality a, ← hg]
  change binaryConjugation (g * x * g⁻¹) = _
  rw [map_mul, map_mul, map_inv]

/-- Full G₂(2) is complete: its conjugation homomorphism is bijective. -/
theorem binaryFullConjugation_bijective :
    Function.Bijective (MulAut.conj : Model (ZMod 2) →* MulAut (Model (ZMod 2))) := by
  refine ⟨?_, binaryFullConjugation_surjective⟩
  intro g h he
  apply binaryConjugation_injective
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  exact MulEquiv.congr_fun he x.val

/-- An automorphism extension of full G₂(2) containing all inner automorphisms
is already full G₂(2), via conjugation. -/
theorem binaryFull_no_proper_automorphism_extension
    (M : Subgroup (MulAut (Model (ZMod 2))))
    (hM : ∀ g : Model (ZMod 2), MulAut.conj g ∈ M) : M = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨g, rfl⟩ := binaryFullConjugation_surjective a
  exact hM g

/-- A faithful extension acting on the actual derived subgroup cannot properly
contain full G₂(2). The compatibility equation fixes the original conjugation embedding. -/
theorem binaryExtension_embedding_bijective {E : Type*} [Group E]
    (j : Model (ZMod 2) →* E) (a : E →* MulAut BinaryDerived)
    (ha : Function.Injective a) (haj : a.comp j = binaryConjugation) :
    Function.Bijective j := by
  constructor
  · intro g h he
    apply binaryConjugation_injective
    rw [← haj]
    exact congrArg a he
  · intro e
    obtain ⟨g, hg⟩ := binaryConjugation_surjective (a e)
    refine ⟨g, ha ?_⟩
    exact (DFunLike.congr_fun haj g).trans hg

/-- In an extension with the source intersection convention, both full marked
parabolics and their whole overlap are precisely the original images. -/
theorem binaryExtension_marked_eq {E : Type*} [Group E]
    (j : Model (ZMod 2) →* E) (a : E →* MulAut BinaryDerived)
    (ha : Function.Injective a) (haj : a.comp j = binaryConjugation)
    (P : Fin 2 → Subgroup E)
    (hP : ∀ i, (P i).comap j = if i = 0 then parabolic₁ else parabolic₂) :
    (∀ i, P i = (if i = 0 then parabolic₁ else parabolic₂).map j) ∧
      P 0 ⊓ P 1 = (parabolic₁ ⊓ parabolic₂).map j := by
  have hj := binaryExtension_embedding_bijective j a ha haj
  have h (i : Fin 2) : P i = (if i = 0 then parabolic₁ else parabolic₂).map j := by
    rw [← hP]
    ext e
    constructor
    · intro he
      obtain ⟨g, rfl⟩ := hj.2 e
      exact ⟨g, he, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg
  refine ⟨h, ?_⟩
  rw [h 0, h 1]
  simp only [↓reduceIte, show (1 : Fin 2) ≠ 0 by decide]
  exact (Subgroup.map_inf _ _ j hj.1).symm

end Atlas.G2.LieAutomorphismExtensions
