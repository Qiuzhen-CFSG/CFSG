module
public import Theory.Representation.BinaryConjugationSection.CoordinateEmbedding
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan

/-!
# Compatible embeddings in a marked quotient action

Inclusions of literal binary sections descend to injective intertwiners for
specified quotient factors. Only the subgroup mapping onto the factor needs
to have that factor's action; the larger actor of the smaller section may
have other quotient coordinates. Conjugate generation by a one-dimensional
seed then proves cyclicity in the same coordinates.

This supplies the compatible seed embeddings for Aschbacher--Smith,
The Classification of Quasithin Groups, 13.8.29(3), printed p.964.
-/

public section
open Subgroup Representation
namespace Representation.BinaryConjugationSection
variable {G K I U W : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
  {H P R S A Z : Subgroup G}
  {ρ : Representation (ZMod 2) I W} {σ : Representation (ZMod 2) K U}

/-- Descend the inclusion of literal sections along a specified quotient factor. -/
theorem exists_factor_embedding
    (π : H →* I) (κ : P →* K) (ι : K →* I)
    (c : BinaryConjugationSection H S Z (ρ.comp π))
    (d : BinaryConjugationSection P A Z (σ.comp κ))
    (hPH : P ≤ H) (hAS : A ≤ S) (hRP : R ≤ P)
    (hκ : Function.Surjective (κ.comp (inclusion hRP)))
    (hπ : ∀ r : R, π (inclusion (hRP.trans hPH) r) = ι (κ (inclusion hRP r))) :
    ∃ f : σ.IntertwiningMap (ρ.comp ι),
      Function.Injective f ∧ f.range.toSubmodule = c.imageSpace A ∧
      ∀ a : A, f (d.coordinates a).toAdd =
        (c.coordinates (inclusion hAS a)).toAdd := by
  obtain ⟨e,hi,hcoord,hact,hrange⟩ := c.exists_coordinate_embedding d hPH hAS
  have he (k : K) (u : U) : e (σ k u) = ρ (ι k) (e u) := by
    obtain ⟨r,rfl⟩ := hκ k
    have hh := hact (inclusion hRP r) u
    change ρ (π (inclusion (hRP.trans hPH) r)) (e u) =
      e (σ (κ (inclusion hRP r)) u) at hh
    rw [hπ] at hh
    exact hh.symm
  let f : σ.IntertwiningMap (ρ.comp ι) :=
    ⟨e, fun k => LinearMap.ext (he k)⟩
  exact ⟨f,hi,hrange,hcoord⟩

/-- Conjugate generation by a one-dimensional seed supplies cyclicity in
any specified factor coordinates. -/
theorem cyclic_of_seed_span
    (κ : P →* K) (d : BinaryConjugationSection P A Z (σ.comp κ))
    (R B : Subgroup G) (hRP : R ≤ P) (hgen : A = conjugateSpanBy B R)
    (u : U) (hseed : d.imageSpace B = Submodule.span (ZMod 2) {u}) :
    Submodule.span (ZMod 2) (Set.range fun k => σ k u) = ⊤ := by
  let M := Submodule.span (ZMod 2) (Set.range fun k => σ k u)
  have hm (p : P) : M ≤ M.comap (σ (κ p)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    change σ (κ p) (σ k u) ∈ M
    exact Submodule.subset_span ⟨κ p * k, by change σ (κ p * k) u = _; rw [map_mul]; rfl⟩
  let m : Subrepresentation (σ.comp κ) :=
    { toSubmodule := M, apply_mem_toSubmodule := hm }
  have hBP : B ≤ A := hgen ▸ le_conjugateSpanBy _ _
  have hgenP : A = conjugateSpanBy B P := le_antisymm
    (hgen ▸ conjugateSpanBy_mono le_rfl hRP)
    (conjugateSpanBy_le hBP d.normalized)
  apply d.generated_image_le B hgenP m
  rw [hseed]
  apply Submodule.span_le.mpr
  rintro _ rfl
  exact Submodule.subset_span ⟨1,by simp⟩
end Representation.BinaryConjugationSection
