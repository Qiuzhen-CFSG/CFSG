module

public import Theory.Representation.BinaryPermutation.PointStabilizerRank
public import Theory.Representation.BinaryOffender.CentralKernelPointRank

/-!
# Point stabilizers in central covers of the natural A₈ module

The two independent cubics fixing every natural-module point also give
three-rank at least two in its actual stabilizer in any central binary cover.
The actor equivalence and the prescribed projection are retained literally.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),13.5.23,
printed p.925.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open BinaryNaturalDual.VectorStabilizers
namespace BinaryPermutation.PointStabilizerRank
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
/-- Every point of a central cover of the A₈ natural module has stabilizer three-rank at least two. -/
theorem two_le_central_cover_stabilizer
    (ρ : Representation (ZMod 2) G V) (e : G ≃* alternatingGroup (Fin 8))
    (f : V →ₗ[ZMod 2] natural (Fin 8))
    (hf : ∀ g v, f (ρ g v) = alternatingNaturalRepresentation (Fin 8) (e g) (f v))
    (hk : f.ker ≤ fixedSpace ρ ⊤) (v : V) :
    2 ≤ primeRank 3 (representationStabilizer ρ v) := by
  let σ := (alternatingNaturalRepresentation (Fin 8)).comp e.toMonoidHom
  rw [primeRank_stabilizer_central_kernel ρ σ f hf hk v]
  let q := BinaryNaturalDual.Transport.stabilizerEquiv σ
    (alternatingNaturalRepresentation (Fin 8)) e (LinearEquiv.refl (ZMod 2) _)
    (fun _ _ => rfl) (f v)
  rw [primeRank_equiv 3 q]
  exact two_le_natural_stabilizer (by simp) (f v)
end BinaryPermutation.PointStabilizerRank
