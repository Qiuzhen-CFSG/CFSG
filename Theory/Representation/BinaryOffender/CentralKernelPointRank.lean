module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
public import Theory.Representation.BinaryOffender.PPerfectFixedLift
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Three-rank of point stabilizers through a central kernel

A central equivariant projection preserves the three-rank of every point
stabilizer. The two-residual of a quotient stabilizer has the same three-rank;
its displacement homomorphism into the binary central kernel is trivial, so
it fixes the prescribed original vector. No splitting of the module is needed.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
13.5.23, printed p.925.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open BinaryNaturalDual.VectorStabilizers
namespace Representation.BinaryOffender
variable {G V W : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- A central projection preserves the three-rank of each actual point stabilizer. -/
theorem primeRank_stabilizer_central_kernel
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (f : V →ₗ[ZMod 2] W) (hf : ∀ g v, f (ρ g v) = σ g (f v))
    (hk : f.ker ≤ fixedSpace ρ ⊤) (v : V) :
    primeRank 3 (representationStabilizer ρ v) =
      primeRank 3 (representationStabilizer σ (f v)) := by
  let C := representationStabilizer σ (f v)
  let R := (pResidual 2 C).map C.subtype
  have hRC : R ≤ C := map_subtype_le _
  have hR : R ≤ representationStabilizer ρ v := by
    have hv : v ∈ fixedSpace ρ R := fixed_of_pPerfect_central_kernel ρ R
      (isPPerfect_embedded_pResidual 2 C) f
      (by intro w hw r; exact hk hw ⟨r.val, mem_top _⟩) v (by
        intro r
        rw [hf]
        exact hRC r.property)
    intro r hr
    exact hv ⟨r,hr⟩
  have hrank : primeRank 3 R = primeRank 3 C := by
    rw [← primeRank_congr 3 ((pResidual 2 C).equivMapOfInjective C.subtype
      C.subtype_injective)]
    exact ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)
  apply le_antisymm
  · apply primeRank_mono
    intro g hg
    change σ g (f v) = f v
    rw [← hf, hg]
  · rw [← hrank]
    exact primeRank_mono 3 hR

end Representation.BinaryOffender
