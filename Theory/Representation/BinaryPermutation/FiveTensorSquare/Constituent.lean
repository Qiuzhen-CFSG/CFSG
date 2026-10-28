module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Centralizer
public import Theory.Representation.BinaryPermutation.SevenPointChiefFactor
public import Theory.Representation.AbsolutelyIrreducible
/-!
# Absolute irreducibility of the deleted five-letter core

The elementary invariant-subspace proof gives irreducibility. The proved
scalar commutant then gives absolute irreducibility by Schur's criterion.
This supplies the actual constituent for the binary tensor factorization
in Aschbacher–Smith D.3.7, printed pp.197–199.
-/
public section
open Representation
namespace BinaryPermutation.FiveTensorSquare

theorem core_irreducible : δ.IsIrreducible := by
  let : Nontrivial C := Module.nontrivial_of_finrank_pos (by rw [finrank_core]; decide)
  rw [Representation.IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,fun S => ?_⟩
  rcases SevenPointChiefFactor.fiveCore_simple S.toSubmodule
    (fun g v hv => S.apply_mem_toSubmodule g hv) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

theorem core_absolute : δ.IsAbsolutelyIrreducible := by
  let := core_irreducible
  apply (isAbsolutelyIrreducible_iff_surjective δ).mpr
  intro f
  obtain ⟨c,hc⟩ := FiveTensorNormalizer.core_commuting_scalar f.toLinearMap
    (fun g v => Representation.IntertwiningMap.isIntertwining δ δ f g v)
  refine ⟨c,?_⟩
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  exact (hc v).symm
end BinaryPermutation.FiveTensorSquare
