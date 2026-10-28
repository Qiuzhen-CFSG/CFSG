module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Scalar
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.Kernel

/-!
# The two inputs to the long-frame construction

`LocalEmbedding` asks only for the actual SL₃(4)-with-graph local subgroup
inside the literal tetrahedral centralizer. No representation comparison or
coordinates are part of this input, and no inhabitant is asserted.

The proved scalar-field action restricts to any such embedding. Its kernel
has exponent dividing four, by the already proved Leech kernel calculation.
Thus the module-identification branch can work independently with this exact
input; the long-frame owner must still construct the embedding and discharge
that hypothesis in the final assembly.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284:
construction of K₁ followed by its natural-plus-dual module identification.
-/

open Atlas.Conway Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
open OctonionLocals
@[expose] public noncomputable section

/-- The actual local subgroup, without any coordinate or action-classification
premise. Its domain retains the prescribed octonion SL₃ and graph conventions. -/
structure LocalEmbedding where
  hom : longLocal (F := F) →* LeechCentralQuotient
  injective : Function.Injective hom
  mem_centralizer : ∀ k, hom k ∈ centralizerI

/-- Restrict the genuine GF(4) action to the embedded local subgroup. -/
def LocalEmbedding.action (E : LocalEmbedding) :
    longLocal (F := F) →* (fixedSpace ≃ₗ[F] fixedSpace) :=
  centralizerAction.comp (E.hom.codRestrict centralizerI E.mem_centralizer)

@[simp] theorem LocalEmbedding.action_apply (E : LocalEmbedding)
    (k : longLocal (F := F)) (v : fixedSpace) :
    (E.action k v).val = quotientModTwoRepresentation (E.hom k) v.val := rfl

/-- This kernel bound uses the actual Leech action. It does not assume the
still separate faithfulness theorem for the full tetrahedral centralizer. -/
theorem LocalEmbedding.action_kernel_pow_four (E : LocalEmbedding)
    (k : longLocal (F := F)) (hk : E.action k = 1) : k ^ 4 = 1 := by
  apply E.injective
  rw [map_pow, map_one]
  apply kernel_pow_four (E.mem_centralizer k)
  intro v hv
  have he := congrArg (fun f : fixedSpace ≃ₗ[F] fixedSpace => (f ⟨v, hv⟩).val) hk
  exact he

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
