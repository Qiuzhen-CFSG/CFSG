module

public import Theory.GroupTheory.PResidual.FrattiniGeneration
public import Theory.GroupTheory.PResidual.NormalizedSupplement

/-!
# Residual generation through a normalized prime kernel

An image covering the ambient p-residual lifts to containment when the
kernel on that residual lies in a p-subgroup normalizing the source.
Taking residuals first restricts the kernel to the actual residual; no
condition on the entire homomorphism kernel is needed.

Source: the residual lifting argument of Aschbacher--Smith G.2.3,
printed p.333, as used after12.7.18 on printed p.845.
-/

public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- Absorb only the actual residual kernel, retaining the supplied map. -/
theorem pResidual_le_of_normalized_image_cover {p : ℕ} [Fact p.Prime]
    (f : G →* H) (I Q : Subgroup G) (hQ : IsPGroup p Q)
    (hn : Q ≤ normalizer (I : Set G))
    (hk : pResidual p G ⊓ f.ker ≤ Q)
    (hi : (pResidual p G).map f ≤ I.map f) : pResidual p G ≤ I := by
  have he := pResidual_eq_embedded_sup_kernel_of_map_le p I f hi
  have hcover : pResidual p G ≤ I ⊔ Q :=
    he.le.trans (sup_le_sup (map_subtype_le _) hk)
  exact le_of_isPPerfect_of_le_sup_of_normalizes (pResidual p G) I Q
    (isPPerfect_pResidual p) hQ hn hcover

end Subgroup
