module
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# Normalization of fixed subgroups from an action image

If the kernel of a homomorphism centralizes V, adjoining that kernel to J
does not change C_V(J). An image normalizing the image of J therefore
normalizes the same fixed subgroup. This retains literal quotient maps
and applies to the Thompson fixed subgroup in Aschbacher--Smith15.2.5.
-/
public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Group D]
theorem normalizes_fixed_of_image_normalizes (f : G →* D) (V J X : Subgroup G)
    (hXV : X ≤ normalizer (V : Set G))
    (hker : f.ker ≤ centralizer (V : Set G))
    (hn : X.map f ≤ normalizer (J.map f : Set D)) :
    X ≤ normalizer (V ⊓ centralizer (J : Set G) : Subgroup G) := by
  have hXN : X ≤ normalizer ((J.map f).comap f : Set G) :=
    (map_le_iff_le_comap.mp hn).trans (le_normalizer_comap f)
  have he : V ⊓ centralizer (J ⊔ f.ker : Subgroup G) =
      V ⊓ centralizer (J : Set G) := by
    apply le_antisymm (inf_le_inf_left _ (centralizer_le (show J ≤ J ⊔ f.ker from le_sup_left)))
    apply le_inf inf_le_left
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (hker.trans (centralizer_le (show V ⊓ centralizer (J : Set G) ≤ V from inf_le_left)))
  rw [comap_map_eq] at hXN
  rw [← he]
  exact (le_inf hXV (hXN.trans (normalizer_le_normalizer_centralizer _))).trans
    inf_normalizer_le_normalizer_inf
end Subgroup
