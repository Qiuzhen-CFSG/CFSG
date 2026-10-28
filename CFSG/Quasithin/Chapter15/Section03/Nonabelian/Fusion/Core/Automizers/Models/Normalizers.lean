module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models.Actions
public import Theory.GroupTheory.ElementarySixteenNineNormalizer

/-!
# The two concrete automizer normalizers at s = 1

The common actor and compatible coordinates in `LayerActions` make both
literal conjugation layers elementary abelian of order sixteen, and their
actual Y-images have order nine. The general elementary-sixteen normalizer
theorem therefore identifies each image with the embedded two-residual of
its full automorphism normalizer. The images here are those defined using
the ambient local overgroup M in `Automizers.Reduction`.

For an elementary binary group B, every group automorphism is linear over
F₂: scalar compatibility follows from additivity. `binaryAutEquiv` realizes
this canonical identification with GL(B), so these are the full normalizers
appearing in the source. The parent source assembly still supplies the
earlier action witnesses and the local core equality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.59, printed p.1150, using 15.3.53(1), 15.3.54(4), and s = 1.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
open Subgroup

namespace LayerActions
variable {G : Type*} [Group G] [Finite G] {I Y P V : Subgroup G}
variable {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
variable [(V.subgroupOf P).Normal] (d : LayerActions I Y P V hIP hIV)
include d

/-- The actual Y-automizer of V is the embedded two-residual of its full
automorphism normalizer. The tensor coordinates retain the common actor. -/
theorem lower_normalizer_residual (M : Subgroup G) (hYI : Y ≤ I) (hIM : I ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    IsNormalizerResidual (lowerImage M Y V hMV) := by
  let : IsElementaryAbelian 2 V := d.elementary_lower
  exact normalizer_residual_of_elementary_sixteen_nine d.card_lower
    (lowerImage M Y V hMV) (d.card_lower_image_overgroup M hYI hIM hMV)

/-- The actual Y-automizer of P/V is the embedded two-residual of its full
automorphism normalizer, with the same actor as on V and the literal quotient. -/
theorem upper_normalizer_residual (M : Subgroup G) (hYI : Y ≤ I) (hIM : I ≤ M)
    (hMP : M ≤ normalizer (P : Set G)) (hMV : M ≤ normalizer (V : Set G)) :
    IsNormalizerResidual (upperImage M Y P V hMP hMV) := by
  let : IsElementaryAbelian 2 (P ⧸ V.subgroupOf P) := d.elementary_upper
  exact normalizer_residual_of_elementary_sixteen_nine d.card_upper
    (upperImage M Y P V hMP hMV) (d.card_upper_image_overgroup M hYI hIM hMP hMV)

end LayerActions
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
