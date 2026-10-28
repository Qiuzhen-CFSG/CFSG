module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer.Isometries

/-!
# The normalizer of the actual natural A₆ image

The invariant bilinear form is unique up to a binary scalar, so every
normalizing operator preserves the nondegenerate coordinate pairing.
Its isometries are precisely the symmetric natural image, as established
using an explicit symplectic basis and the order of Sp₄(2). The reverse
containment follows from normality of A₆ in S₆.

This is the intrinsic normalizer calculation for the faithful extension
argument in Aschbacher–Smith 13.8.26–27, printed pp.962–963, using the natural
module of §B.3, printed pp.83–85. Both embeddings are the original actions
on the augmentation quotient; no outer-action identification is assumed.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix

/-- The full linear normalizer of the literal natural A₆ image is its natural S₆ overgroup. -/
theorem normalizer_alternatingImage :
    Subgroup.normalizer (alternatingImage : Set LinearGroup) = symmetricImage := by
  apply le_antisymm
  · intro u hu
    exact isometry_mem_symmetricImage u (normalizer_preserves_pairing u hu)
  · exact symmetricImage_le_normalizer

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
