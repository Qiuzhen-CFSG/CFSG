module

public import Stellmacher.Recognition.PSU3ThreeEmbedding

/-!
# Excluding PSU₃(3) from minimal simple groups

The concrete PSU₃(3) contains a proper nonsolvable copy of SL₃(2). The
imported construction embeds its binary matrices through a faithful unitary
representation over the field of nine elements. An explicit unitary matrix
outside the image proves properness. Normalizing the prime-power parameters
in `ABG.IsPSU3` and transporting along its actual group equivalence therefore
excludes this recognition alternative for every minimal simple group.

Source: the subgroup construction in `PSU3ThreeEmbedding` and the defining
proper-subgroup condition of minimal simplicity; roadmap milestone M5.
-/

namespace Stellmacher.Recognition

/-- A minimal simple group cannot be an actual PSU₃(3) model. -/
public theorem not_isPSU3_three_of_isMinimalSimple
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimple G) :
    ¬ ABG.IsPSU3 G 3 :=
  fun hmodel => not_isMinimalSimple_of_isPSU3_three hmodel hG

end Stellmacher.Recognition
