module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.LocalGroups

/-!
# The natural-module output of the binary local argument

This output interface separates the actual natural-module identification and
fixed/moving splitting from the later critical-pair calculations. Its existence
from LocalSource, Geometry and b > 2 remains a proof obligation. The marking
belongs to the specified SL₃(2) quotient and acts on the actual U subgroup.
No module dimension label is used as a replacement for that identification.

Source: MS93 (1993), the binary parts of (3.2)--(3.3), (3.8), (4.1), printed
pp.863--868, 877--879, 881--882. In particular the doubled and nonsplit cases
of (3.2) must be excluded by the local argument before constructing this output.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The module and splitting conclusions, to be constructed from the source. -/
structure BinaryNaturalStructure (source : LocalSource L R) where
  X_eq_Z : ∀ a, color R a = false → X R a = Z R a
  natural : NaturalU R source.projection
  decomposition : Z R (alpha R) = U R (alpha R) ⊔
    (Z R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)))
  disjoint : Disjoint (U R (alpha R))
    (Z R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
