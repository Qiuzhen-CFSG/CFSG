module

public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# The quadratic subgroup family used in Chapter K

The family D(G,V) consists of the noncyclic elementary abelian two-subgroups
acting quadratically. Its rank condition is literal binary rank, independent
of whether its action ratio is at most two.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.4,
printed p.458. Cubic and quadratic ratios are re-exported from the
representation layer, with distinct indexing families.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK
open Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The source's D(G,V), expressed by noncyclicity through binary rank. -/
def quadraticSubgroups (ρ : Representation (ZMod 2) G V) : Set (Subgroup G) :=
  {A | IsElementaryTwo A ∧ 1 < rank A ∧ IsQuadratic ρ A}

end CFSG.Quasithin.ChapterK
