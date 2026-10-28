module

public import CFSG.Quasithin.Defs
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Data.ZMod.Basic

/-!
# The local configuration of Theorem 13.9.1

The source excludes a maximal two-local subgroup containing a Sylow
two-subgroup and isomorphic to the literal wreath product `S₄ wr C₂`.
`Configuration` records exactly these local inputs. The ambient simple QTKE
hypothesis is supplied separately; none of the later fusion or centralizer
conclusions is part of this record.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Theorem
13.9.1 and its setup, printed p.969 (PDF p.986). The source theorem uses
the full known-simple class in the QTKE hypothesis.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section09

/-- The actual symmetric wreath product appearing in 13.9.1. -/
abbrev WreathModel :=
  RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2))

/-- The local inputs of 13.9.1, with a chosen actual model isomorphism. -/
structure Configuration (G : Type*) [Group G] where
  T : Sylow 2 G
  M : Subgroup G
  maximal : IsMaximalTwoLocal M
  sylow_le : (T : Subgroup G) ≤ M
  model : M ≃* WreathModel

end CFSG.Quasithin.Chapter13.Section09
