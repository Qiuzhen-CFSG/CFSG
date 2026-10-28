module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalHypotheses
public import CFSG.Quasithin.ClassicalModels
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Data.ZMod.Basic
/-!
# The bare original hypotheses of C.6.1

The quotient alternatives retain O²(H/O₂(H)), rather than replacing it with
the whole quotient or with a marked module. The actual intersection Λ∩H is
the image of the supplied Sylow subgroup. Normalizer control is exactly the
source assertion for its nontrivial H-normal subgroups.

No SQTK, minimal-parabolic, block or representation assumption is added.
The separate bridge theorems derive those properties from these models.
Source: Aschbacher--Smith C.6.1(i)--(iv), printed p.164.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section06.Original

abbrev CubicWreath := RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))

/-- The three quotient alternatives of C.6.1(i), before any block marking. -/
def QuotientModels (H : Type*) [Group H] : Prop :=
  (∃ n : ℕ, ClassicalGroup.IsPSL (pResidual 2 (H ⧸ pCore 2 H)) 2 (2 ^ n)) ∨
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∨
    Nonempty ((H ⧸ pCore 2 H) ≃* CubicWreath)

variable {G : Type*} [Group G]

structure Input (H Λ : Subgroup G) where
  fitting : generalizedFitting H = pCore 2 H
  models : QuotientModels H
  two : IsPGroup 2 Λ
  sylow : Sylow 2 H
  intersection : (sylow : Subgroup H).map H.subtype = Λ ⊓ H
  proper : Λ ⊓ H < Λ
  control : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ Λ ⊓ H →
    H ≤ normalizer (W : Set G) → Λ ⊓ normalizer (W : Set G) = Λ ⊓ H

end CFSG.Quasithin.ChapterC.Section06.Original
