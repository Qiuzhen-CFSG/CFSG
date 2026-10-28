module

public import CFSG.Quasithin.ChapterJ.Section01To02.Preliminaries
public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The chosen subgroups for the odd-centralizer arguments in J.2

These are the choices made before J.2.3: B is a Sylow three-subgroup of
L₁, B₇ is a B-invariant subgroup of L of order seven, s is a nonidentity
member of C_S(B₇), and z generates Z. No centralizer recognition, fusion,
or additional SQTK hypothesis is included. Earlier J.2 producers must
construct these choices from `LocalSetup`.

The two residuals are kept distinct: L_B = C_G(B)^∞ is the solvable
residual, while L_s = O²(C_G(s)) is the two-residual. Both are mapped
into the ambient group through their literal subgroup inclusions.

Source: Aschbacher–Smith, printed pp.433,435,438 (PDF pp.444,446,449).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Centralizers
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The choices preceding J.2.3, with their original ambient embeddings. -/
structure Choices (d : LocalSetup G) where
  sylowThree : Sylow 3 d.toTypeRuSetup.L₁
  B7 : Subgroup G
  B7_le : B7 ≤ d.L
  B7_card : Nat.card B7 = 7
  B_normalizes : (sylowThree : Subgroup d.toTypeRuSetup.L₁).map
    d.toTypeRuSetup.L₁.subtype ≤ normalizer (B7 : Set G)
  s : G
  s_mem : s ∈ d.toTypeRuSetup.S ⊓ centralizer (B7 : Set G)
  s_ne_one : s ≠ 1
  z : G
  z_generator : d.toTypeRuSetup.Z = zpowers z

namespace Choices
variable {d : LocalSetup G} (c : Choices d)

abbrev B : Subgroup G :=
  (c.sylowThree : Subgroup d.toTypeRuSetup.L₁).map d.toTypeRuSetup.L₁.subtype
abbrev S0 : Subgroup G := d.toTypeRuSetup.S ⊓ centralizer (c.B7 : Set G)
abbrev Ts : Subgroup G := d.toTypeRuSetup.S ⊓ centralizer ({c.s} : Set G)
abbrev S1 : Subgroup G := ⁅c.Ts, c.B7⁆
abbrev GB : Subgroup G := centralizer (c.B : Set G)
abbrev NB : Subgroup G := normalizer (c.B : Set G)
abbrev LB : Subgroup G := (solvableResidual c.GB).map c.GB.subtype
abbrev Gs : Subgroup G := centralizer ({c.s} : Set G)
abbrev Ls : Subgroup G := (pResidual 2 c.Gs).map c.Gs.subtype

end Choices
end CFSG.Quasithin.ChapterJ.Centralizers
