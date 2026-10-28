module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.Contracts
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The Sylow-five normalizer in the hypothetical small-centralizer branch

These definitions retain the source Sylow subgroup of H = C_G(z), its actual
ambient image P, and V = O₃(N_G(P)) under the normalizer subtype map. The
record specifies the normalizer facts still required from the hypothetical
order 51840. It is not an existence assertion or a recognition theorem.

The involution lies in the literal N_H(P); hence it centralizes z and acts
on V. The local normalizer order will imply that z inverts V. The separate action
argument then derives the centralizer contradiction, without assuming its
fixed-space orders.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.1, printed p.260.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer

variable {G : Type*} [Group G] [Finite G]

/-- The source Sylow-five subgroup, embedded from H into G. -/
def ambientFive (D : Seed G) (P : Sylow 5 (involutionCentralizer D.z)) : Subgroup G :=
  (P : Subgroup (involutionCentralizer D.z)).map (involutionCentralizer D.z).subtype

/-- The full ambient normalizer of the embedded source Sylow subgroup. -/
def fiveNormalizer (D : Seed G) (P : Sylow 5 (involutionCentralizer D.z)) : Subgroup G :=
  normalizer (ambientFive D P : Set G)

/-- The normalizer's three-core, with its literal ambient embedding. -/
def normalizerThreeCore (D : Seed G) (P : Sylow 5 (involutionCentralizer D.z)) : Subgroup G :=
  (fiveNormalizer D P).pCoreIn 3

/-- The earlier normalizer calculations needed after Thompson's formula has
produced order 51840. All subgroups, actions and normalizers are literal.
The fixed centralizer of order divisible by nine is not a field. -/
structure FiveNormalizerData (D : Seed G) where
  P : Sylow 5 (involutionCentralizer D.z)
  localEquiv :
    normalizer ((P : Subgroup (involutionCentralizer D.z)) : Set (involutionCentralizer D.z)) ≃*
      DihedralGroup 10
  twoPart : (Nat.card (fiveNormalizer D P)).factorization 2 = 2
  core_card : Nat.card (normalizerThreeCore D P) = 27
  s : normalizer ((P : Subgroup (involutionCentralizer D.z)) : Set (involutionCentralizer D.z))
  s_order : orderOf s = 2
  s_ne_z : ((s : involutionCentralizer D.z) : G) ≠ D.z
  s_inverts_five : ∀ p ∈ ambientFive D P,
    ((s : involutionCentralizer D.z) : G) * p *
      ((s : involutionCentralizer D.z) : G)⁻¹ = p⁻¹

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
