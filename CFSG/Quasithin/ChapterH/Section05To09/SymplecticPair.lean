module

public import Theory.Representation.SymplecticConjugatePair.Parabolics
public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.Setup
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module

/-!
# Root witnesses for the paired symplectic module in H.7

Each nonidentity element of each concrete root subgroup is an involution
with fixed codimension 3n on the canonical natural-plus-graph-conjugate
module. Consequently it supplies the upper bound for the actual minimum
involution parameter of E.3.1. Swapping involutions have codimension 4n by
the re-exported linear calculation. The concrete plane radical gives an
elementary abelian rank-3n witness with fixed codimension 5n.

The lower bound for all involutions, the acting overgroup's two-rank, the
E.3.8 fixed-space-family bound, and the α and β arguments remain separate
obligations. In particular no equality for an arbitrary overgroup is inferred
from these witnesses in the full symplectic group; at n = 1 the source must
keep that group distinct from its derived subgroup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.7, printed pp.388–389; E.3.1, printed p.231.
-/

public section

namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
open Representation.BinaryOffender
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The attaining root involutions, in all eight actual root families. -/
theorem root_witnesses {n : ℕ} (hF : Nat.card F = 2^n) (r : Fin 8) :
    orderOf (rootElement r (1 : F)) = 2 ∧
      fixedCodim (graphPair (F := F)) (Subgroup.zpowers (rootElement r (1 : F))) = 3*n :=
  ⟨root_involution r one_ne_zero, root_fixedCodim_of_card hF r one_ne_zero⟩

/-- One direction of the minimum-involution parameter calculation on the
full matrix group. The opposite direction requires the involution analysis. -/
theorem moduleM_graphPair_le {n : ℕ} (hF : Nat.card F = 2^n) :
    ChapterE.moduleM (graphPair (F := F)) ≤ 3*n := by
  obtain ⟨ho, hc⟩ := root_witnesses hF 0
  exact (ChapterE.moduleM_le_involution (graphPair (F := F))
    (t := rootElement 0 (1 : F)) ho).trans_eq hc

/-- A literal maximal-parabolic radical realizes rank 3n; its paired fixed
space has codimension 5n. This concerns the full symplectic carrier. -/
theorem plane_radical_witness {n : ℕ} (hF : Nat.card F = 2^n) :
    IsElementaryAbelian 2 (planeRadical (F := F)) ∧
      rank (planeRadical (F := F)) = 3*n ∧
      fixedCodim (graphPair (F := F)) planeRadical = 5*n :=
  ⟨planeRadical_elementary, rank_planeRadical hF, planeRadical_fixedCodim hF⟩

end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
