module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Orbits.SupportTransport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Orbits.InvariantSupportSums
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Stabilizer

/-!
# Consumers of the solvable factor orbit argument

The normalizer-index bound now discharges the explicit index premise in the
factor alternative. Minimality and the given Sylow witness also prove actual
T_v* transitivity, in `Orbits/FactorConjugation.lean`.

The cubic residuals split every X-invariant subgroup into its actual supports.
Combining this decomposition with transitivity proves irreducibility for X T_v
on U_H. The marked consumer then gives U_X = U_H and the nonzero L_v commutator,
with no additional support-decomposition or irreducibility premise.

These results start with the constructed normal S₃ decomposition. Its
construction, the subsequent L_v* factor identification and the final
contradiction remain with the assembly of source 13.6.13.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 13.6.13, printed p.929.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
variable {G : Type*} [Group G] [Finite G]
namespace FactorArgument

/-- The actual factor alternative, with the normalizer-index premise discharged
by the conjugation action on the specified one- or two-factor product. -/
theorem factor_alternative (L T : Subgroup G) (z v : G)
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    {X : Subgroup (Gstar z v)} (d : NormalS3Decomposition z v X)
    (i : Fin d.count) :
    starImage z v (Lv L v) = d.factorResidual i ∨
      starImage z v (Lv L v) ≤ centralizer (d.factor i : Set (Gstar z v)) :=
  factor_alternative_of_small_normalizer_index L T z v S hS hL hcard d i
    (d.factor_normalizer_index_le_two i)

end FactorArgument

/-- Minimality and the actual Sylow witness give transitivity, while the
independent cubic actors split invariant subgroups into their supports.
Together they prove the source irreducibility assertion on the literal U_H. -/
theorem NormalS3Decomposition.irreducible_of_minimalSolvable
    (L T : Subgroup G) {z v : G} [IsElementaryAbelian 2 (Uv z v)]
    {X : Subgroup (Gstar z v)} (hX : MinimalSolvable L T z v X)
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (d : NormalS3Decomposition z v X) :
    IrreducibleOn (starPreimage z v X ⊔ Tv T v) (movedSubgroup z v d.H) :=
  d.irreducible_of_factorsTransitive T (d.factorsTransitive L T hX S hS)

/-- The source's marked module identification after the local invariant-support
calculation. Transitivity is proved from minimality and the actual Sylow witness. -/
theorem NormalS3Decomposition.marked_moved_commutator_of_invariantSupportSums
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (d : NormalS3Decomposition (A5Module.markedZ s) (A5Module.markedV s) X)
    (hsum : d.InvariantSupportSums) :
    UX L (A5Module.markedZ s) (A5Module.markedV s) X =
        movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) d.H ∧
      ⁅movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) d.H,
        Lv L (A5Module.markedV s)⁆ ≠ ⊥ :=
  d.marked_moved_commutator s T S hS hfix hL hX.1
    (d.irreducible_of_invariantSupportSums T (d.factorsTransitive L T hX S hS) hsum)

/-- The source's marked module identification and nonzero L_v commutator,
with transitivity and irreducibility proved from the minimal solvable member
and its specified decomposition. This discharges Configuration's explicit
irreducibility premise using the actual star preimage and Sylow actor. -/
theorem NormalS3Decomposition.marked_moved_commutator_of_minimalSolvable
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (d : NormalS3Decomposition (A5Module.markedZ s) (A5Module.markedV s) X) :
    UX L (A5Module.markedZ s) (A5Module.markedV s) X =
        movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) d.H ∧
      ⁅movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) d.H,
        Lv L (A5Module.markedV s)⁆ ≠ ⊥ :=
  d.marked_moved_commutator s T S hS hfix hL hX.1
    (d.irreducible_of_minimalSolvable L T hX S hS)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
end
