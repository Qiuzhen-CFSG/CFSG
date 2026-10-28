module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Stabilizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Orbits
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Projection

/-!
# The solvable factor argument in 13.6.13

Starting with the constructed normal S₃ decomposition, minimality gives
T_v* transitivity and irreducibility on U_H. The genuine marked A₅ seed
then gives U_X = U_H and nontrivial L_v movement. The factor normalizer
index bounds and the actual support actions identify L_v* = O²(H_i*).
Here the normal-S₃ argument takes place in the factor stabilizer; it does
not require the entire star group to split as a direct product.

Sylow invariance now forces one factor, so L_v* = X*. X-family membership
supplies the literal Thompson commutator identity, while relative
normality of the factor residual supplies subnormality in the star group.
The final theorem discharges all orbit, irreducibility, movement and
factor-identification premises from the original marked inputs and the
explicit decomposition. The assembly of source 13.6.13 must still construct
that decomposition and apply the independently proved 13.6.10 obstruction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
namespace FactorArgument
variable {G : Type*} [Group G] [Finite G]

/-- The last two assertions of the source factor argument, after its two
independent group-theoretic inputs have been supplied. -/
theorem commutator_and_subnormal_of_transitive_factor
    (L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    {X : Subgroup (Gstar z v)} (hX : X ∈ XFamily L T z v)
    (d : NormalS3Decomposition z v X)
    (htrans : d.FactorsTransitive T)
    (hfactor : ∃ i, starImage z v (Lv L v) = d.factorResidual i) :
    starImage z v (Lv L v) =
        ⁅starImage z v (Lv L v),
          starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ ∧
      (starImage z v (Lv L v)).IsSubnormal := by
  obtain ⟨i, hi⟩ := hfactor
  have he := d.eq_X_of_transitive_invariant_residual T htrans
    (starImage z v (Lv L v)) (starTv_normalizes_starLv L T z v hL) i hi
  refine ⟨?_, hi.symm ▸ d.factorResidual_isSubnormal i⟩
  rw [he]
  exact hX.1.2.2.2.symm

/-- The actual moved module and cubic factor in the source argument.
Minimality supplies irreducibility, the marked seed supplies movement, and
the normalizer-index bound discharges the projection theorem's last premise. -/
theorem marked_factor_identification
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hcard : Nat.card (Lv L (A5Module.markedV s) ⧸
      pCore 2 (Lv L (A5Module.markedV s))) = 3)
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (d : NormalS3Decomposition (A5Module.markedZ s) (A5Module.markedV s) X) :
    UX L (A5Module.markedZ s) (A5Module.markedV s) X =
        movedSubgroup (A5Module.markedZ s) (A5Module.markedV s) d.H ∧
      ∃ i, starImage (A5Module.markedZ s) (A5Module.markedV s)
        (Lv L (A5Module.markedV s)) = d.factorResidual i := by
  obtain ⟨hUX, hmove⟩ :=
    d.marked_moved_commutator_of_minimalSolvable s T S hS hfix hL hX
  exact ⟨hUX, Projection.exists_factorResidual_of_movement L T _ _ S hS hL hcard d
    hmove d.factor_normalizer_index_le_two⟩

/-- The second half of 13.6.13, conditional only on the constructed normal
S₃ decomposition and the earlier marked source inputs. The Thompson subgroup
is the literal J(T_v), and subnormality is in the original star quotient.
The source assembly applies its separate 13.6.10 obstruction to this pair. -/
theorem commutator_and_subnormal_of_minimalSolvable
    {L V : Subgroup G} (s : A5Module.Marking L V) (T : Subgroup G)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map (Gv (A5Module.markedV s)).subtype =
      Tv T (A5Module.markedV s))
    (hfix : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hcard : Nat.card (Lv L (A5Module.markedV s) ⧸
      pCore 2 (Lv L (A5Module.markedV s))) = 3)
    {X : Subgroup (Gstar (A5Module.markedZ s) (A5Module.markedV s))}
    (hX : MinimalSolvable L T (A5Module.markedZ s) (A5Module.markedV s) X)
    (d : NormalS3Decomposition (A5Module.markedZ s) (A5Module.markedV s) X) :
    starImage (A5Module.markedZ s) (A5Module.markedV s) (Lv L (A5Module.markedV s)) =
        ⁅starImage (A5Module.markedZ s) (A5Module.markedV s) (Lv L (A5Module.markedV s)),
          starImage (A5Module.markedZ s) (A5Module.markedV s)
            (Stellmacher.elementaryAbelianMaxJ (Tv T (A5Module.markedV s)))⁆ ∧
      (starImage (A5Module.markedZ s) (A5Module.markedV s)
        (Lv L (A5Module.markedV s))).IsSubnormal :=
  commutator_and_subnormal_of_transitive_factor L T _ _ hL hX.1 d
    (d.factorsTransitive L T hX S hS)
    (marked_factor_identification s T S hS hfix hL hcard hX d).2

end FactorArgument
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable
end
