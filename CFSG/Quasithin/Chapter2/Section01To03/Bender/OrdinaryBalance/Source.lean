module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.OrdinaryBalance
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
public import CFSG.Quasithin.ChapterI.Section03.LayerBalance

/-!
# The proved ordinary-balance input to the empty-delta Bender branch

The unconditional Sylow-fixer theorem and GLS II 5.17 supply the two
universal inputs of the ordinary-component orbit theorem. This discharges
OrdinaryBalance13 for the full known-simple catalogue. The existing Bender
application retains H = C_G(v), t = u, the component pullback and every
original subtype map.

The empty-delta consumer constructs the local-control witness and its
involution-centralizer containments. Its only remaining earlier-source
input is the literal component-action clause of 1.1.5, owned by qt-1-01;
the full Bender recognition and Theorem ZD remain with their existing owners.

Source: Aschbacher--Smith 2.2.2, printed pp.519--520, using I.3.1 and
GLS II 5.17/5.22.
-/

public section

namespace CFSG.Quasithin.Chapter2.BenderFusion
open Subgroup Theory.GroupTheory
universe u

/-- The actual ordinary balance needed by Bender, with both earlier
Sylow-fixer and two-layer implications supplied by their proved theorems. -/
theorem BadCentralizers.ordinaryBalance13_knownSimple :
    BadCentralizers.OrdinaryBalance13.{u} CFSG.KnownSimple.IsKnownSimple := by
  apply BadCentralizers.ordinaryBalance13_of_sylowFixer_and_twoLayer
  · intro S _ _ _ P
    exact ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  · intro H _ _ hS P hP
    exact ChapterI.LayerBalance.map_twoLayer_centralizer_le hS P hP

/-- The original empty-delta application with ordinary balance discharged.
The complete earlier 1.1.5 component-action implication is retained literally. -/
theorem source_local_control_with_centralizers_of_delta_empty_and_source115
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleQTKE CFSG.KnownSimple.IsKnownSimple G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : delta (Chapter1.He G) M = ∅)
    (source115 : BadCentralizers.ComponentSource115 G) :
    ∃ w : LocalControlWitness T M,
      ∀ u ∈ w.U, u ≠ 1 → centralizer ({u} : Set G) ≤ M :=
  source_local_control_with_centralizers_of_delta_empty hG T M hM hTM hunique hdelta
    source115 BadCentralizers.ordinaryBalance13_knownSimple

end CFSG.Quasithin.Chapter2.BenderFusion
