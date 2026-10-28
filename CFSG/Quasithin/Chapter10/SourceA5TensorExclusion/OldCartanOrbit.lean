module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorLine
public import Theory.GroupAction.CardFourCubic.Conjugation

/-!
# Cubic Cartan orbits on the original tensor line

The original common-Sylow fixed line has four elements. A nontrivial cubic
Cartan action therefore has no proper nontrivial invariant subgroup, and
the Cartan orbit of any nonidentity point generates the whole original line.
This supplies the orbit input for source 9.3.1 and the irreducibility input
for 9.3.6. Construction and marking of the actual Cartan remain separate.
Source: Aschbacher–Smith, printed pp.732–734, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}

/-- Retain the literal original line and the original ambient Cartan action. -/
theorem tensorLine_cartan_orbit (m : SourceA5TensorModel D e)
    (A : Subgroup G) (hA : A ≤ normalizer (m.tensorLine : Set G))
    (a : G) (haA : a ∈ A) (ha3 : a ^ 3 = 1)
    (haC : a ∉ centralizer (m.tensorLine : Set G))
    (u : G) (hu : u ∈ m.tensorLine) (hu1 : u ≠ 1) :
    componentOrbit (zpowers u) A = m.tensorLine :=
  Theory.GroupAction.CardFourCubic.componentOrbit_zpowers_eq
    m.tensorLine A m.card_tensorLine hA a haA ha3 haC u hu hu1

/-- Every subgroup of the original line normalized by the marked Cartan is
trivial or the full original line. -/
theorem tensorLine_cartan_irreducible (m : SourceA5TensorModel D e)
    (A : Subgroup G) (hA : A ≤ normalizer (m.tensorLine : Set G))
    (a : G) (haA : a ∈ A) (ha3 : a ^ 3 = 1)
    (haC : a ∉ centralizer (m.tensorLine : Set G))
    (N : Subgroup G) (hN : N ≤ m.tensorLine) (hAN : A ≤ normalizer (N : Set G)) :
    N = ⊥ ∨ N = m.tensorLine :=
  Theory.GroupAction.CardFourCubic.invariant_ambient_subgroup
    m.tensorLine m.card_tensorLine a (hA haA) ha3 haC N hN (hAN haA)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
