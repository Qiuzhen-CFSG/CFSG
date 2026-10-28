module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Completion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.SL23Local

/-!
# Assembly and involution transport for the three pair representatives

The root-normalizer calculation proves the A₅ fixer of the A₄ pair from
compatible product coordinates and retains its intrinsic component marking.
The five-local construction supplies the actual A₄ and A₅ pairs. The
original-centralizer construction supplies the actual SL₂(3) pair and its
Sylow two stabilizer. They assemble into `ThreePairRepresentatives`, and
the existing completion supplies all four suborbits. Conjugating the literal
ambient fixer transports its involution fusion to every neighbor of the
base vertex.

`Representatives.exists_marked_representatives` constructs all three pairs
from the marked 47.1 geometry, the five-local families of 47.2, the marked
Sylow-three conclusion of 47.3, and the earlier orders |N_G(X)| = 2160
and |N_H(X)| = 48. It retains the edge's literal root coordinates, its
fixer/component equality, and fusion of every fixer involution to z.
`fourSuborbits_of_earlier_source` consumes the construction, also using
|G| = 604800 from 47.1. No representative, fixer, or orbit conclusion
of 47.5 is an input to these theorems.

The earlier conclusions remain explicit: their producers are
`qt-i47-j2-source-involutions` and `qt-i47-j2-source-prime-normalizers`
(in particular its five-local and three-local calculations). Discharging
those premises in the unconditional source argument remains with
`qt-i47-j2-source-suborbits-intersections`. The SL₂(3) construction uses
an actual Sylow subgroup, never the printed semidihedral assertion.

Source: Aschbacher, *Sporadic Groups* (1994), 47.5, printed p.263, and the
common-involution use in 47.6. The group and normalizer orders are earlier
47.1 and 47.3 inputs. No subdegree or coverage conclusion is assumed.
-/

@[expose] public section

open Subgroup MulAction
open Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
variable {G : Type*} [Group G] [Finite G]

namespace ThreePairRepresentatives
variable {D : Seed G} (R : ThreePairRepresentatives D)

/-- Orbit transport of the representative involution fusion, using the literal
conjugation action on both endpoint stabilizers. -/
theorem edgeFixer_involutions_conjugate
    (hG : Nat.card G = 604800) (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (hfusion : ∀ u ∈ edgeFixer G D.base R.edge, orderOf u = 2 → IsConj D.z u)
    {V : D.Vertex} (hV : D.graph.Adj D.base V)
    {u : G} (hu : u ∈ edgeFixer G D.base V) (ho : orderOf u = 2) : IsConj D.z u := by
  obtain ⟨k, hk⟩ := (R.fourSuborbits hG hM).transitive R.edge V
    ((orbitLabel_of_adj D R.edge_adjacent).trans (orbitLabel_of_adj D hV).symm)
  have hf : (edgeFixer G D.base R.edge).map (MulAut.conj (k : G)).toMonoidHom =
      edgeFixer G D.base V := by
    rw [edgeFixer, Subgroup.map_inf _ _ _ (MulAut.conj (k : G)).injective,
      ← stabilizer_smul_eq_stabilizer_map_conj,
      ← stabilizer_smul_eq_stabilizer_map_conj, normalizer_fixes_base D k, hk]
    rfl
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp (hf.symm ▸ hu)
  have hv2 : orderOf v = 2 := ((MulAut.conj (k : G)).orderOf_eq v).symm.trans ho
  exact (hfusion v hv hv2).trans (isConj_iff.mpr ⟨(k : G), rfl⟩)
end ThreePairRepresentatives

namespace Representatives.FiveLocalPairs
variable {D : Seed G} (F : FiveLocalPairs D) (S : SL23Pair D)

/-- Assemble the independently constructed five-local and SL₂(3) pairs. -/
noncomputable def representatives : ThreePairRepresentatives D where
  edge := F.edge
  edge_adjacent := F.root.edge_adjacent
  edge_fixer := ⟨F.root.fixerEquiv⟩
  sl := S.vertex
  sl_join := S.join
  sl_sylow := S.sylow
  five := F.five
  five_join := F.five_join
  five_fixer := F.five_fixer

include F S in
/-- The actual consumer of the local constructions: the existing completion
proves all four suborbits without a new counting argument. -/
theorem fourSuborbits (hG : Nat.card G = 604800)
    (hM : Nat.card (normalizer (D.X : Set G)) = 2160) : FourSuborbits D :=
  (F.representatives S).fourSuborbits hG hM

include F S in
/-- Every edge at the base has the distinguished involution class in its fixer. -/
theorem edge_involutions_conjugate (hG : Nat.card G = 604800)
    (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    {V : D.Vertex} (hV : D.graph.Adj D.base V)
    {u : G} (hu : u ∈ edgeFixer G D.base V) (ho : orderOf u = 2) : IsConj D.z u := by
  exact (F.representatives S).edgeFixer_involutions_conjugate hG hM
    (fun _ hu ho => F.root.fixer_involutions_conjugate hu ho) hV hu ho

end Representatives.FiveLocalPairs

namespace Representatives
variable {D : Seed G} (S : InvolutionGeometry.SelectedGeometry D)
  (hA : PrimeNormalizers.FiveLocal.RootFiveFamily D S.t)
  (hB : PrimeNormalizers.FiveLocal.TwoCentralFiveFamily D S.t)
  (hSyl : ∀ P : Sylow 3 G,
    Nonempty (PrimeNormalizers.ThreeLocal.SylowThreeStructure D P))
  (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
  (hN : Nat.card (SL23Local.localNormalizer D) = 48)
include S hA hB hSyl hM hN

/-- Construct the three representatives from genuine 47.1–47.3 conclusions.
The edge retains its marked root normalizer, its literal component fixer,
and the distinguished involution class needed in the proof of 47.6. -/
theorem exists_marked_representatives :
    ∃ R : ThreePairRepresentatives D,
      Nonempty (RootPairCoordinates D R.edge) ∧
      edgeFixer G D.base R.edge = rootComponent D R.edge ∧
      ∀ u ∈ edgeFixer G D.base R.edge, orderOf u = 2 → IsConj D.z u := by
  obtain ⟨F⟩ := FiveLocal.fiveLocalPairs_nonempty S hA hB hSyl
  obtain ⟨L⟩ := SL23Local.nonempty_pair D hM hN
  exact ⟨F.representatives L, ⟨F.root⟩, F.root.fixer_eq_component,
    fun _ hu ho => F.root.fixer_involutions_conjugate hu ho⟩

/-- The representative contract is inhabited without assuming any of its
pair or stabilizer conclusions. -/
theorem threePairRepresentatives_nonempty : Nonempty (ThreePairRepresentatives D) := by
  obtain ⟨R, _⟩ := exists_marked_representatives S hA hB hSyl hM hN
  exact ⟨R⟩

/-- Apply the existing completion to the constructed representatives. This
proves the four suborbits and join types of 47.5, conditional only on the
specified earlier-source conclusions. The constructed representatives also
support the completion's three stabilizer transport theorems. -/
theorem fourSuborbits_of_earlier_source (hG : Nat.card G = 604800) : FourSuborbits D := by
  obtain ⟨R⟩ := threePairRepresentatives_nonempty S hA hB hSyl hM hN
  exact R.fourSuborbits hG hM

/-- The constructed edge's involution fusion holds for every edge at the base.
This supplies the edge-fixer premise of the common-involution argument. -/
theorem edge_involutions_conjugate_of_earlier_source (hG : Nat.card G = 604800)
    {V : D.Vertex} (hV : D.graph.Adj D.base V)
    {u : G} (hu : u ∈ edgeFixer G D.base V) (ho : orderOf u = 2) : IsConj D.z u := by
  obtain ⟨R, _, _, hfusion⟩ := exists_marked_representatives S hA hB hSyl hM hN
  exact R.edgeFixer_involutions_conjugate hG hM hfusion hV hu ho

end Representatives
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
