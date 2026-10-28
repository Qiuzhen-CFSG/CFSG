module

public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.Amalgam
public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.EdgeAmalgam
public import Theory.GroupTheory.GraphUniquenessSystem.UniversalCompletion.PathPresentation

/-!
# Universal-completion machinery for graph uniqueness systems

The rank-three amalgam retains vertex, setwise-edge, and local groups, with all
three intersection compatibilities. Its inverse comparison maps lift to the
extension required by recognition. The geometric interface uses the actual
normal closure of local cycles: a graph covering that lifts generating cycles
closed has singleton fibers when its source is connected.

The rank-three path presentation connects the amalgam with this covering
argument and is canonically isomorphic to the acting group under the cycle-base
hypothesis. Compatible maps to arbitrary groups therefore extend uniquely.
Equivalence supplies the compatible setwise-edge isomorphism; only the target
system needs a cycle base.

Source: Aschbacher, *Sporadic Groups* (1994), 35.16 and 37.4–37.6.
-/

@[expose] public section

namespace Theory.GroupTheory.GraphUniquenessSystem

universe u v u' v'
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable {G' : Type u'} {V' : Type v'} [Group G'] [MulAction G' V']

namespace Similarity
variable {U : System G V} {U' : System G' V'} (s : Similarity U U')

/-- An equivalence extends from a target with a normal cycle base to the source
group. The edge-conjugation compatibility supplies the third amalgam map, and
the target's cycle base extends the inverse maps on all three groups. -/
theorem nonempty_extension_of_isEquivalence_of_isBase
    (hs : s.IsEquivalence) (hb : U'.IsBase) : Nonempty s.Extension := by
  obtain ⟨e⟩ := s.nonempty_amalgamEquiv_of_isEquivalence hs
  exact ⟨e.extensionOfLift (e.inverseMap.liftOfBase hb)⟩

end Similarity
end Theory.GroupTheory.GraphUniquenessSystem
