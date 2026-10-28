module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Basic
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.WeylRealization.NormalizerAction
public import Theory.AlgebraicGroup.Borel.OppositeBigCell.Separation

/-!
# Root partitions for actual D4 Bruhat splitting

For each Weyl element the positive roots split into those remaining positive
and those becoming negative. The resulting subgroups use the actual root
subgroups of `Geometry`. The geometric obligations below distinguish root
transport, collection across this partition, and separation of Borel double
cosets. None of these obligations is asserted to follow merely by packaging
it in this interface.

Source: GLS3 1.11.3--1.11.5 and 1.12.7(a),
`refs/KGroup/GLS3/Chapter1.tex`. In particular the right factor uses negative
images, as in 1.11.5; the transcription of Steinberg 6.3 in
`Chapter2St2.tex` omits the minus on the second unipotent subgroup.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ConnectedCentralizer.Bruhat.Splitting

universe u
variable {k : Type u} [Field k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

abbrev positiveGroup (S : Geometry K) := RootSubgroupGenerated S.roots S.roots.positive

abbrev negativeGroup (S : Geometry K) :=
  RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive)

def rootAction (S : Geometry K) (w : AmbientCount.Weyl) : S.roots.Root ≃ S.roots.Root :=
  S.rootIndex.trans (((typeDRootPairing 2).weylGroupToPerm w).trans S.rootIndex.symm)

def inversionRoots (S : Geometry K) (w : AmbientCount.Weyl) : Set S.roots.Root :=
  {a | a ∈ S.roots.positive ∧ rootAction S w a ∉ S.roots.positive}

def retainedRoots (S : Geometry K) (w : AmbientCount.Weyl) : Set S.roots.Root :=
  {a | a ∈ S.roots.positive ∧ rootAction S w a ∈ S.roots.positive}

def inversionFactor (S : Geometry K) (w : AmbientCount.Weyl) : Subgroup (Variety.Point K) :=
  RootSubgroupGenerated S.roots (inversionRoots S w)

def retainedFactor (S : Geometry K) (w : AmbientCount.Weyl) : Subgroup (Variety.Point K) :=
  RootSubgroupGenerated S.roots (retainedRoots S w)

/-- Compatibility of the Weyl label with conjugation of actual root subgroups.
The displayed left-conjugation formula is equivalent, after replacing `n`
by its inverse, to the inverse-conjugation convention in GLS3 1.11.5. -/
def RootTransport (S : Geometry K)
    (f : S.torus.normalizer.toSubgroup →* AmbientCount.Weyl) : Prop :=
  ∀ (n : S.torus.normalizer.toSubgroup) (a : S.roots.Root),
    (S.roots.rootSubgroup a).conjugate (n : Variety.Point K) =
      S.roots.rootSubgroup (rootAction S (f n) a)

/-- The two-block positive-root product, before applying a normalizer element.
This is a collection theorem, not a subgroup-supremum statement. -/
def RootPartitionProducts (S : Geometry K) : Prop :=
  ∀ (w : AmbientCount.Weyl) (q : Variety.Point K), q ∈ positiveGroup S →
    ∃ a v : Variety.Point K,
      a ∈ retainedFactor S w ∧ v ∈ inversionFactor S w ∧ q = a * v

/-- Distinct actual normalizer cosets give distinct Borel double cosets.
Raw B--N--B coverage does not itself assert this uniqueness. -/
def CellSeparation (S : Geometry K) : Prop :=
  ∀ (n m : S.torus.normalizer.toSubgroup) (b c d e : Variety.Point K),
    b ∈ S.bigCell.data.B.toSubgroup → c ∈ S.bigCell.data.B.toSubgroup →
    d ∈ S.bigCell.data.B.toSubgroup → e ∈ S.bigCell.data.B.toSubgroup →
    b * (n : Variety.Point K) * c = d * (m : Variety.Point K) * e →
      (n : Variety.Point K)⁻¹ * (m : Variety.Point K) ∈ S.torus.toSubgroup

theorem inversionFactor_le_positive (S : Geometry K) (w : AmbientCount.Weyl) :
    inversionFactor S w ≤ positiveGroup S :=
  RootSubgroupGenerated_mono S.roots (fun _ h => h.1)

theorem retainedFactor_le_positive (S : Geometry K) (w : AmbientCount.Weyl) :
    retainedFactor S w ≤ positiveGroup S :=
  RootSubgroupGenerated_mono S.roots (fun _ h => h.1)

end ConnectedCentralizer.Bruhat.Splitting
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
