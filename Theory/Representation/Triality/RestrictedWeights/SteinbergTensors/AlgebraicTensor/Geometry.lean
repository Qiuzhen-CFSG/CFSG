module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.Construction
public import Theory.AlgebraicGroup.Borel.HighestWeight
public import Theory.AlgebraicGroup.RootData.Chevalley

/-!
# Geometric inputs for rational D4 tensor products

The group is simple and universal, its root data realizes the standard D4
pairing and base, and the positive and opposite Borels form a big cell.
The integral coordinate lattice is identified with actual algebraic torus
characters through their evaluations on the numbered simple coroots.
Regular root parametrizations and their compatible coroots specify a genuine
pinning. No representation-theoretic conclusions are fields of this setup.

Ordinary Frobenius is a regular, point-surjective endomorphism acting by
squaring on the pinned roots and torus. Triality is an algebraic isomorphism
with the forward numbered diagram action on roots and coroots. In particular,
no regular inverse to Frobenius is assumed.

Sources: GLS3, §§1.9–1.15, Definition 2.8.3 and Remark 2.8.4,
`refs/KGroup/GLS3/Chapter1.tex` and `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (K : Variety k) [AlgebraicGroup K]

/-- Geometric inputs for a simple simply connected group of type D4.
The weight map is an isomorphism with actual algebraic torus characters, and
its coordinates are evaluations on the actual simple coroots. No assertion
about representations is included. -/
structure D4Geometry where
  simple : IsSimpleAlgebraicGroup K
  universal : IsUniversalVersion K
  torus : ClosedSubgroup K
  maximalTorus : IsMaximalTorus torus
  roots : RootGroupData K torus
  realized : roots.IsRealization
  rootEquiv : roots.Root ≃ TypeDRootIndex 4
  based : IsRootSystemRealization roots (typeDRootPairing 2)
    rootEquiv (typeDRootPairing_base 2)
  addition : IsRootAdditionRealization roots (typeDRootPairing 2) rootEquiv
  bigCell : OppositeBorelBigCell torus roots roots.positive
  characters : Multiplicative Weight ≃* TorusWeight torus
  coroot_coordinates : ∀ x i,
    roots.weightPairing (characters (Multiplicative.ofAdd x))
      (rootEquiv.symm (typeDSimpleRootIndex 2 i)) = x i
  chevalley : ChevalleyData K roots
  chevalley_spec : IsChevalleySystem roots chevalley (typeDRootPairing 2)
    rootEquiv (typeDRootPairing_base 2)
  rootParam : ∀ α, OneParameterParametrization (roots.rootSubgroup α).carrierVariety
  rootParam_spec : ∀ α t,
    (roots.rootSubgroup α).includePoint ((rootParam α).value t) = chevalley.x α t
  coroot_spec : ∀ α t,
    torus.includePoint ((roots.rootCocharacter α).onPoints t) =
      chevalley.h α (dPointEquiv 1 t 0)

variable {K}

/-- The Borel belonging to the chosen positive root system. -/
def D4Geometry.borel (S : D4Geometry K) : ClosedSubgroup K := S.bigCell.data.B

/-- The embedding required by the existing basic-family interface. -/
def D4Geometry.weightEmbedding (S : D4Geometry K) : Weight ↪ TorusWeight S.torus :=
  ⟨fun x => S.characters (Multiplicative.ofAdd x),
    fun _ _ h => S.characters.injective h⟩

omit [IsAlgClosed k] in
/-- The embedded weight coordinates are actual character--coroot exponents. -/
theorem D4Geometry.weightEmbedding_coroot (S : D4Geometry K) (x : Weight) (i : Fin 4) :
    WeightCocharacterEquation S.torus (S.weightEmbedding x)
      (S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))) (x i) := by
  rw [← S.coroot_coordinates x i]
  exact S.realized.weightPairing_spec _ _

/-- Ordinary Frobenius for this pinning, as an actual regular group morphism.
Its torus action is squaring and its root action squares the root parameter. -/
structure OrdinaryFrobenius (S : D4Geometry K) where
  morphism : Theory.AlgebraicGroup.Morphism K K
  surjective : Function.Surjective morphism.onPoints
  root_formula : ∀ α t, morphism.onPoints (S.chevalley.x α t) = S.chevalley.x α (t ^ 2)
  torus_formula : ∀ t : Variety.Point S.torus.carrierVariety,
    morphism.onPoints (S.torus.includePoint t) = S.torus.includePoint (t ^ 2)
  borel_stable : ∀ b, b ∈ S.borel → morphism.onPoints b ∈ S.borel

/-- The pinned diagram automorphism, with its geometric action on coroots.
The forward convention sends vertex `i` to `typeD4DiagramPermutation i`. -/
structure PinnedTriality (S : D4Geometry K) where
  iso : Theory.AlgebraicGroup.Iso K K
  root_formula : ∀ α t, iso.hom.onPoints (S.chevalley.x α t) =
    S.chevalley.x (S.rootEquiv.symm (typeD4DiagramEquiv.indexEquiv (S.rootEquiv α))) t
  coroot_formula : ∀ i t,
    iso.hom.onPoints
      (S.torus.includePoint
        ((S.roots.rootCocharacter (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))).onPoints t)) =
    S.torus.includePoint
      ((S.roots.rootCocharacter
        (S.rootEquiv.symm (typeDSimpleRootIndex 2 (typeD4DiagramPermutation i)))).onPoints t)
  torus_stable : ∀ t, t ∈ S.torus → iso.hom.onPoints t ∈ S.torus
  torus_inverse_stable : ∀ t, t ∈ S.torus → iso.inv.onPoints t ∈ S.torus
  borel_stable : ∀ b, b ∈ S.borel → iso.hom.onPoints b ∈ S.borel
  borel_inverse_stable : ∀ b, b ∈ S.borel → iso.inv.onPoints b ∈ S.borel

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
