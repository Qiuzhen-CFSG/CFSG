module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.RegularFunctions
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusGeometry.PinnedMaps
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedRootTorus.RootStability

/-!
# Transport of outer regular functions by the actual D4 diagram map

The geometric torus restriction and its simple-coroot permutation determine
pullback on the actual left characters. The ambient diagram map preserves the
original positive root subgroups, so its regular pullback carries a normalized
highest-weight function to another such function. In the fixed numbering the
forward map cycles roots as `0 → 2 → 3 → 0`, and function pullback cycles the
fundamental weights as `0 → 3 → 2 → 0`.

Thus a single outer function supplies the other two. Existence of the first
function is a separate obligation: no fundamental representation is assumed
or constructed by the transport theorem itself.

Sources: GLS3, Examples 1.14.9(d),(f) and §1.15; Steinberg, (6.1) and §13,
`refs/KGroup/GLS3/Chapter1.tex` and `Chapter2St2.tex`.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

open ClassBound.AmbientCount.TorusGeometry ClassBound.FixedRootTorus

/-- The actual ambient diagram automorphism restricted regularly to the torus. -/
def diagramTorus (S : Geometry K) :
    Theory.AlgebraicGroup.Morphism S.torus.carrierVariety S.torus.carrierVariety :=
  (Classical.choice (nonempty_pinnedTorusMaps S)).diagram

/-- The torus restriction intertwines the actual ambient inclusions. -/
theorem diagramTorus_ambient (S : Geometry K) (t : S.torus.carrierVariety.Point) :
    S.torus.includePoint ((diagramTorus S).onPoints t) =
      S.diagram.toMulEquiv (S.torus.includePoint t) :=
  (Classical.choice (nonempty_pinnedTorusMaps S)).diagram_ambient t

/-- Forward graph pullback precomposes coordinates by the numbered permutation. -/
theorem diagramTorus_leftWeight (S : Geometry K) (a : Weight)
    (t : S.torus.carrierVariety.Point) :
    (S.leftWeightEmbedding a).pointCharacter ((diagramTorus S).onPoints t) =
      (S.leftWeightEmbedding (a ∘ typeD4DiagramPermutation)).pointCharacter t := by
  let F := Classical.choice (nonempty_pinnedTorusMaps S)
  have h := pullback_weight_of_coroot S F.diagram typeD4DiagramPermutation 1
    (by simpa only [pow_one] using F.diagram_coroot) (-a) t
  rw [S.leftWeightEmbedding_eq_raw, S.leftWeightEmbedding_eq_raw]
  change (S.weight (Multiplicative.ofAdd (-a))).pointCharacter (F.diagram.onPoints t) =
    (S.weight (Multiplicative.ofAdd (-(a ∘ typeD4DiagramPermutation)))).pointCharacter t
  have hn : (-a) ∘ typeD4DiagramPermutation = -(a ∘ typeD4DiagramPermutation) := rfl
  simpa only [pow_one, hn] using h

/-- The pullback identity is an equality of actual algebraic characters. -/
theorem diagramTorus_pullback_leftWeight (S : Geometry K) (a : Weight) :
    TorusCharacter.pullback (diagramTorus S) (S.leftWeightEmbedding a) =
      S.leftWeightEmbedding (a ∘ typeD4DiagramPermutation) := by
  apply TorusCharacter.pointCharacter_injective
  ext t
  exact diagramTorus_leftWeight S a t

/-- Pullback along the actual regular diagram map preserves global regularity. -/
def diagramPullback (S : Geometry K) (f : K.PolynomialFunction) : K.PolynomialFunction :=
  Variety.PolynomialFunction.pullback S.diagram.hom.toVariety f

omit [IsAlgClosed k] in
@[simp] theorem diagramPullback_apply (S : Geometry K) (f : K.PolynomialFunction)
    (x : K.Point) : diagramPullback S f x = f (S.diagram.toMulEquiv x) := rfl

/-- Graph pullback preserves normalization and the original positive-root laws. -/
theorem diagramPullback_highest (S : Geometry K) {a : Weight} {f : K.PolynomialFunction}
    (hf : IsLeftHighestWeightRegularFunction S a f) :
    IsLeftHighestWeightRegularFunction S (a ∘ typeD4DiagramPermutation)
      (diagramPullback S f) := by
  refine ⟨?_, ?_, ?_⟩
  · change f (S.diagram.toMulEquiv 1) = 1
    rw [map_one, hf.at_one]
  · intro t x
    simp only [diagramPullback_apply, map_mul]
    rw [← diagramTorus_ambient S t, hf.torus, diagramTorus_leftWeight]
  · intro r hr v x
    have hv : (S.roots.rootSubgroup r).includePoint v ∈ S.roots.rootSubgroup r :=
      ((S.roots.rootSubgroup r).pointEquiv v).property
    have hmap : S.diagram.toMulEquiv ((S.roots.rootSubgroup r).includePoint v) ∈
        S.roots.rootSubgroup (diagramRoot S r) := by
      change S.diagram.toMulEquiv ((S.roots.rootSubgroup r).includePoint v) ∈
        (S.roots.rootSubgroup (diagramRoot S r)).toSubgroup
      rw [← diagram_map_rootSubgroup S r]
      exact ⟨_, hv, rfl⟩
    let w := (S.roots.rootSubgroup (diagramRoot S r)).pointEquiv.symm ⟨_, hmap⟩
    have hw : (S.roots.rootSubgroup (diagramRoot S r)).includePoint w =
        S.diagram.toMulEquiv ((S.roots.rootSubgroup r).includePoint v) :=
      congrArg Subtype.val
        ((S.roots.rootSubgroup (diagramRoot S r)).pointEquiv.apply_symm_apply ⟨_, hmap⟩)
    simp only [diagramPullback_apply, map_mul]
    rw [← hw]
    exact hf.positive_root _ ((diagramRoot_positive_iff S r).mpr hr) w _

/-- Pulling back a fundamental weight follows the inverse arm cycle. -/
theorem single_comp_diagram (i : Fin 4) :
    (Pi.single i (1 : ℤ)) ∘ typeD4DiagramPermutation =
      Pi.single (typeD4DiagramPermutation.symm i) 1 := by
  funext j
  by_cases h : j = typeD4DiagramPermutation.symm i
  · subst j
    simp
  · have h' : typeD4DiagramPermutation j ≠ i := by
      intro he
      exact h ((Equiv.eq_symm_apply _).mpr he)
    simp [h, h']

/-- A function of fundamental weight at arm `0` gives all three outer functions. -/
theorem outerRegularFunction_exists_of_zero (S : Geometry K) (f : K.PolynomialFunction)
    (hf : IsLeftHighestWeightRegularFunction S (Pi.single 0 1) f)
    (i : Fin 4) (hi : i ≠ 1) :
    ∃ g : K.PolynomialFunction, IsLeftHighestWeightRegularFunction S (Pi.single i 1) g := by
  have h3 : IsLeftHighestWeightRegularFunction S (Pi.single 3 1) (diagramPullback S f) := by
    simpa only [single_comp_diagram, show typeD4DiagramPermutation.symm 0 = 3 from rfl]
      using diagramPullback_highest S hf
  have h2 : IsLeftHighestWeightRegularFunction S (Pi.single 2 1)
      (diagramPullback S (diagramPullback S f)) := by
    simpa only [single_comp_diagram, show typeD4DiagramPermutation.symm 3 = 2 from rfl]
      using diagramPullback_highest S h3
  fin_cases i
  · exact ⟨f, hf⟩
  · exact (hi rfl).elim
  · exact ⟨_, h2⟩
  · exact ⟨_, h3⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
