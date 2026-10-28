module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.LeftContracts.Cells

/-!
# Finite highest lines and irreducibility with the source left characters

Matrix coefficients and the dual opposite highest vector turn actual finite
cell injectivity into highest-line detection and a spanning finite orbit.
The finite positive radical is a two-group, so every nonzero submodule meets
that line. This proves irreducibility on the original elementary subgroup.
All range and eigencharacter statements use the corrected left embedding;
the older raw-character APIs remain unchanged.
Source: Steinberg 13.3(a), GLS3 2.8.2.
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
universe u
variable {k:Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K:Variety k} [AlgebraicGroup K]

/-- Finite positive-cell evaluation detects the actual highest line. -/
theorem leftFiniteHighestLine_of_cellInjectivity (S : Geometry K) (n : ℕ)
    (hcell : LeftRestrictedCellInjectivity S n) : LeftFiniteHighestLine S n := by
  intro A a ha v hv w hw
  obtain ⟨tau, htau, htaur⟩ := rationalRepresentation_dual_exists A.action A.irreducible.1
  obtain ⟨l, hl, hlv⟩ := exists_opposite_dual_highestWeight S.bigCell S.maximalTorus
    A.action A.irreducible v (S.leftWeightEmbedding a) hv tau htau htaur
  let x := l v • w - l w • v
  have hfix (g : positiveUnipotent S n) :
      (A.restrict (S.inclusion n)).ρ g.val x = x := by
    change (A.action.action (S.inclusion n g.val)).1 (l v • w - l w • v) =
      l v • w - l w • v
    have hwg := hw g
    change (A.action.action (S.inclusion n g.val)).1 w = w at hwg
    rw [map_sub, map_smul, map_smul, hwg,
      highestVector_fixed_positiveRoots S A hv _ g.property]
  obtain ⟨f, hf, hfval⟩ := exists_rootCovariant_matrixCoefficient S tau htaur
    S.bigCell.data.opposite_witness l (S.leftWeightEmbedding a)⁻¹ hl (Module.Dual.eval k A.Space x)
  have hfzero : f = 0 := (hcell a ha).2 f hf (by
    intro g hg
    rw [hfval]
    change ((tau.action (S.inclusion n g)).1 l) x = 0
    rw [htau]
    have h := hfix (⟨g, hg⟩⁻¹)
    change (A.action.action (S.inclusion n g⁻¹)).1 x = x at h
    rw [map_inv] at h
    rw [h]
    simp [x, mul_comm])
  have hx : x = 0 := by
    apply matrixCoefficient_separates_irreducible A.action A.irreducible l hl.1.1 x
    intro g
    have hz : f g⁻¹ = 0 := congrArg (fun q : K.PolynomialFunction => q g⁻¹) hfzero
    rw [hfval] at hz
    change ((tau.action g⁻¹).1 l) x = 0 at hz
    rwa [htau, inv_inv] at hz
  apply Submodule.mem_span_singleton.mpr
  refine ⟨l w / l v, ?_⟩
  have heq := congrArg (fun y : A.Space => (l v)⁻¹ • y) (sub_eq_zero.mp hx)
  simpa [smul_smul, hlv, div_eq_mul_inv, mul_comm] using heq.symm

/-- Finite negative-cell evaluation makes the actual elementary highest
orbit span; no finite irreducibility assumption is used. -/
theorem leftFiniteHighestOrbitSpan_of_cellInjectivity (S : Geometry K) (n : ℕ)
    (hcell : LeftRestrictedCellInjectivity S n) : LeftFiniteHighestOrbitSpan S n := by
  intro A a ha v hv
  by_contra hne
  obtain ⟨l, hl, hker⟩ := (Submodule.span k (Set.range
    (fun g => (A.restrict (S.inclusion n)).ρ g v))).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr hne)
  obtain ⟨f, hf, hfval⟩ := exists_rootCovariant_matrixCoefficient S A.action A.irreducible.1
    S.bigCell.data.positive_witness v (S.leftWeightEmbedding a) hv l
  have hfzero : f = 0 := (hcell a ha).1 f hf (by
    intro g _
    rw [hfval]
    exact hker (Submodule.subset_span ⟨g, rfl⟩))
  apply hv.1.1
  apply matrixCoefficient_separates_irreducible A.action A.irreducible l hl v
  intro g
  have hz : f g = 0 := congrArg (fun q : K.PolynomialFunction => q g) hfzero
  rwa [hfval] at hz

/-- The actual finite highest line and orbit give restricted irreducibility. -/
theorem leftRestrictedIrreducibility_of_finiteHighestLine_of_orbitSpan
    (S:Geometry K) (n:ℕ) (hn:0<n)
    (hline:LeftFiniteHighestLine S n) (hspan:LeftFiniteHighestOrbitSpan S n) :
    LeftRestrictedIrreducibility S n := by
  intro A a ha hA
  obtain ⟨v,hv⟩:=hA
  let := S.elementary_finite n hn
  let : Nontrivial (A.restrict (S.inclusion n)) := inferInstanceAs (Nontrivial A.Space)
  exact irreducible_of_fixedLine_of_orbitSpan (A.restrict (S.inclusion n)).ρ
    (positiveUnipotent S n) (positiveUnipotent_isPGroup S n) v
    (hline A a ha v hv) (hspan A a ha v hv)

/-- Source left weights are separated by actual finite intertwiners once
highest lines and rank-one recovery have been proved. -/
theorem leftRestrictedSeparation_of_finiteHighestLine_of_weightRecovery
    (S : Geometry K) (n : ℕ)
    (hline : LeftFiniteHighestLine S n)
    (hweight : LeftHighestVectorWeightRecovery S n) : LeftRestrictedSeparation S n := by
  intro A C a b ha hb hA hC he
  obtain ⟨v, hv⟩ := hA
  obtain ⟨w, hw⟩ := hC
  obtain ⟨e⟩ := he
  have hmem : e v ∈ Submodule.span k ({w} : Set C.Space) := by
    apply hline C b hb w hw (e v)
    intro g
    calc
      (C.restrict (S.inclusion n)).ρ g.val (e v) =
          e ((A.restrict (S.inclusion n)).ρ g.val v) :=
        (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g.val v).symm
      _ = e v := congrArg e (highestVector_fixed_positiveUnipotent S A hv n g)
  have hhigh : HasHighWeight C.action S.bigCell.data.B S.torus (e v)
      (S.leftWeightEmbedding b) := by
    apply hasHighWeight_of_mem_highestLine S C hw
    · exact fun h => hv.1.1 (e.toLinearEquiv.map_eq_zero_iff.mp h)
    · exact hmem
  exact hweight A C a b ha hb v (e v) hv hhigh e rfl

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
