module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedSubgroups
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedRootTorus.RootStability
public import Theory.AlgebraicGroup.RootSubgroups.TorusGeneratedNormalizer
public import Theory.AlgebraicGroup.Tori.UnipotentIntersection

/-!
# Fixed Borel factors in the supplied D4 geometry

A torus and a unipotent subgroup have trivial intersection. Thus a product
`t * u` in either supplied Borel has unique factors, and graph-field fixation
of that product fixes both factors once the torus is preserved. The root
invariance used here is proved directly from `Geometry` in `RootStability`.
The fixed Borel intersections and torus normalization are unconditional.

Torus invariance is also reduced to the geometric identification of the two
Borels as the normalizers of their unipotent radicals. Those identifications
remain explicit hypotheses; this module does not claim to construct them.

The requested unconditional generation by `fixedPositive`, `fixedNegative`
and `fixedTorus` still needs full fixed-point Bruhat decomposition and fixed
Weyl representatives from the two unipotents. These are separate from Borel
factorization and are not assumed as a generation certificate here.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 11.1 and 12.2--12.3(a).
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedRootTorus
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The actual torus and positive unipotent subgroup have trivial intersection. -/
theorem torus_disjoint_positive (S : Geometry K) :
    Disjoint S.torus.toSubgroup (RootSubgroupGenerated S.roots S.roots.positive) := by
  rw [disjoint_iff, ← S.bigCell.data.positive_witness.root_generated]
  exact subtorus_inf_unipotent_eq_bot S.torus _ S.maximalTorus.1
    S.bigCell.data.positive_witness.radical.2.1

/-- The actual torus and negative unipotent subgroup have trivial intersection. -/
theorem torus_disjoint_negative (S : Geometry K) :
    Disjoint S.torus.toSubgroup
      (RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive)) := by
  rw [disjoint_iff, ← S.bigCell.data.opposite_witness.root_generated]
  exact subtorus_inf_unipotent_eq_bot S.torus _ S.maximalTorus.1
    S.bigCell.data.opposite_witness.radical.2.1

private theorem fixed_factors {G : Type*} [Group G] (f : G →* G)
    (T U : Subgroup G) (hTU : Disjoint T U)
    (hT : ∀ t ∈ T, f t ∈ T) (hU : ∀ x ∈ U, f x ∈ U)
    {t u : G} (ht : t ∈ T) (hu : u ∈ U) (hfixed : f (t * u) = t * u) :
    f t = t ∧ f u = u := by
  have h := Subgroup.mul_injective_of_disjoint hTU
    (a₁ := (⟨f t, hT t ht⟩, ⟨f u, hU u hu⟩))
    (a₂ := (⟨t, ht⟩, ⟨u, hu⟩)) (by simpa only [map_mul] using hfixed)
  exact ⟨congrArg (fun p : T × U => (p.1 : G)) h,
    congrArg (fun p : T × U => (p.2 : G)) h⟩

/-- Uniqueness of torus--unipotent factors gives fixed positive Borel factors.
Only preservation of the torus is still required. -/
theorem positive_factors_fixed (S : Geometry K) (n : ℕ)
    (hT : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus)
    {t u : Variety.Point K} (ht : t ∈ S.torus)
    (hu : u ∈ RootSubgroupGenerated S.roots S.roots.positive)
    (hfixed : graphFieldEnd S n (t * u) = t * u) :
    graphFieldEnd S n t = t ∧ graphFieldEnd S n u = u := by
  apply fixed_factors (graphFieldEnd S n) S.torus.toSubgroup
    (RootSubgroupGenerated S.roots S.roots.positive) (torus_disjoint_positive S)
    hT _ ht hu hfixed
  intro x hx
  rw [← graphFieldEnd_map_positive S n]
  exact ⟨x, hx, rfl⟩

/-- The analogous fixed-factor argument for the opposite Borel. -/
theorem negative_factors_fixed (S : Geometry K) (n : ℕ)
    (hT : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus)
    {t u : Variety.Point K} (ht : t ∈ S.torus)
    (hu : u ∈ RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive))
    (hfixed : graphFieldEnd S n (t * u) = t * u) :
    graphFieldEnd S n t = t ∧ graphFieldEnd S n u = u := by
  apply fixed_factors (graphFieldEnd S n) S.torus.toSubgroup
    (RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive))
    (torus_disjoint_negative S) hT _ ht hu hfixed
  intro x hx
  rw [← graphFieldEnd_map_negative S n]
  exact ⟨x, hx, rfl⟩

/-- The literal positive Borel intersection inside the full fixed group. -/
def fixedBorel (S : Geometry K) (n : ℕ) :
    Subgroup (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :=
  S.bigCell.data.B.toSubgroup.comap
    (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype

/-- The literal opposite Borel intersection inside the full fixed group. -/
def fixedOppositeBorel (S : Geometry K) (n : ℕ) :
    Subgroup (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :=
  S.bigCell.data.Bopp.toSubgroup.comap
    (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype

/-- The positive Borel decomposition descends to the full fixed group
when the torus is preserved. There is no positive-exponent restriction. -/
theorem fixedBorel_decomposition (S : Geometry K) (n : ℕ)
    (hT : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus)
    (g : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :
    g ∈ fixedBorel S n ↔ ∃ t u, t ∈ fixedTorus S n ∧ u ∈ fixedPositive S n ∧ g = t * u := by
  constructor
  · intro hg
    obtain ⟨t, u, ht, hu, htu⟩ := (S.bigCell.positive_decomposition g).mp hg
    have hfixed : graphFieldEnd S n (t * u) = t * u := by
      rw [← htu]
      exact g.property
    obtain ⟨htf, huf⟩ := positive_factors_fixed S n hT ht hu hfixed
    exact ⟨⟨t, htf⟩, ⟨u, huf⟩, ht, hu, Subtype.ext htu⟩
  · rintro ⟨t, u, ht, hu, rfl⟩
    exact (S.bigCell.positive_decomposition _).mpr ⟨t, u, ht, hu, rfl⟩

/-- The opposite Borel decomposition descends under the same torus premise. -/
theorem fixedOppositeBorel_decomposition (S : Geometry K) (n : ℕ)
    (hT : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus)
    (g : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :
    g ∈ fixedOppositeBorel S n ↔
      ∃ t u, t ∈ fixedTorus S n ∧ u ∈ fixedNegative S n ∧ g = t * u := by
  constructor
  · intro hg
    obtain ⟨t, u, ht, hu, htu⟩ := (S.bigCell.negative_decomposition g).mp hg
    have hfixed : graphFieldEnd S n (t * u) = t * u := by
      rw [← htu]
      exact g.property
    obtain ⟨htf, huf⟩ := negative_factors_fixed S n hT ht hu hfixed
    exact ⟨⟨t, htf⟩, ⟨u, huf⟩, ht, hu, Subtype.ext htu⟩
  · rintro ⟨t, u, ht, hu, rfl⟩
    exact (S.bigCell.negative_decomposition _).mpr ⟨t, u, ht, hu, rfl⟩

/-- Under torus preservation, the fixed Borel is generated by its actual
fixed torus and positive unipotent subgroup. -/
theorem fixedBorel_eq_sup (S : Geometry K) (n : ℕ)
    (hT : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus) :
    fixedBorel S n = fixedTorus S n ⊔ fixedPositive S n := by
  apply le_antisymm
  · intro g hg
    obtain ⟨t, u, ht, hu, rfl⟩ := (fixedBorel_decomposition S n hT g).mp hg
    exact Subgroup.mul_mem_sup ht hu
  · apply sup_le
    · intro t ht
      exact (fixedBorel_decomposition S n hT t).mpr
        ⟨t, 1, ht, (fixedPositive S n).one_mem, by simp⟩
    · intro u hu
      exact (fixedBorel_decomposition S n hT u).mpr
        ⟨1, u, (fixedTorus S n).one_mem, hu, by simp⟩

/-- Under torus preservation, the opposite fixed Borel has the analogous generators. -/
theorem fixedOppositeBorel_eq_sup (S : Geometry K) (n : ℕ)
    (hT : ∀ t ∈ S.torus, graphFieldEnd S n t ∈ S.torus) :
    fixedOppositeBorel S n = fixedTorus S n ⊔ fixedNegative S n := by
  apply le_antisymm
  · intro g hg
    obtain ⟨t, u, ht, hu, rfl⟩ := (fixedOppositeBorel_decomposition S n hT g).mp hg
    exact Subgroup.mul_mem_sup ht hu
  · apply sup_le
    · intro t ht
      exact (fixedOppositeBorel_decomposition S n hT t).mpr
        ⟨t, 1, ht, (fixedNegative S n).one_mem, by simp⟩
    · intro u hu
      exact (fixedOppositeBorel_decomposition S n hT u).mpr
        ⟨1, u, (fixedTorus S n).one_mem, hu, by simp⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedRootTorus

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedRootTorus
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Identifying the two Borels as unipotent normalizers implies invariance
of their intersection, the actual supplied torus. The two normalizer
identifications are geometric premises still to be constructed. -/
theorem graphFieldEnd_map_torus_of_unipotent_normalizers (S : Geometry K) (n : ℕ)
    (hpos : Subgroup.normalizer (RootSubgroupGenerated S.roots S.roots.positive : Set (Variety.Point K)) =
      S.bigCell.data.B.toSubgroup)
    (hneg : Subgroup.normalizer (RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive) : Set (Variety.Point K)) =
      S.bigCell.data.Bopp.toSubgroup) :
    S.torus.toSubgroup.map (graphFieldEnd S n) = S.torus.toSubgroup := by
  let σ : Variety.Point K →* Variety.Point K := graphFieldEnd S n
  have hp : (RootSubgroupGenerated S.roots S.roots.positive).map σ =
      RootSubgroupGenerated S.roots S.roots.positive := graphFieldEnd_map_positive S n
  have hm : (RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive)).map σ =
      RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive) :=
    graphFieldEnd_map_negative S n
  have hbij : Function.Bijective σ :=
    (S.frobenius_bijective.iterate n).comp S.diagram.toMulEquiv.bijective
  have hB : S.bigCell.data.B.toSubgroup.map σ =
      S.bigCell.data.B.toSubgroup := by
    rw [← hpos, Subgroup.map_normalizer_eq_of_bijective _ hbij,
      hp]
  have hBopp : S.bigCell.data.Bopp.toSubgroup.map σ =
      S.bigCell.data.Bopp.toSubgroup := by
    rw [← hneg, Subgroup.map_normalizer_eq_of_bijective _ hbij,
      hm]
  change S.torus.toSubgroup.map σ = S.torus.toSubgroup
  rw [← S.bigCell.intersection_eq_torus, Subgroup.map_inf _ _ _ hbij.injective, hB, hBopp]

/-- Exact torus invariance and proved root invariance give positive Borel invariance. -/
theorem graphFieldEnd_map_borel (S : Geometry K) (n : ℕ)
    (hT : S.torus.toSubgroup.map (graphFieldEnd S n) = S.torus.toSubgroup) :
    S.bigCell.data.B.toSubgroup.map (graphFieldEnd S n) =
      S.bigCell.data.B.toSubgroup := by
  rw [S.bigCell.data.positive_witness.torus_unipotent_generate,
    S.bigCell.data.positive_witness.root_generated]
  exact (Subgroup.map_sup _ _ (graphFieldEnd S n)).trans
    (congrArg₂ (· ⊔ ·) hT (graphFieldEnd_map_positive S n))

/-- Exact torus invariance also gives opposite Borel invariance. -/
theorem graphFieldEnd_map_oppositeBorel (S : Geometry K) (n : ℕ)
    (hT : S.torus.toSubgroup.map (graphFieldEnd S n) = S.torus.toSubgroup) :
    S.bigCell.data.Bopp.toSubgroup.map (graphFieldEnd S n) =
      S.bigCell.data.Bopp.toSubgroup := by
  rw [S.bigCell.data.opposite_witness.torus_unipotent_generate,
    S.bigCell.data.opposite_witness.root_generated]
  exact (Subgroup.map_sup _ _ (graphFieldEnd S n)).trans
    (congrArg₂ (· ⊔ ·) hT (graphFieldEnd_map_negative S n))

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedRootTorus

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedRootTorus
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The two literal fixed Borels intersect in exactly the fixed torus. -/
theorem fixedBorel_inf_opposite (S : Geometry K) (n : ℕ) :
    fixedBorel S n ⊓ fixedOppositeBorel S n = fixedTorus S n := by
  change S.bigCell.data.B.toSubgroup.comap _ ⊓ S.bigCell.data.Bopp.toSubgroup.comap _ = _
  rw [← Subgroup.comap_inf, S.bigCell.intersection_eq_torus]
  rfl

/-- The actual fixed torus normalizes the actual fixed positive unipotents. -/
theorem fixedTorus_le_positive_normalizer (S : Geometry K) (n : ℕ) :
    fixedTorus S n ≤ Subgroup.normalizer
      (fixedPositive S n : Set (graphFieldFixedSubgroup
        S.diagram.toMulEquiv S.frobenius.onPoints n)) := by
  exact (Subgroup.comap_mono
    (torus_le_rootSubgroupGenerated_normalizer S.roots S.realized S.roots.positive)).trans
      (Subgroup.le_normalizer_comap _)

/-- The actual fixed torus normalizes the actual fixed negative unipotents. -/
theorem fixedTorus_le_negative_normalizer (S : Geometry K) (n : ℕ) :
    fixedTorus S n ≤ Subgroup.normalizer
      (fixedNegative S n : Set (graphFieldFixedSubgroup
        S.diagram.toMulEquiv S.frobenius.onPoints n)) := by
  exact (Subgroup.comap_mono (torus_le_rootSubgroupGenerated_normalizer S.roots S.realized
    (S.roots.neg ⁻¹' S.roots.positive))).trans (Subgroup.le_normalizer_comap _)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedRootTorus
