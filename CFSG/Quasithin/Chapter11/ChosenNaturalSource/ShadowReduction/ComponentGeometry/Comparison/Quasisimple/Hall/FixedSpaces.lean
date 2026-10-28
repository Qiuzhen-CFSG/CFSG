module
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectSubgroups
public import Theory.Representation.G2NaturalTransitivity
public import Theory.Representation.G2NaturalExtensions.FixedSpaces
public import Theory.AtlasPort.LinearGroups.G2.PerfectSubgroups

/-!
# Rank-two actors on the three natural modules in 11.4.2

Every subgroup of odd-prime rank at least two fixes only zero on the natural
SL₃, Sp₄ or G₂ module. Nonzero-vector transitivity transports a proposed
fixed vector to the standard vector. Its stabilizer has a two-group kernel
and SL₂ quotient, hence odd-prime rank at most one. In G₂, norm preservation
lifts fixed natural classes to trace-zero octonions and identifies the
stabilizer with the genuine long-root local group. No torus marking or
Sylow-normalization hypothesis is imposed on the actor.

The chosen-flag Hall endpoint transports these calculations through the
original central quotient, retaining all covering kernels.
Source: Aschbacher--Smith, 11.4.2, printed p.777. Imported octonion geometry
retains the ATLAS attribution in LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff; no additional ATLAS source is copied here.
-/

@[expose] public noncomputable section
open Subgroup Matrix Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall

private theorem fixed_zero_of_rank_one_stabilizer
    {k A W : Type*} [Field k] [Group A] [Finite A] [AddCommGroup W] [Module k W]
    (ρ : Representation k A W) (C : Subgroup A) (w : W)
    (ht : ∀ v : W, v ≠ 0 → ∃ g : A, ρ g v = w)
    (hc : ∀ a : A, ρ a w = w → a ∈ C)
    {p : ℕ} [Fact p.Prime] (hrC : primeRank p C ≤ 1)
    (B : Subgroup A) (hr : 2 ≤ primeRank p B)
    (v : W) (hv : ∀ a ∈ B, ρ a v = v) : v = 0 := by
  by_contra hn
  obtain ⟨g,hg⟩ := ht v hn
  let j := (MulAut.conj g).toMonoidHom.comp B.subtype
  have hj (a : B) : j a ∈ C := by
    apply hc
    change ρ (g * (a : A) * g⁻¹) w = w
    rw [←hg]
    simp [map_mul, Module.End.mul_apply, hv a a.property]
  let f : B →* C := j.codRestrict C hj
  have hf : Function.Injective f := by
    intro a b hab
    exact B.subtype_injective ((MulAut.conj g).injective (congrArg Subtype.val hab))
  have hb := (Theory.GroupTheory.primeRank_le_of_injective p f hf).trans hrC
  omega

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every odd-prime rank-two subgroup of SL3 fixes only zero in the natural
three-space, retaining the full special-linear covering center. -/
theorem sl3_fixed_eq_zero {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (B : Subgroup SL(3,F)) (hr : 2 ≤ primeRank p B)
    (v : Fin 3 → F) (hv : ∀ a ∈ B, specialLinearNatural 3 a v = v) : v = 0 := by
  let C := Matrix.PSL3.LinearThree.pointLocalSL F
  have hc : primeRank p C ≤ 1 := by
    rw [← primeRank_quotient_eq_of_isTwoGroup p hp (pCore 2 C) pCore_isPGroup,
      primeRank_equiv p (Matrix.PSL3.LinearThree.pointLocalSLCoreQuotientEquiv F)]
    exact Matrix.SL2.binary_odd_primeRank_le_one hp
  apply fixed_zero_of_rank_one_stabilizer (specialLinearNatural (k := F) 3)
    C ![1,0,0] _ _ hc B hr v hv
  · intro x hx
    apply Matrix.SpecialLinearGroup.exists_mulVec_eq_three x ![1,0,0] hx
    intro h
    have := congrFun h 0
    simp at this
  · intro a ha
    apply (Matrix.PSL3.LinearThree.mem_pointLocalSL_iff F a).mpr
    change a.val *ᵥ ![1,0,0] = ![1,0,0] at ha
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    have h2 := congrFun ha 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using
      And.intro h0 (And.intro h1 h2)

/-- The natural symplectic four-space has no nonzero fixed vector under an
odd-prime rank-two subgroup, by its actual point stabilizer quotient SL2. -/
theorem sp4_fixed_eq_zero {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (B : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hr : 2 ≤ primeRank p B)
    (v : Theory.SpecificGroups.SymplecticFour.Vector F)
    (hv : ∀ a ∈ B, symplecticNatural 2 a v = v) : v = 0 := by
  apply fixed_zero_of_rank_one_stabilizer (symplecticNatural (k := F) 2)
    Theory.SpecificGroups.SymplecticFour.pointLocal
    (Theory.SpecificGroups.SymplecticFour.e 0) _ _
    (Theory.SpecificGroups.SymplecticFour.pointLocal_odd_primeRank_le_one hp) B hr v hv
  · intro x hx
    apply Theory.SpecificGroups.SymplecticFour.TwoLocalCover.nonzero_vector_transitive hx
    intro h
    have := congrFun h (.inl 0)
    simp [Theory.SpecificGroups.SymplecticFour.e] at this
  · intro a ha
    exact (Theory.SpecificGroups.SymplecticFour.mem_pointLocal_iff_fixed a).mpr ha

/-- The genuine octonion natural quotient has the same bound: fixed vectors
lift to trace-zero octonions, whose stabilizer is the long-root local group. -/
theorem g2_fixed_eq_zero {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (B : Subgroup (Atlas.G2.Model F)) (hr : 2 ≤ primeRank p B)
    (v : Atlas.G2.Natural.Space F)
    (hv : ∀ a ∈ B, Atlas.G2.Natural.action F a v = v) : v = 0 := by
  let w : Atlas.G2.Natural.TraceZero F :=
    ⟨Atlas.SplitOctonion.basisVector 0, by simp [Atlas.G2.Natural.mem_traceZero,
      Atlas.SplitOctonion.trace, Atlas.SplitOctonion.basisVector]⟩
  have hw : Atlas.G2.Natural.mk F w ≠ 0 := by
    intro hz
    obtain ⟨r,hr⟩ := (Atlas.G2.Natural.mk_eq_zero_iff F w).mp hz
    have he := congrFun hr 0
    simp [w, Atlas.SplitOctonion.unit, Atlas.SplitOctonion.basisVector] at he
  apply fixed_zero_of_rank_one_stabilizer (Atlas.G2.Natural.action F)
    Atlas.G2.LieParabolicSetup.local₂ (Atlas.G2.Natural.mk F w) _ _
    (Atlas.G2.PerfectSubgroups.local₂_odd_primeRank_le_one hp) B hr v hv
  · intro x hx
    exact Atlas.G2.Natural.action_transitive hx hw
  · intro a ha
    rw [Atlas.G2.LieParabolicSetup.local₂_eq_fixingFirstVector]
    exact congrArg Subtype.val
      (Atlas.G2.Natural.Extensions.traceZero_fixed_of_natural_fixed a w ha)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
