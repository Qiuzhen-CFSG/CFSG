module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.Spectral
public import Theory.AtlasPort.OtherSporadic.Conway.DerivedCrossTransitivity
public import Theory.AtlasPort.OtherSporadic.Conway.NormalGenerationElement
public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayOctadTransitivity
public import Mathlib.GroupTheory.PGroup

/-!
# Integral reduction of trace-eight Leech involutions

The odd number of Leech crosses supplies an invariant cross for every
square-one isometry. Transitivity and monomial recovery produce an actual
integral conjugator into the signed Golay permutation group. Its rational
trace is the signed sum over fixed coordinates, so trace eight requires at
least eight fixed coordinates. The diagonal case follows from transitivity
on octads. The existing sextet isometry also connects the marked nontrivial
monomial representative to a weight-eight sign inside the full lattice.

Source: Aschbacher, *Sporadic Groups* (1994), Sections 22–23 (cross geometry),
25.1–25.5, pp.132–134, and 49.3–49.4, pp.280–282. Section 25 uses the
complementary sign lift; these results retain the weight-eight, trace-positive
lift. The lattice, code, cross and sextet APIs are the existing attributed
ATLAS ports; no classification of Conway groups is assumed.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

theorem traceEight_exists_fixedCross (t : LeechIsometryGroup) (ht : t ^ 2 = 1) :
    ∃ X : LeechCross, crossAction t X = X := by
  let Z := Subgroup.zpowers t
  let : MulAction Z LeechCross :=
    MulAction.compHom LeechCross (crossRepresentation.comp Z.subtype)
  have hZ : IsPGroup 2 Z := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one ht)
  obtain ⟨X, hX⟩ := hZ.nonempty_fixed_point_of_prime_not_dvd_card LeechCross (by
    rw [leechCross_card]
    decide)
  exact ⟨X, MulAction.mem_fixedPoints.mp hX ⟨t, Subgroup.mem_zpowers t⟩⟩

theorem traceEight_exists_monomial (t : LeechIsometryGroup) (ht : TraceEightInvolution t) :
    ∃ m : GolayMonomialGroup, TraceEightInvolution (monomialEmbedding m) ∧
      ∃ h : LeechIsometryGroup, MulAut.conj h t = monomialEmbedding m := by
  obtain ⟨X, hX⟩ := traceEight_exists_fixedCross t ht.1
  let _ := full_cross_transitive
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq LeechIsometryGroup standardCross X
  change crossAction s standardCross = X at hs
  let k := s⁻¹ * t * s
  have hkX : crossAction k standardCross = standardCross := by
    rw [show k = s⁻¹ * (t * s) by dsimp [k]; group]
    rw [crossAction_mul, crossAction_mul, hs, hX, ← hs, ← crossAction_mul,
      inv_mul_cancel]
    rfl
  let m := recoverMonomial k hkX
  have hm : monomialEmbedding m = k := recoverMonomial_spec k hkX
  have hc : MulAut.conj s⁻¹ t = monomialEmbedding m := by simpa [k] using hm.symm
  refine ⟨m, ⟨?_, ?_⟩, s⁻¹, hc⟩
  · rw [← hc, ← map_pow, ht.1, map_one]
  · rw [← hc, rationalLeechTrace_conj, ht.2]

theorem octadSign_isConj_integralOctadSign (c : golay) (hc : hammingNorm c.val = 8) :
    IsConj (signIsometry c) integralOctadSign := by
  obtain ⟨g, hg⟩ := mathieu24_octad_transitive (support c.val) (support (golayBasis 0).val)
    ((octads_mem _).mpr ⟨c, hc, rfl⟩)
    ((octads_mem _).mpr ⟨golayBasis 0, golay_octad_basis.2 0, rfl⟩)
  have he : golayPermutationEquiv g c = golayBasis 0 := by
    apply Subtype.ext
    apply support_injective
    exact (coordinatePermutation_support g.val c.val).trans hg
  refine isConj_iff.mpr ⟨permutationEmbedding g, ?_⟩
  have h := DFunLike.congr_fun (sign_permutation_compatibility g) (Multiplicative.ofAdd c)
  change signIsometry (golayPermutationEquiv g c) =
    permutationEmbedding g * signIsometry c * (permutationEmbedding g)⁻¹ at h
  rw [he] at h
  exact h.symm

theorem traceEight_sign_isConj (c : golay) (hc : rationalLeechTrace (signIsometry c) = 8) :
    IsConj (signIsometry c) integralOctadSign := by
  apply octadSign_isConj_integralOctadSign
  rw [rationalLeechTrace_sign_weight] at hc
  have he : (hammingNorm c.val : ℚ) = 8 := by linarith
  exact_mod_cast he

theorem normalGenerationMonomial_isConj_integralOctadSign :
    IsConj (monomialEmbedding normalGenerationMonomial) integralOctadSign := by
  rw [normalGenerationMonomial_image]
  have hc : IsConj (signIsometry normalGenerationCode) normalGenerationConjugate :=
    isConj_iff.mpr ⟨zeta, rfl⟩
  exact hc.symm.trans (octadSign_isConj_integralOctadSign normalGenerationCode
    normalGenerationCode_weight)


theorem rationalExtension_monomial_apply (m : GolayMonomialGroup)
    (x : RationalCoordinates) (i : Omega) :
    rationalExtension (monomialEmbedding m).val x i =
      if m.left.toAdd.val i = 0 then x (m.right.val.symm i) else -x (m.right.val.symm i) := by
  let f : RationalCoordinates →ₗ[ℚ] RationalCoordinates := {
    toFun := fun x i => if m.left.toAdd.val i = 0 then
      x (m.right.val.symm i) else -x (m.right.val.symm i)
    map_add' := by intros; ext i; split_ifs <;> simp_all [add_comm]
    map_smul' := by intros; ext i; split_ifs <;> simp_all }
  have hf : f = (rationalExtension (monomialEmbedding m).val).toLinearMap := by
    apply rationalExtension_unique
    intro y
    ext j
    change (if m.left.toAdd.val j = 0 then (y.val (m.right.val.symm j) : ℚ)
      else -(y.val (m.right.val.symm j) : ℚ)) =
      ((if m.left.toAdd.val j = 0 then y.val (m.right.val.symm j)
      else -y.val (m.right.val.symm j) : ℤ) : ℚ)
    split_ifs <;> simp
  exact (congrArg (fun q : RationalCoordinates →ₗ[ℚ] RationalCoordinates => q x i) hf).symm

theorem rationalLeechTrace_monomial (m : GolayMonomialGroup) :
    rationalLeechTrace (monomialEmbedding m) =
      ∑ i : Omega, if m.right.val.symm i = i then
        (if m.left.toAdd.val i = 0 then 1 else -1) else 0 := by
  classical
  rw [rationalLeechTrace, LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ Omega)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change rationalExtension (monomialEmbedding m).val (Pi.single i 1) i = _
  rw [rationalExtension_monomial_apply]
  by_cases h : m.right.val.symm i = i <;> simp [h]

theorem traceEight_monomial_fixed_card (m : GolayMonomialGroup)
    (hm : rationalLeechTrace (monomialEmbedding m) = 8) :
    8 ≤ (Finset.univ.filter (fun i : Omega => m.right.val.symm i = i)).card := by
  classical
  have h : rationalLeechTrace (monomialEmbedding m) ≤
      ((Finset.univ.filter (fun i : Omega => m.right.val.symm i = i)).card : ℚ) := by
    rw [rationalLeechTrace_monomial]
    calc
      _ ≤ ∑ i : Omega, if m.right.val.symm i = i then (1 : ℚ) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> norm_num
      _ = _ := by simp
  rw [hm] at h
  exact_mod_cast h

theorem traceEight_monomial_involutive (m : GolayMonomialGroup)
    (hm : (monomialEmbedding m) ^ 2 = 1) : Function.Involutive m.right.val.symm := by
  have hs : m * m = 1 := monomialEmbedding_injective (by simpa [pow_two] using hm)
  intro i
  exact congrArg (fun n : GolayMonomialGroup => n.right.val.symm i) hs

theorem traceEight_monomial_sign_invariant (m : GolayMonomialGroup)
    (hm : (monomialEmbedding m) ^ 2 = 1) (i : Omega) :
    m.left.toAdd.val (m.right.val.symm i) = m.left.toAdd.val i := by
  have hs : m * m = 1 := monomialEmbedding_injective (by simpa [pow_two] using hm)
  have he := congrArg (fun n : GolayMonomialGroup => n.left.toAdd.val i) hs
  change m.left.toAdd.val i + m.left.toAdd.val (m.right.val.symm i) = 0 at he
  rcases bit_cases (m.left.toAdd.val i) with h | h <;>
    rcases bit_cases (m.left.toAdd.val (m.right.val.symm i)) with h' | h' <;> simp_all



end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
