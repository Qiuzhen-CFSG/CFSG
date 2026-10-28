module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.GeometryInterface
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.KernelModel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Counting


/-!
# The relative centralizer of the octad restriction kernel

Five explicit shortened Golay words distinguish each complementary coordinate
from all other coordinates. Commutation with their sign changes therefore
forces an integral isometry to preserve every complementary axis up to sign.
Its square fixes those axes and hence belongs to the literal Golay monomial
group. The permutation component fixes the disjoint native octad 321 pointwise,
so the native octad two-core theorem makes it a two-element. The remaining
Golay sign component has exponent two. Thus the relative centralizer is a
two-group, even without assuming that the restriction kernel is extraspecial.

The final application discharges the relative-centralizer premise in the
kernel bound for conjugation on the actual central quotient Q/Z(Q).

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5, pp.132–134.
The explicit Golay basis, Leech monomial embedding and coordinate comparison
are the existing CFSG ATLAS ports of Gerald Höhn and ATLAS contributors,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.Realization
open KernelModel

private def separatingWords : Fin 5 → golay :=
  ![golayBasis 0 + golayBasis 3 + golayBasis 4 + golayBasis 6,
    golayBasis 1 + golayBasis 2 + golayBasis 5 + golayBasis 7,
    golayBasis 1 + golayBasis 2 + golayBasis 3 + golayBasis 4 + golayBasis 5 + golayBasis 9,
    golayBasis 8 + golayBasis 10, golayBasis 11]

private def separatingVectors : Fin 5 → BinaryWord :=
  ![golayGenerators 0 + golayGenerators 3 + golayGenerators 4 + golayGenerators 6,
    golayGenerators 1 + golayGenerators 2 + golayGenerators 5 + golayGenerators 7,
    golayGenerators 1 + golayGenerators 2 + golayGenerators 3 + golayGenerators 4 +
      golayGenerators 5 + golayGenerators 9,
    golayGenerators 8 + golayGenerators 10, golayGenerators 11]

private theorem separatingWords_coe (k : Fin 5) :
    (separatingWords k).val = separatingVectors k := by
  fin_cases k <;> simp [separatingWords, separatingVectors, golayBasis_coe]

private theorem separatingVectors_vanish :
    ∀ k i, golayGenerators 0 i ≠ 0 → separatingVectors k i = 0 := by
  decide +kernel

private theorem separatingVectors_separate :
    ∀ i j, golayGenerators 0 i = 0 → i ≠ j →
      ∃ k, separatingVectors k i ≠ separatingVectors k j := by
  decide +kernel

private def separatingSigns (k : Fin 5) : signCode :=
  ⟨separatingWords k, fun i => by
    rw [separatingWords_coe]
    exact separatingVectors_vanish k i.val (by simpa only [golayBasis_coe] using i.prop)⟩

private theorem signs_separate (i j : Omega) (hi : (golayBasis 0).val i = 0)
    (hij : i ≠ j) : ∃ c : signCode, c.val.val i ≠ c.val.val j := by
  obtain ⟨k, hk⟩ := separatingVectors_separate i j (by simpa only [golayBasis_coe] using hi) hij
  refine ⟨separatingSigns k, ?_⟩
  change (separatingWords k).val i ≠ (separatingWords k).val j
  simpa only [separatingWords_coe] using hk

private def signKernel (c : signCode) : action.ker :=
  kernelEquiv (SemidirectProduct.inl (Multiplicative.ofAdd c))

private theorem signKernel_apply (c : signCode) (x : leech) (i : Omega) :
    ((signKernel c).val.val.val x).val i =
      if c.val.val i = 0 then x.val i else -x.val i := rfl

private theorem signKernel_axis (c : signCode) (i : Omega) :
    (signKernel c).val.val.val (coordinateEight i) =
      if c.val.val i = 0 then coordinateEight i else -coordinateEight i := by
  apply Subtype.ext
  funext j
  rw [signKernel_apply]
  by_cases hj : j = i
  · subst j; split_ifs <;> rfl
  · split_ifs <;> simp [coordinateEight, coordinateVector, hj]

private theorem centralizer_axis_support
    (g : Subgroup.centralizer (action.ker : Set centralizer))
    (i : Omega) (hi : (golayBasis 0).val i = 0) (j : Omega) (hji : j ≠ i) :
    (g.val.val.val (coordinateEight i)).val j = 0 := by
  obtain ⟨c, hc⟩ := signs_separate i j hi hji.symm
  have he := (Subgroup.mem_centralizer_iff.mp g.prop) (signKernel c).val (signKernel c).prop
  have he' := congrArg (fun a : centralizer => (a.val.val (coordinateEight i)).val j) he
  change ((signKernel c).val.val.val (g.val.val.val (coordinateEight i))).val j =
    (g.val.val.val ((signKernel c).val.val.val (coordinateEight i))).val j at he'
  rw [signKernel_apply, signKernel_axis] at he'
  rcases bit_cases (c.val.val i) with hi' | hi' <;>
    rcases bit_cases (c.val.val j) with hj' | hj'
  all_goals simp [hi', hj'] at hc he'
  all_goals omega

private theorem centralizer_axis_signed
    (g : Subgroup.centralizer (action.ker : Set centralizer))
    (i : Omega) (hi : (golayBasis 0).val i = 0) :
    g.val.val.val (coordinateEight i) = coordinateEight i ∨
      g.val.val.val (coordinateEight i) = -coordinateEight i := by
  let x := g.val.val.val (coordinateEight i)
  have hx : x.val = coordinateVector i (x.val i) := by
    funext j
    by_cases hji : j = i
    · subst j; simp [coordinateVector]
    · simp [coordinateVector, hji, x, centralizer_axis_support g i hi j hji]
  have hn := g.val.val.prop (coordinateEight i) (coordinateEight i)
  change integerDot x.val x.val =
    integerDot (coordinateVector i 8) (coordinateVector i 8) at hn
  rw [hx, integerDot_coordinateVector, integerDot_coordinateVector] at hn
  simp only [coordinateVector, Pi.single_eq_same] at hn
  have hv : x.val i = 8 ∨ x.val i = -8 := by
    have : (x.val i - 8) * (x.val i + 8) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h <;> omega
  rcases hv with hv | hv
  · left; apply Subtype.ext; exact hx.trans (congrArg (coordinateVector i) hv)
  · right; apply Subtype.ext
    rw [hx, hv]
    simp [coordinateEight, coordinateVector, Pi.single_neg]

private theorem centralizer_square_fixes_axis
    (g : Subgroup.centralizer (action.ker : Set centralizer))
    (i : Omega) (hi : (golayBasis 0).val i = 0) :
    (g.val.val ^ 2).val (coordinateEight i) = coordinateEight i := by
  change g.val.val.val (g.val.val.val (coordinateEight i)) = coordinateEight i
  rcases centralizer_axis_signed g i hi with h | h
  · rw [h, h]
  · rw [h, map_neg, h, neg_neg]

private def complementaryOctad : Sporadic.Mathieu.M24LocalGeometry.Octad :=
  ⟨Sporadic.Mathieu.m24BlockAt 321,
    Finset.mem_image.mpr ⟨321, Finset.mem_univ _, rfl⟩⟩

private theorem complementaryOctad_disjoint (i : Fin 24) (hi : i ∈ complementaryOctad.val) :
    (golayBasis 0).val (MathieuCode.atlasPointEquiv.symm i) = 0 := by
  rw [golayBasis_coe]
  revert i
  decide +kernel

private theorem centralizer_square_monomial
    (g : Subgroup.centralizer (action.ker : Set centralizer)) :
    g.val.val ^ 2 ∈ monomialSubgroup := by
  apply coordinateEight_fixer_mem_monomial _ ((0,0),0)
  exact centralizer_square_fixes_axis g _ (by rw [golayBasis_coe]; decide +kernel)

private theorem monomial_square_permutation
    (g : Subgroup.centralizer (action.ker : Set centralizer)) (m : GolayMonomialGroup)
    (hm : monomialEmbedding m = g.val.val ^ 2) :
    ∃ k : ℕ, m.right ^ (2 ^ k) = 1 := by
  let n := Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv.symm m.right
  have hn : n ∈ MathieuCode.octadPointwiseKernel complementaryOctad := by
    rw [MathieuCode.mem_octadPointwiseKernel]
    intro i hi
    have hfix := (monomial_axis_fixed_iff m (MathieuCode.atlasPointEquiv.symm i)).mp
      (by rw [hm]; exact centralizer_square_fixes_axis g _ (complementaryOctad_disjoint i hi))
    have hh : (Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv n).val
        (MathieuCode.atlasPointEquiv.symm i) = MathieuCode.atlasPointEquiv.symm i := by
      simpa only [n, MulEquiv.apply_symm_apply] using hfix.1
    change MathieuCode.atlasPointEquiv.symm
      (n.val (MathieuCode.atlasPointEquiv (MathieuCode.atlasPointEquiv.symm i))) = _ at hh
    rw [MathieuCode.atlasPointEquiv.apply_symm_apply] at hh
    exact MathieuCode.atlasPointEquiv.symm.injective hh
  have hp : IsPGroup 2 (MathieuCode.octadPointwiseKernel complementaryOctad) := by
    rw [← MathieuCode.octad_core_map_eq_pointwise]
    exact pCore_isPGroup.map _
  obtain ⟨k, hk⟩ := hp ⟨n, hn⟩
  have hnk : n ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  have hmk := congrArg Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv hnk
  simpa only [map_pow, map_one, n, MulEquiv.apply_symm_apply] using hmk

private theorem monomial_sq_of_right_one (m : GolayMonomialGroup) (hm : m.right = 1) :
    m ^ 2 = 1 := by
  have he : m = SemidirectProduct.inl m.left := by
    have h := SemidirectProduct.inl_left_mul_inr_right m
    simpa only [hm, map_one, mul_one] using h.symm
  rw [he, ← map_pow]
  have hs : m.left ^ 2 = 1 := by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    ext i
    change m.left.toAdd.val i + m.left.toAdd.val i = 0
    rw [← two_mul, show (2 : Bit) = 0 by decide, zero_mul]
  rw [hs, map_one]

/-- The relative centralizer in the integral octad centralizer is a two-group. -/
theorem relativeCentralizer_isTwoGroup_unconditional :
    IsPGroup 2 (Subgroup.centralizer (action.ker : Set centralizer)) := by
  intro g
  obtain ⟨m, hm⟩ := centralizer_square_monomial g
  obtain ⟨k, hk⟩ := monomial_square_permutation g m hm
  have hr : (m ^ (2 ^ k)).right = 1 :=
    (map_pow (SemidirectProduct.rightHom : GolayMonomialGroup →* Mathieu24CodeModel) m
      (2 ^ k)).trans hk
  have hp : m ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ, pow_mul]
    exact monomial_sq_of_right_one _ hr
  have hg : (g.val.val ^ 2) ^ (2 ^ (k + 1)) = 1 := by
    simpa only [map_pow, hm, map_one] using congrArg monomialEmbedding hp
  refine ⟨k + 2, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change g.val.val ^ (2 ^ (k + 2)) = 1
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ, Nat.mul_comm, pow_mul]
  exact hg

set_option linter.unusedVariables false in
/-- Extraspeciality is retained for the quotient-action consumer. The relative
centralizer bound itself follows already from the literal Golay kernel. -/
theorem relativeCentralizer_isTwoGroup (hExtra : IsExtraspecial 2 action.ker) :
    IsPGroup 2 (Subgroup.centralizer (action.ker : Set centralizer)) :=
  relativeCentralizer_isTwoGroup_unconditional

/-- Discharge the centralizer premise in the actual quotient-action kernel bound. -/
theorem kernelQuotientAction_isTwoGroup (hExtra : IsExtraspecial 2 action.ker) :
    IsPGroup 2 kernelQuotientAction.ker :=
  kernelQuotientAction_isTwoGroup_of_centralizer hExtra (relativeCentralizer_isTwoGroup hExtra)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.Realization
