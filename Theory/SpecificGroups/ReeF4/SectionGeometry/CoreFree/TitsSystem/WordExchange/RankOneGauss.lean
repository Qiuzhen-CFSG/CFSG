module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.WordExchange.RootFactors
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.FixedNormalizer
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.SplitNormalForm
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.LinearCover.RankOne

/-!
# Rank-one Gauss decomposition in the actual fixed Ree group

For the linear block the defining three-root Weyl word gives the Gauss
factorization, and the Borel–normalizer intersection identifies its torus
factor. For the Suzuki block, the restricted split Levi normal form and the
complete fixed-normalizer calculation descend to the two actual fixed Bruhat
cells. The identity cell is excluded by separation of the negative block
from the Borel. This retains the complete fixed torus and every positive
B₂ root without requiring a separate ambient Gauss matrix identity.

Source: GLS3 2.3.4–5 and §2.4, Table 2.4 types V and VI,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LargeLocalSeeds Parabolics Parabolics.Binary.FixedGeometry
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.FixedCollection
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open LocalBlockInput.PairRigidity.LocalIndices LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem local_weyl_inv {m : ℕ} (d : LocalBlockInput m) (s : Side) :
    (relativeWeyl d s)⁻¹ = relativeWeyl d s := by
  apply d.modelEquiv.injective
  rw [map_inv, wordExchange_modelEquiv_relativeWeyl]
  exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using weylLift_sq m s)

private theorem local_conj_block {m : ℕ} (d : LocalBlockInput m) (s : Side)
    {x : d.fixedGroup} (hx : x ∈ simpleBlock d s true) :
    relativeWeyl d s * x * (relativeWeyl d s)⁻¹ ∈ simpleBlock d s false := by
  have h : splitSimpleBlock m s true ≤ (splitSimpleBlock m s false).comap
      (MulAut.conj (relativeWeyl d s).val).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    change (relativeWeyl d s).val * rootGeneratorInGroup m r t *
      (relativeWeyl d s).val⁻¹ ∈ splitSimpleBlock m s false
    rw [relativeWeyl_conj_block_root d s true r t hr]
    exact subset_closure ⟨_, t, (isSimpleBlockRoot_neg_iff s true r).mpr hr, rfl⟩
  exact h hx

private theorem local_suzuki_gauss {m : ℕ} (d : LocalBlockInput m)
    {x : d.fixedGroup} (hx : x ∈ simpleBlock d .suzuki true) (hx1 : x ≠ 1) :
    ∃ a ∈ simpleBlock d .suzuki true,
      ∃ t ∈ (splitTorus m).subgroupOf d.fixedGroup,
      ∃ y ∈ simpleBlock d .suzuki true,
        relativeWeyl d .suzuki * x * (relativeWeyl d .suzuki)⁻¹ =
          a * t * relativeWeyl d .suzuki * y := by
  let v := relativeWeyl d .suzuki
  let g := v * x * v⁻¹
  have hgneg : g ∈ simpleBlock d .suzuki false := local_conj_block d .suzuki hx
  have hg : g ∈ fixedLevi d .suzuki := simpleBlock_le_fixedLevi d .suzuki false hgneg
  have hg1 : g ≠ 1 := by
    intro he
    apply hx1
    have hh := congrArg (fun z => v⁻¹ * z * v) he
    simpa only [g, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, one_mul] using hh
  obtain ⟨a, ha, y, hy, n, e, he⟩ := suzukiLeviBruhatCover_of_normalForms d
    (suzukiSplitLeviNormalForm m) (suzuki_fixedNormalizerForm d) g hg
  let t : d.fixedGroup := ⟨SuzukiGaussData.torusFactor n, SuzukiNormalizer.torusFactor_fixed d n⟩
  have ht : t ∈ (splitTorus m).subgroupOf d.fixedGroup := SuzukiGaussData.torusFactor_mem n
  have heq : g = a * t * (if e then v else 1) * y := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, apply_ite, Subgroup.coe_one] using he
  cases e with
  | false =>
    have hB : g ∈ rootBorel d := by
      rw [heq]
      simpa only [Bool.false_eq_true, ↓reduceIte, mul_one] using
        (rootBorel d).mul_mem
          ((rootBorel d).mul_mem
            ((show standardUnipotent d ≤ rootBorel d from comap_mono le_sup_left)
              (simpleBlock_positive_le d .suzuki ha))
            (suzukiPanelTorus_le_borel d ht))
          ((show standardUnipotent d ≤ rootBorel d from comap_mono le_sup_left)
            (simpleBlock_positive_le d .suzuki hy))
    exact (hg1 (Subgroup.disjoint_def.mp
      (negativeBlock_disjoint_rootBorel d (splitTorus_eq_diagonalTorus m) .suzuki) hgneg hB)).elim
  | true => exact ⟨a, ha, t, ht, y, hy, heq⟩

private theorem local_linear_weyl {m : ℕ} (d : LocalBlockInput m) :
    relativeWeyl d .linear = linearPanelWeyl d 1 := by
  apply Subtype.ext
  rw [relativeWeyl_val, linearPanelWeyl_split]
  simp [simpleWord, sideWord]

private theorem local_linear_weyl_mem {m : ℕ} (d : LocalBlockInput m)
    (t : (CoefficientField m)ˣ) : (linearPanelWeyl d t).val ∈ splitNormalizerWords m := by
  rw [linearPanelWeyl_split]
  exact mul_mem (weylWord_mem_splitNormalizerWords m _ t)
    (weylWord_mem_splitNormalizerWords m _
      (Units.map (rootFieldEnd m (typeF4SimpleRootIndex 0)).toMonoidHom t))

private theorem local_linear_gauss {m : ℕ} (d : LocalBlockInput m)
    {x : d.fixedGroup} (hx : x ∈ simpleBlock d .linear true) (hx1 : x ≠ 1) :
    ∃ a ∈ simpleBlock d .linear true,
      ∃ t ∈ (splitTorus m).subgroupOf d.fixedGroup,
      ∃ y ∈ simpleBlock d .linear true,
        relativeWeyl d .linear * x * (relativeWeyl d .linear)⁻¹ =
          a * t * relativeWeyl d .linear * y := by
  obtain ⟨z, rfl⟩ := linearElement_surjective d true hx
  have hz : z ≠ 0 := by intro he; exact hx1 (he ▸ linearElement_zero d true)
  let q : (CoefficientField m)ˣ := (Units.mk0 z hz)⁻¹
  let a := linearElement d true q
  let v := linearPanelWeyl d 1
  let w := linearPanelWeyl d q
  let t := w * v⁻¹
  have ht : t ∈ (splitTorus m).subgroupOf d.fixedGroup := by
    change t.val ∈ splitTorus m
    rw [← splitBorel_inf_normalizerWords]
    change t.val ∈ splitBorel m ∧ t.val ∈ splitNormalizerWords m
    constructor
    · have h := (rootBorel d).inv_mem (linearPanelWeyl_ratio_mem_borel d q)
      change ((linearPanelWeyl d 1)⁻¹ * linearPanelWeyl d q)⁻¹ ∈ rootBorel d at h
      change t ∈ rootBorel d
      simpa only [t, w, v, mul_inv_rev, inv_inv, linearPanelWeyl_inv] using h
    · exact mul_mem (local_linear_weyl_mem d q)
        (inv_mem (local_linear_weyl_mem d 1))
  refine ⟨a, linearElement_mem d true q, t, ht, a, linearElement_mem d true q, ?_⟩
  rw [local_linear_weyl, linearPanelWeyl_conj_positive]
  have hw : w = a * linearElement d false z * a := by
    simp only [w, linearPanelWeyl, a, q, inv_inv, Units.val_mk0]
  change linearElement d false z = a * (w * v⁻¹) * v * a
  rw [hw]
  have haa : a * a = 1 := linearElement_self_mul d true q
  calc
    _ = a * (a * linearElement d false z * a) * a := by
      symm
      calc
        _ = (a * a) * linearElement d false z * (a * a) := by group
        _ = _ := by rw [haa, one_mul, mul_one]
    _ = _ := by group

/-- Every nonidentity positive relative root element has its reflected Gauss
form, with both root factors and the torus factor in the actual fixed group. -/
theorem relativeRankOneGauss (m : ℕ) : RelativeRankOneGauss m := by
  intro s x hx hx1
  let d := canonicalLocalBlockInput m
  let x' := d.modelEquiv.symm x
  have hx' : x' ∈ simpleBlock d s true :=
    (modelEquiv_mem_relativePositiveBlock_iff d s x').mp (by simpa only [x', MulEquiv.apply_symm_apply] using hx)
  have hx1' : x' ≠ 1 := by
    intro he
    apply hx1
    simpa only [x', MulEquiv.apply_symm_apply, map_one] using congrArg d.modelEquiv he
  have h : ∃ a ∈ simpleBlock d s true, ∃ t ∈ (splitTorus m).subgroupOf d.fixedGroup,
      ∃ y ∈ simpleBlock d s true,
        relativeWeyl d s * x' * (relativeWeyl d s)⁻¹ = a * t * relativeWeyl d s * y := by
    cases s
    · exact local_suzuki_gauss d hx' hx1'
    · exact local_linear_gauss d hx' hx1'
  obtain ⟨a, ha, t, ht, y, hy, he⟩ := h
  refine ⟨d.modelEquiv a, (modelEquiv_mem_relativePositiveBlock_iff d s a).mpr ha,
    d.modelEquiv t, ?_, d.modelEquiv y,
    (modelEquiv_mem_relativePositiveBlock_iff d s y).mpr hy, ?_⟩
  · change toSplitGroup m (d.modelEquiv t) ∈ splitTorus m
    change t.val ∈ splitTorus m at ht
    simpa only [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe] using ht
  · rw [local_weyl_inv] at he
    simpa only [map_mul, wordExchange_modelEquiv_relativeWeyl, x', MulEquiv.apply_symm_apply] using
      congrArg d.modelEquiv he

end ReeF4.SectionGeometry.BNPair
