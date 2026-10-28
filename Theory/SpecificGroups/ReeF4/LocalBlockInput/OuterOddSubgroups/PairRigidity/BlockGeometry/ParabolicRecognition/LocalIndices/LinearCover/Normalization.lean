module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.LinearCover.RankOne
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.SplitRetraction.Normality
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges

/-!
# Radical and torus actions for the linear Ree panel

Positive root exchanges preserve the linear radical, since every correction
root has height greater than one and hence lies outside the end-node Levi.
The paired Weyl representative preserves this radical by its two end
reflections. Its parameter-preserving exchange of the signed linear blocks
then proves that the full negative block normalizes the radical, for every
coefficient field. Restriction to the supplied fixed group preserves these
normalizer containments.

Diagonal torus conjugation scales the generators of the negative root closure.
For the Weyl action on the torus, conjugate the actual generating coroot words:
their roots are reflected and their parameters are unchanged. Thus both the
radical and the torus conjugate into the root Borel. Only the torus action on
the negative block uses equality of the coroot and diagonal tori.

Source: GLS3, 2.3.8(a,b), Table 2.4 type VI, and 2.6.5(g),
`refs/KGroup/GLS3/chapter2.tex`. The positive-exchange argument adapts
`BinaryLocals/LinearProjection/SplitRetraction/Normality.lean` to arbitrary
parameters using the proved paired Weyl action.
-/

public section
noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices
open Subgroup LargeLocalSeeds Parabolics BlockParameters.FieldRecovery
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {m : ℕ}

private theorem root_degree_levi_le_one {r : F4Chevalley.Root}
    (hr : BinaryLinear.IsLeviRoot r) : RadicalCoordinates.rootDegree r ≤ 1 := by
  have hd (i : Fin 4) : typeF4RootPairing_base.height (typeF4SimpleRootIndex i) = 1 :=
    typeF4RootPairing_base.height_one_of_mem_support
      (typeF4RootPairing_baseEquiv i).property
  rcases hr with ⟨i, _, rfl | rfl⟩
  · rw [RadicalCoordinates.rootDegree, hd]
    decide
  · rw [RadicalCoordinates.rootDegree,
      typeF4RootPairing_base.height_reflectionPerm_self, hd]
    decide

private theorem radical_of_degree_gt_one (r : RadicalCoordinates.Root .positive)
    (hr : 1 < RadicalCoordinates.rootDegree r.val) : IsRadicalRoot .linear r.val := by
  rcases BinaryLinear.isSeedRoot_radical_or_levi (Or.inl r.property) with h | h
  · exact h
  · have := root_degree_levi_le_one h
    omega

private theorem root_mul_self (r : F4Chevalley.Root) (t : CoefficientField m) :
    rootGeneratorInGroup m r t * rootGeneratorInGroup m r t = 1 := by
  apply Subtype.ext
  change F4Chevalley.rootCurve r t * F4Chevalley.rootCurve r t = 1
  rw [← F4Chevalley.rootCurve_add, CharTwo.add_self_eq_zero,
    F4Chevalley.rootCurve_zero]

private theorem mem_radical_normalizer_of_conj_roots (g : SplitGroup m)
    (h : ∀ (r : F4Chevalley.Root) (t : CoefficientField m),
      IsRadicalRoot .linear r →
      g * rootGeneratorInGroup m r t * g⁻¹ ∈ splitRadical m .linear) :
    g ∈ normalizer (splitRadical m .linear) := by
  have hle : splitRadical m .linear ≤
      (splitRadical m .linear).comap (MulAut.conj g).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    exact h r t hr
  exact mem_normalizer_fintype fun _ hx => hle hx

private theorem positive_root_mem_radical_normalizer (s : F4Chevalley.Root)
    (b : CoefficientField m) (hs : typeF4RootPairing_base.IsPos s) :
    rootGeneratorInGroup m s b ∈ normalizer (splitRadical m .linear) := by
  let N := splitRadical m .linear
  by_cases hsr : IsRadicalRoot .linear s
  · exact N.le_normalizer (subset_closure ⟨s, b, hsr, rfl⟩)
  apply mem_radical_normalizer_of_conj_roots
  intro r a hr
  obtain ⟨c, hc, he⟩ := RadicalCoordinates.rootGenerator_exchange m
    (⟨r, hr.1⟩ : RadicalCoordinates.Root .positive) ⟨s, hs⟩ a b (by
      intro heq
      have hrs : r = s := congrArg Subtype.val heq
      exact hsr (hrs ▸ hr))
  have hcmem : FilteredCollection.wordProduct
      (fun q : RadicalCoordinates.Root .positive => rootGeneratorInGroup m q.val) c ∈ N := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    apply Subgroup.subset_closure
    refine ⟨z.1.val, z.2, radical_of_degree_gt_one z.1 ?_, rfl⟩
    have hd := RadicalCoordinates.rootDegree_pos (⟨s, hs⟩ : RadicalCoordinates.Root .positive)
    have hc' := hc z hz
    have hm := Nat.le_max_right (RadicalCoordinates.rootDegree r) (RadicalCoordinates.rootDegree s)
    dsimp only at hd hc'
    omega
  have hinv : (rootGeneratorInGroup m s b)⁻¹ = rootGeneratorInGroup m s b :=
    inv_eq_of_mul_eq_one_left (root_mul_self s b)
  have he' : rootGeneratorInGroup m s b * rootGeneratorInGroup m r a *
      (rootGeneratorInGroup m s b)⁻¹ = rootGeneratorInGroup m r a *
        FilteredCollection.wordProduct
          (fun q : RadicalCoordinates.Root .positive => rootGeneratorInGroup m q.val) c := by
    rw [hinv, mul_assoc, he]
    rw [← mul_assoc (rootGeneratorInGroup m s b),
      ← mul_assoc (rootGeneratorInGroup m s b), root_mul_self s b, one_mul]
  rw [he']
  exact N.mul_mem (subset_closure ⟨r, a, hr, rfl⟩) hcmem

private theorem positive_le_radical_normalizer (d : LocalBlockInput m) :
    standardUnipotent d ≤ normalizer (linearPanelRadical d) := by
  have h : splitUnipotent m ≤ normalizer (splitRadical m .linear) := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, hr, rfl⟩
    exact positive_root_mem_radical_normalizer r t hr
  exact (Subgroup.comap_mono h).trans (Subgroup.le_normalizer_comap d.fixedGroup.subtype)

private theorem panelWeyl_mem_radical_normalizer (d : LocalBlockInput m) :
    linearPanelWeyl d 1 ∈ normalizer (linearPanelRadical d) := by
  apply Subgroup.le_normalizer_comap d.fixedGroup.subtype
  apply mem_radical_normalizer_of_conj_roots
  intro r t hr
  change (linearPanelWeyl d 1).val * rootGeneratorInGroup m r t *
    (linearPanelWeyl d 1).val⁻¹ ∈ splitRadical m .linear
  rw [linearPanelWeyl_conj_root]
  exact subset_closure ⟨_, t,
    BinaryLinear.isRadicalRoot_end_reflection 0 (by simp [leviNodes]) _
      (BinaryLinear.isRadicalRoot_end_reflection 3 (by simp [leviNodes]) r hr), rfl⟩

/-- The full negative linear block normalizes the prescribed positive radical. -/
theorem linear_negative_le_radical_normalizer (d : LocalBlockInput m) :
    simpleBlock d .linear false ≤ normalizer (linearPanelRadical d) := by
  intro x hx
  obtain ⟨t, rfl⟩ := linearElement_surjective d false hx
  rw [← linearPanelWeyl_conj_positive]
  have hn := panelWeyl_mem_radical_normalizer d
  have hp := positive_le_radical_normalizer d
    (simpleBlock_positive_le d .linear (linearElement_mem d true t))
  exact mul_mem (mul_mem hn hp) (inv_mem hn)

private theorem diagonalTorus_le_block_normalizer (m : ℕ) (s : Side) (p : Bool) :
    diagonalTorus m ≤ normalizer (splitSimpleBlock m s p) := by
  unfold splitSimpleBlock
  rw [le_normalizer_closure_iff]
  intro z hz x hx
  change z.val ∈ (diagonalTorusHom m).range at hz
  obtain ⟨u, hu⟩ := hz
  obtain ⟨r, t, hr, rfl⟩ := hx
  apply Subgroup.subset_closure
  refine ⟨r, ((integralChevalleyRootScale (P := typeF4RootPairing) u⁻¹ r :
    (CoefficientField m)ˣ) : CoefficientField m) * t, hr, ?_⟩
  apply Subtype.ext
  change z.val * F4Chevalley.rootCurve r t * z.val⁻¹ = _
  rw [← hu]
  have he := F4Chevalley.rootCurve_torus_conjugation u⁻¹ r t
  simpa only [← diagonalTorusHom_apply, map_inv, inv_inv, rootGeneratorInGroup_coe] using he

/-- The fixed coroot torus normalizes the negative linear block whenever the
coroot-word torus is the diagonal torus. -/
theorem linearPanelTorus_le_negative_normalizer (d : LocalBlockInput m)
    (hT : splitTorus m = diagonalTorus m) :
    linearPanelTorus d ≤ normalizer (simpleBlock d .linear false) := by
  have h := hT.le.trans (diagonalTorus_le_block_normalizer m .linear false)
  exact (Subgroup.comap_mono h).trans (Subgroup.le_normalizer_comap d.fixedGroup.subtype)

/-- Conjugation by the paired Weyl representative carries the radical into
the root Borel, with convention `n * x * n⁻¹`. -/
theorem linearPanelRadical_le_borel_comap_weyl (d : LocalBlockInput m) :
    linearPanelRadical d ≤ (rootBorel d).comap
      (MulAut.conj (linearPanelWeyl d 1)).toMonoidHom := by
  intro x hx
  exact linearPanelRadical_le_borel d
    ((mem_normalizer_iff.mp (panelWeyl_mem_radical_normalizer d) x).mp hx)

private theorem reflection_neg (i r : F4Chevalley.Root) :
    typeF4RootPairing.reflectionPerm i (-r) =
      -typeF4RootPairing.reflectionPerm i r := by
  apply typeF4RootPairing.root.injective
  have hneg (r : F4Chevalley.Root) :
      typeF4RootPairing.root (-r) = -typeF4RootPairing.root r := by
    change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm r r) = _
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  calc
    _ = typeF4RootPairing.reflection i (typeF4RootPairing.root (-r)) :=
      typeF4RootPairing.root_reflectionPerm i (-r)
    _ = -typeF4RootPairing.reflection i (typeF4RootPairing.root r) := by
      rw [hneg, map_neg]
    _ = _ := by rw [hneg, RootPairing.root_reflectionPerm]

private theorem panelWeyl_conj_torusWord (d : LocalBlockInput m)
    (r : F4Chevalley.Root) (t : (CoefficientField m)ˣ) :
    MulAut.conj (linearPanelWeyl d 1).val (torusWord m r t) =
      torusWord m
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0)
          (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 3) r)) t := by
  simp only [torusWord, weylWord, map_mul, MulAut.conj_apply,
    linearPanelWeyl_conj_root, reflection_neg]

/-- Conjugation of the actual generating coroot words carries the fixed torus
into the root Borel, with convention `n * x * n⁻¹`. -/
theorem linearPanelTorus_le_borel_comap_weyl (d : LocalBlockInput m) :
    linearPanelTorus d ≤ (rootBorel d).comap
      (MulAut.conj (linearPanelWeyl d 1)).toMonoidHom := by
  have h : splitTorus m ≤ (splitTorus m).comap
      (MulAut.conj (linearPanelWeyl d 1).val).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨r, t, rfl⟩
    change MulAut.conj (linearPanelWeyl d 1).val (torusWord m r t) ∈ splitTorus m
    rw [panelWeyl_conj_torusWord]
    exact subset_closure ⟨_, t, rfl⟩
  intro x hx
  apply linearPanelTorus_le_borel d
  exact h hx

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices
