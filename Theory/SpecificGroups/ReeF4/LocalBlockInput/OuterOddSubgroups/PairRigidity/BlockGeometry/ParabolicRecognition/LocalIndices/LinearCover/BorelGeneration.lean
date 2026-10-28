module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.LinearCover.RankOne
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.SplitRetraction

/-!
# Generation of the fixed linear Ree Borel

Collect the positive split root generators in an order with the positive
linear-block roots first and the radical roots second. This gives a product
of the two actual root-generated subgroups. The matrix grading separates
the radical from the end-node Levi, so the two factors are unique. Both
subgroups are twist-stable; uniqueness therefore makes both factors fixed
when their product is fixed.

The coroot-word torus identity supplies oddness and normalization through
the diagonal torus. The established fixed Borel decomposition then gives
generation by the positive linear block, the prescribed radical, and the
prescribed torus. All assertions hold also at the binary endpoint.

Source: GLS3, 2.3.4(c), 2.3.7, Table 2.4 type VI, and 2.6.5(g),
`refs/KGroup/GLS3/chapter2.tex`.
-/

public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices
open Subgroup FilteredCollection LargeLocalSeeds Parabolics
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics.RadicalCoordinates BlockParameters.FieldRecovery

private theorem split_positive_factorization (m : ℕ) (x : SplitGroup m)
    (hx : x ∈ splitUnipotent m) :
    ∃ a ∈ splitSimpleBlock m .linear true, ∃ r ∈ splitRadical m .linear, a * r = x := by
  classical
  let : Fintype (Root .positive) := Fintype.ofFinite _
  let p : Root .positive → Bool := fun r => decide (IsSimpleBlockRoot .linear true r.val)
  let allRoots : List (Root .positive) := Finset.univ.toList
  let first := allRoots.filter p
  let rest := allRoots.filter (fun r => !p r)
  let order := first ++ rest
  have hp : order.Perm allRoots := List.filter_append_perm p allRoots
  have hmem (r : Root .positive) : r ∈ order := hp.mem_iff.mpr (by simp [allRoots])
  have hn : order.Nodup := hp.nodup_iff.mpr (Finset.nodup_toList _)
  obtain ⟨w, hw⟩ := exists_rootWord m (k := .positive) x hx
  obtain ⟨t, ht⟩ := filteredCollection_exists_params
    (fun r : Root .positive => rootDegree r.val)
    (fun r : Root .positive => rootGeneratorInGroup m r.val) order hn
    ((Finset.univ.sup fun r : Root .positive => rootDegree r.val) + 1)
    (fun r _ => Nat.lt_succ_of_le (Finset.le_sup (f := fun r : Root .positive =>
      rootDegree r.val) (Finset.mem_univ r)))
    (fun r a b => Subtype.ext (F4Chevalley.rootCurve_add r.val a b).symm)
    (fun r s a b _ _ hne => by
      obtain ⟨c, hc, he⟩ := rootGenerator_exchange m r s a b hne
      exact ⟨c, fun z hz => ⟨hmem z.1, hc z hz⟩, he⟩)
    w (fun z _ => hmem z.1)
  refine ⟨(first.map fun r => rootGeneratorInGroup m r.val (t r)).prod, ?_,
    (rest.map fun r => rootGeneratorInGroup m r.val (t r)).prod, ?_, ?_⟩
  · apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    have hr' : IsSimpleBlockRoot .linear true r.val := by
      simpa only [p, decide_eq_true_eq] using (List.mem_filter.mp hr).2
    exact subset_closure ⟨r.val, t r, hr', rfl⟩
  · apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    have hr' : ¬ IsSimpleBlockRoot .linear true r.val := by
      simpa [p] using (List.mem_filter.mp hr).2
    have hrR : IsRadicalRoot .linear r.val := by
      refine ⟨r.property, ?_⟩
      by_contra h
      apply hr'
      refine ⟨?_, r.property⟩
      push Not at h
      exact h
    exact subset_closure ⟨r.val, t r, hrR, rfl⟩
  · simpa only [order, List.map_append, List.prod_append] using (hw.trans ht).symm

private theorem splitLinearBlock_le_levi (m : ℕ) :
    splitSimpleBlock m .linear true ≤ BinaryLinear.splitLevi m := by
  apply Subgroup.closure_mono
  rintro x ⟨r, t, hr, rfl⟩
  exact ⟨r, t, BinaryLinear.isLeviRoot_of_middle_coefficients_zero r
    (hr.1 1 (by simp [leviNodes])) (hr.1 2 (by simp [leviNodes])), rfl⟩

private theorem twist_mem_splitLinearBlock {m : ℕ} (d : LocalBlockInput m)
    {x : SplitGroup m} (hx : x ∈ splitSimpleBlock m .linear true) :
    d.twist x ∈ splitSimpleBlock m .linear true := by
  have hroot (i : Fin 4) (hi : i = 0 ∨ i = 3) (t : CoefficientField m) :
      rootGeneratorInGroup m (typeF4SimpleRootIndex i) t ∈
        splitSimpleBlock m .linear true := by
    apply Subgroup.subset_closure
    refine ⟨_, t, ⟨?_, ?_⟩, rfl⟩
    · intro j hj
      rcases hi with rfl | rfl
      all_goals fin_cases j <;>
        simp_all [leviNodes, typeF4SimpleCoefficient, typeF4SimpleRoot, Fin.ext_iff] <;>
        norm_num
    · exact typeF4RootPairing_base.isPos_of_mem_support
        (typeF4RootPairing_baseEquiv i).property
  obtain ⟨t, u, rfl⟩ := linearSplitWord_surjective hx
  simp only [linearSplitWord, map_mul, d.twist_root, exceptionalRootPermutation_simple]
  exact mul_mem (hroot 3 (Or.inr rfl) _) (hroot 0 (Or.inl rfl) _)

/-- Each fixed positive element has a fixed linear-block factor and a fixed radical factor. -/
theorem linearPanelUnipotent_factorization {m : ℕ} (d : LocalBlockInput m)
    (x : d.fixedGroup) (hx : x ∈ standardUnipotent d) :
    ∃ a ∈ simpleBlock d .linear true, ∃ r ∈ linearPanelRadical d, a * r = x := by
  obtain ⟨a, ha, r, hr, he⟩ := split_positive_factorization m x.val hx
  have ha' := twist_mem_splitLinearBlock d ha
  have hr' : d.twist r ∈ splitRadical m .linear := by
    rw [d.twist_eq_reeAutomorphism]
    exact (BinaryLinear.splitRadical_linear_invariant m).le
      (Subgroup.mem_map_of_mem (reeAutomorphism m).toMonoidHom hr)
  have hd : Disjoint (splitSimpleBlock m .linear true) (splitRadical m .linear) :=
    (BinaryLinear.splitRadical_disjoint_splitLevi m).symm.mono_left (splitLinearBlock_le_levi m)
  have hf : d.twist a * d.twist r = a * r := by
    rw [← map_mul, he]
    exact x.property
  have hp := Subgroup.mul_injective_of_disjoint hd
    (a₁ := (⟨d.twist a, ha'⟩, ⟨d.twist r, hr'⟩))
    (a₂ := (⟨a, ha⟩, ⟨r, hr⟩)) hf
  have hfa : d.twist a = a := congrArg (fun z => z.1.val) hp
  have hfr : d.twist r = r := congrArg (fun z => z.2.val) hp
  exact ⟨⟨a, hfa⟩, ha, ⟨r, hfr⟩, hr, Subtype.ext he⟩

/-- Generation of the actual positive fixed intersection by the prescribed root subgroups. -/
theorem standardUnipotent_le_linearBlock_sup_radical {m : ℕ} (d : LocalBlockInput m) :
    standardUnipotent d ≤ simpleBlock d .linear true ⊔ linearPanelRadical d := by
  intro x hx
  obtain ⟨a, ha, r, hr, rfl⟩ := linearPanelUnipotent_factorization d x hx
  exact mul_mem_sup ha hr

private theorem modelEquiv_map_intersection {m : ℕ} (d : LocalBlockInput m)
    (H : Subgroup (SplitGroup m)) :
    (H.subgroupOf d.fixedGroup).map d.modelEquiv.toMonoidHom =
      H.comap (toSplitGroup m) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change toSplitGroup m (d.modelEquiv y) ∈ H
    rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]
    exact Subgroup.mem_subgroupOf.mp hy
  · intro hx
    refine ⟨d.modelEquiv.symm x, ?_, d.modelEquiv.apply_symm_apply x⟩
    change (d.modelEquiv.symm x).val ∈ H
    rw [Parabolics.modelEquiv_symm_coe]
    simpa only [Subgroup.mem_comap, toSplitGroup_apply] using hx

/-- The matrix-preserving model equivalence transports the fixed Borel decomposition. -/
theorem rootBorel_eq_standardUnipotent_sup_linearPanelTorus {m : ℕ} (d : LocalBlockInput m)
    (hT : splitTorus m = diagonalTorus m) :
    rootBorel d = standardUnipotent d ⊔ linearPanelTorus d := by
  apply (Subgroup.map_injective (f := d.modelEquiv.toMonoidHom) d.modelEquiv.injective)
  rw [rootBorel_map_modelEquiv, Subgroup.map_sup]
  change borel m =
    ((splitUnipotent m).subgroupOf d.fixedGroup).map d.modelEquiv.toMonoidHom ⊔
    ((splitTorus m).subgroupOf d.fixedGroup).map d.modelEquiv.toMonoidHom
  rw [modelEquiv_map_intersection, modelEquiv_map_intersection]
  exact borel_eq_unipotent_sup_fixedTorus_of_splitTorus m
    (splitTorus_le_unipotent_normalizer_of_le_diagonalTorus m hT.le)
    (splitTorus_odd_card_of_le_diagonalTorus m hT.le)

/-- The Borel generation input for the linear parabolic coset cover. -/
theorem rootBorel_le_linearBlock_sup_radical_sup_torus {m : ℕ} (d : LocalBlockInput m)
    (hT : splitTorus m = diagonalTorus m) :
    rootBorel d ≤ (simpleBlock d .linear true ⊔ linearPanelRadical d) ⊔ linearPanelTorus d := by
  rw [rootBorel_eq_standardUnipotent_sup_linearPanelTorus d hT]
  exact sup_le_sup_right (standardUnipotent_le_linearBlock_sup_radical d) _

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices
