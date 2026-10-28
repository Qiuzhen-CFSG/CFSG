module

public import Theory.AlgebraicGroup.Parabolic.InvariantLeviGeometry.Collection

/-!
# Transport of standard Levi root supports

Integral and rational simple-root expansions identify the actual Levi root
subsystem with a rational vector span. Consequently a linear permutation of
root rays preserving `J` preserves its actual Levi subsystem. Scalars may
depend on the root, as needed for the exceptional Steinberg permutations.
Exact root-group transport then preserves all three standard point groups.

Source: GLS3, §§1.13 and 2.3, as used in the proof of Theorem 2.6.5.
-/

namespace Theory.AlgebraicGroup.InvariantLeviGeometry

open scoped BigOperators
universe u
variable {k : Type u} [Field k]
  {K : Variety k} [AlgebraicGroup K]
  (S : StandardParabolicRelativeRootSetup K)

private theorem root_coord (a j : S.ι) (hj : j ∈ S.rationalBase.support) :
    S.rationalBase.toWeightBasis.repr (S.rationalPairing.root a) ⟨j, hj⟩ =
      (S.coeff a j : ℚ) := by
  classical
  let := Fintype.ofFinite S.ι
  have hrepr := congrArg S.rationalBase.toWeightBasis.repr
    (S.rationalSimpleRootExpansion a).1
  simp only [map_sum, map_smul] at hrepr
  have h := congrArg (fun v : S.rationalBase.support →₀ ℚ => v ⟨j, hj⟩) hrepr
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply] at h
  have hcoord (i : S.ι) (hi : i ∈ S.rationalBase.support) :
      S.rationalBase.toWeightBasis.repr (S.rationalPairing.root i) ⟨j, hj⟩ =
        if i = j then 1 else 0 := by
    simpa [Finsupp.single_apply] using congrArg
      (fun v : S.rationalBase.support →₀ ℚ => v ⟨j, hj⟩)
      (S.rationalBase.toWeightBasis_repr_root ⟨i, hi⟩)
  have hs : (∑ i ∈ S.rationalBase.support, (S.coeff a i : ℚ) •
      S.rationalBase.toWeightBasis.repr (S.rationalPairing.root i) ⟨j, hj⟩) =
      (S.coeff a j : ℚ) := by
    rw [Finset.sum_eq_single_of_mem j hj]
    · simp [hcoord j hj]
    · intro i hi hij
      simp [hcoord i hi, hij]
  exact h.trans hs

/-- The integral root-subsystem condition is exactly vanishing of all simple
coordinates outside `J`. -/
public theorem mem_sigma_iff_coeff_zero (a : S.D.Root) :
    a ∈ S.sigmaJ ↔ ∀ j ∈ S.rationalBase.support,
      S.rootEquiv.symm j ∉ S.J → S.coeff (S.rootEquiv a) j = 0 := by
  classical
  let := Fintype.ofFinite S.ι
  let := Fintype.ofFinite S.D.Root
  have hf := relativeRootFiber_zero_eq_standardLeviRoots S.T S.B S.D
    S.integralPairing S.integralBase S.rootEquiv S.weightEquiv
    S.positiveRoots S.J S.sigmaJ S.coeff S.actualRootDatum
    S.integralSimpleRootExpansion S.standardParabolic
  have hm := Set.ext_iff.mp hf (S.rootEquiv a)
  have hz : a ∈ S.sigmaJ ↔ RelativeRootProjection S.coeff
      (S.rationalBase.support : Set S.ι) (S.rootEquiv '' S.J) (S.rootEquiv a) = 0 := by
    rw [S.baseSupport_eq]
    simpa [RelativeRootFiber] using hm.symm
  rw [hz]
  constructor
  · intro h j hj hjJ
    have h' := congrArg (fun v : S.ι →₀ ℤ => v j) h
    simpa [RelativeRootProjection, hj, hjJ] using h'
  · intro h
    apply Finsupp.ext
    intro j
    by_cases hj : j ∈ S.rationalBase.support
    · by_cases hjJ : S.rootEquiv.symm j ∈ S.J
      · simp [RelativeRootProjection, hj, hjJ]
      · simp [RelativeRootProjection, hj, hjJ, h j hj hjJ]
    · simp [RelativeRootProjection, hj]

/-- The actual integral Levi root subsystem is the rational span of its
simple roots, using the shared integral and rational coordinate expansions. -/
public theorem mem_sigma_iff_root_mem_span (a : S.D.Root) :
    a ∈ S.sigmaJ ↔ S.rationalPairing.root (S.rootEquiv a) ∈
      Submodule.span ℚ ((S.rationalPairing.root ∘ S.rootEquiv) '' S.J) := by
  classical
  let := Fintype.ofFinite S.ι
  let I : Set S.rationalBase.support := {j | S.rootEquiv.symm j ∈ S.J}
  have himage : ((S.rationalPairing.root ∘ S.rootEquiv) '' S.J) =
      S.rationalBase.toWeightBasis '' I := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hs : S.rootEquiv b ∈ S.rationalBase.support :=
        (S.rationalRootRealization.2.2.2.1 b).mp (S.standardParabolic.2.1 hb)
      exact ⟨⟨S.rootEquiv b, hs⟩, by simpa [I], by simp⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨S.rootEquiv.symm j, hj, by simp⟩
  rw [himage, S.rationalBase.toWeightBasis.mem_span_image, mem_sigma_iff_coeff_zero]
  constructor
  · intro h j hj
    by_contra hjI
    have hc := h j j.property hjI
    have hnonzero := Finsupp.mem_support_iff.mp hj
    apply hnonzero
    rw [root_coord]
    exact_mod_cast hc
  · intro h j hj hjJ
    have hzero : S.rationalBase.toWeightBasis.repr
        (S.rationalPairing.root (S.rootEquiv a)) ⟨j, hj⟩ = 0 := by
      by_contra hn
      exact hjJ (h (Finsupp.mem_support_iff.mpr hn))
    rw [root_coord] at hzero
    exact_mod_cast hzero

/-- A linear permutation of the actual root rays preserves the Levi root set
whenever it preserves its chosen simple-root subset. The ray scalars need not
be constant. -/
public theorem sigma_image_eq_of_rootRays
    (e : S.D.Root ≃ S.D.Root) (A : S.XQ ≃ₗ[ℚ] S.XQ)
    (c : S.D.Root → ℚ) (hc : ∀ a, c a ≠ 0)
    (hroot : ∀ a, A (S.rationalPairing.root (S.rootEquiv a)) =
      c a • S.rationalPairing.root (S.rootEquiv (e a)))
    (hJ : e '' S.J = S.J) : e '' S.sigmaJ = S.sigmaJ := by
  let v : S.D.Root → S.XQ := S.rationalPairing.root ∘ S.rootEquiv
  let V := Submodule.span ℚ (v '' S.J)
  have hforward : ∀ x ∈ V, A x ∈ V := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      rw [show A (v a) = c a • v (e a) from hroot a]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨e a, hJ ▸ Set.mem_image_of_mem e ha, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa using V.add_mem ihx ihy
    | smul r x hx ih => simpa using V.smul_mem r ih
  have hbackward : ∀ x ∈ V, A.symm x ∈ V := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have he : e.symm a ∈ S.J := by
        have ha' : a ∈ e '' S.J := hJ.symm ▸ ha
        simpa using ha'
      have hv : A.symm (v a) = (c (e.symm a))⁻¹ • v (e.symm a) := by
        apply A.injective
        simp only [LinearEquiv.apply_symm_apply, map_smul]
        rw [show A (v (e.symm a)) = c (e.symm a) • v a by simpa [v] using hroot (e.symm a)]
        simp [smul_smul, hc]
      rw [hv]
      exact V.smul_mem _ (Submodule.subset_span ⟨e.symm a, he, rfl⟩)
    | zero => simp
    | add x y hx hy ihx ihy => simpa using V.add_mem ihx ihy
    | smul r x hx ih => simpa using V.smul_mem r ih
  have hinv (a : S.D.Root) : e a ∈ S.sigmaJ ↔ a ∈ S.sigmaJ := by
    rw [mem_sigma_iff_root_mem_span, mem_sigma_iff_root_mem_span]
    change v (e a) ∈ V ↔ v a ∈ V
    constructor
    · intro ha
      have hm : A (v a) ∈ V := by
        rw [show A (v a) = c a • v (e a) from hroot a]
        exact V.smul_mem _ ha
      simpa using hbackward _ hm
    · intro ha
      have hm := hforward _ ha
      rw [show A (v a) = c a • v (e a) from hroot a] at hm
      exact (V.smul_mem_iff (hc a)).mp hm
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (hinv b).mpr hb
  · intro ha
    exact ⟨e.symm a, (hinv (e.symm a)).mp (by simpa using ha), by simp⟩

/-- A proper subset of the simple roots leaves a positive root outside the
Levi subsystem. This includes the precise root used to witness the complement. -/
public theorem positiveOutside_nonempty_of_simple_ssubset
    (hJ : S.J ⊂ S.D.simple) : (S.positiveRoots \ S.sigmaJ).Nonempty := by
  classical
  let := Fintype.ofFinite S.ι
  obtain ⟨a, ha, haJ⟩ := Set.exists_of_ssubset hJ
  have hs : S.rootEquiv a ∈ S.rationalBase.support :=
    (S.rationalRootRealization.2.2.2.1 a).mp ha
  have height_one : RelativeRootHeight S.coeff S.rationalBase.support
      (S.rootEquiv '' S.J) (S.rootEquiv a) = 1 :=
    (relativeRootHeight_eq_one_iff_not_mem S.rationalPairing S.rationalBase
      (S.rootEquiv '' S.J) S.coeff S.rationalSimpleRootExpansion hs).mpr (by simpa)
  refine ⟨a, ?_, ?_⟩
  · apply (S.actualRootDatum.2.2 a).mpr
    exact S.integralBase.isPos_of_mem_support
      ((S.actualRootDatum.1.2.2.2 a).mp ha)
  · intro h
    have height_zero := standardParabolicLeviRoot_relativeHeight_eq_zero S h
    omega

variable [IsAlgClosed k]

/-- Properness of the actual standard parabolic leaves a positive root outside
its Levi subsystem. Ambient torus/root generation is the earlier Bruhat input. -/
public theorem positiveOutside_nonempty_of_proper
    (hgen : S.T.toSubgroup ⊔ RootSubgroupGenerated S.D Set.univ = ⊤)
    (hproper : (parabolic S.D S.standardParabolic.1.2.1
      S.standardParabolic.1.1.1 S.positiveRoots S.sigmaJ).toSubgroup ≠ ⊤) :
    (S.positiveRoots \ S.sigmaJ).Nonempty := by
  classical
  by_contra hempty
  have hpos : S.positiveRoots ⊆ S.sigmaJ := by
    intro a ha
    by_contra hs
    exact hempty ⟨a, ha, hs⟩
  have hneg {a : S.D.Root} (ha : S.D.neg a ∈ S.sigmaJ) : a ∈ S.sigmaJ := by
    rw [S.standardParabolic.2.2] at ha ⊢
    change S.D.rootWeight a ∈ Subgroup.closure (S.D.rootWeight '' S.J)
    change S.D.rootWeight (S.D.neg a) ∈ Subgroup.closure (S.D.rootWeight '' S.J) at ha
    rw [S.standardParabolic.1.2.1.2.2.2.1] at ha
    exact inv_mem_iff.mp ha
  have hall (a : S.D.Root) : a ∈ S.sigmaJ := by
    have hc : a ∈ S.positiveRoots ∪ S.D.neg ⁻¹' S.positiveRoots := by
      rw [S.standardParabolic.1.2.2.1.2.1]
      trivial
    rcases hc with ha | ha
    · exact hpos ha
    · exact hneg (hpos ha)
  apply hproper
  apply top_unique
  rw [← hgen]
  refine sup_le le_sup_left ?_
  exact (RootSubgroupGenerated_mono S.D (fun a _ => Or.inl (Or.inr (hall a)))).trans
    le_sup_right

/-- Exact invariance from torus invariance and the induced based root-ray
permutation preserving `J`, with no assumed invariance of the Levi subsystem. -/
public theorem standard_candidates_map_eq
    (f : Variety.Point K →* Variety.Point K) (e : S.D.Root ≃ S.D.Root)
    (A : S.XQ ≃ₗ[ℚ] S.XQ) (c : S.D.Root → ℚ) (hc : ∀ a, c a ≠ 0)
    (hray : ∀ a, A (S.rationalPairing.root (S.rootEquiv a)) =
      c a • S.rationalPairing.root (S.rootEquiv (e a)))
    (hroot : ∀ a, (S.D.rootSubgroup a).toSubgroup.map f =
      (S.D.rootSubgroup (e a)).toSubgroup)
    (htorus : S.T.toSubgroup.map f = S.T.toSubgroup)
    (hpositive : e '' S.positiveRoots = S.positiveRoots)
    (hJ : e '' S.J = S.J) (hneg : ∀ a, e (S.D.neg a) = S.D.neg (e a)) :
    let hD := S.standardParabolic.1.2.1
    let hT := S.standardParabolic.1.1.1
    let P := parabolic S.D hD hT S.positiveRoots S.sigmaJ
    let U := unipotent S.D hD S.positiveRoots S.sigmaJ
    let L := levi S.D hD hT S.sigmaJ
    P.toSubgroup.map f = P.toSubgroup ∧
      U.toSubgroup.map f = U.toSubgroup ∧ L.toSubgroup.map f = L.toSubgroup :=
  candidates_map_eq S.D S.standardParabolic.1.2.1 S.standardParabolic.1.1.1
    S.positiveRoots S.sigmaJ f e hroot htorus hpositive
    (sigma_image_eq_of_rootRays S e A c hc hray hJ) hneg

end Theory.AlgebraicGroup.InvariantLeviGeometry
