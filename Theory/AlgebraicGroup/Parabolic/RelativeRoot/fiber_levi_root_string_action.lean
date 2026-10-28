module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.source_chevalley_torus_fiber_bridge
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.source_rootspan_bridge
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.representation_source_nonsingular_coefficient
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.RelativeRootNeg
public import Theory.LinearAlgebra.PolynomialCoefficients

/-!
The Levi root subgroups propagate an invariant subspace along every absolute-root
string contained in one relative-root fiber.  The result assumes nonsingular
characteristic, an invariant submodule of the source fiber representation, and
an integral root-string relation whose direction belongs to the standard Levi
root subsystem.

The proof packages the relevant Chevalley root element as a Levi point using
`levi_alignment`, translates conjugation through the quotient coordinate model,
and applies the nonsingular Chevalley commutator formula.  Since that source
calculation is written as inverse conjugation, it evaluates the maintained left
action at the inverse Levi point through the fiber module's inverse-indexed
compatibility theorem.  Terms of relative
height at least the next layer vanish; the remaining factors become sums of
root vectors through `M.pointEquiv`.  Polynomial coefficient extraction and
nonvanishing of the expected Chevalley coefficient isolate the target vector.
Negative string directions are reduced to the positive case using the realized
opposite root `S.D.neg`.  This is the source-level root-string step used by
the relative-root fiber irreducibility argument following GLS3, Section 1.14.
-/

universe u v

namespace Theory.AlgebraicGroup

open Set
local notation "Submodule" => _root_.Submodule

set_option linter.style.haveILetI false

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

private lemma base_coeff_coord
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    (base : P.Base) (coeff : ι → ι → ℤ)
    (hCoeff : HasSimpleRootExpansion P base coeff)
    (a x : ι) (hx : x ∈ base.support) :
    (base.toWeightBasis.repr (P.root a)) ⟨x, hx⟩ = (coeff a x : ℚ) := by
  classical
  have hrepr := congrArg base.toWeightBasis.repr (hCoeff a).1
  simp only [map_sum, map_smul] at hrepr
  have h := congrArg
    (Finsupp.lapply (⟨x, hx⟩ : base.support) :
      (base.support →₀ ℚ) →ₗ[ℚ] ℚ) hrepr
  simp only [map_sum, map_smul, Finsupp.lapply_apply] at h
  have hrootcoord {j : ι} (hj : j ∈ base.support) :
      (base.toWeightBasis.repr (P.root j)) ⟨x, hx⟩ = if j = x then 1 else 0 := by
    let z : base.support := ⟨j, hj⟩
    have hz := base.toWeightBasis_repr_root z
    simpa [z, Finsupp.single_apply] using
      congrArg (fun y : base.support →₀ ℚ => y ⟨x, hx⟩) hz
  rw [show (∑ j ∈ base.support, (coeff a j : ℚ) •
      (base.toWeightBasis.repr (P.root j)) ⟨x, hx⟩) =
      ∑ j ∈ base.support, (coeff a j : ℚ) • (if j = x then 1 else 0) by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hrootcoord hj]] at h
  rw [Finset.sum_eq_single_of_mem x hx] at h
  · simpa using h
  · intro b hb hbx
    simp [hbx]

private lemma root_span_coord_zero
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support)
    {z : M} (hz : z ∈ Submodule.span ℚ (P.root '' J))
    (x : ι) (hx : x ∈ base.support) (hxJ : x ∉ J) :
    (base.toWeightBasis.repr z) ⟨x, hx⟩ = 0 := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
      rcases hz with ⟨j, hj, rfl⟩
      let y : base.support := ⟨j, hJ hj⟩
      have hneq : j ≠ x := by
        intro h
        exact hxJ (h ▸ hj)
      rw [base.toWeightBasis_repr_root y]
      simp [y, hneq]
  | zero => simp
  | add z₁ z₂ _ _ hz₁ hz₂ => simp [map_add, hz₁, hz₂]
  | smul c z _ hz => simp [map_smul, hz]

private lemma root_mem_span_projection_zero
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {a : ι} (hspan : P.root a ∈ Submodule.span ℚ (P.root '' J)) :
    RelativeRootProjection coeff (base.support : Set ι) J a = 0 := by
  classical
  apply Finsupp.ext
  intro x
  by_cases hx : x ∈ base.support
  · by_cases hxJ : x ∈ J
    · simp [RelativeRootProjection, hx, hxJ]
    · have hcoord := root_span_coord_zero P base J hJ hspan x hx hxJ
      have hcoeff := base_coeff_coord P base coeff hCoeff a x hx
      have hzero : coeff a x = 0 := by
        have : (coeff a x : ℚ) = 0 := by simpa [hcoeff] using hcoord
        exact_mod_cast this
      simp [RelativeRootProjection, hx, hxJ, hzero]
  · simp [RelativeRootProjection, hx]

private lemma projection_eq_of_root_sub_mem_span
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    (P : RootPairing ι ℚ M N) [P.IsRootSystem]
    (base : P.Base) (J : Set ι) (hJ : J ⊆ base.support)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    {a b : ι}
    (hspan : P.root a - P.root b ∈ Submodule.span ℚ (P.root '' J)) :
    RelativeRootProjection coeff (base.support : Set ι) J a =
      RelativeRootProjection coeff (base.support : Set ι) J b := by
  classical
  apply Finsupp.ext
  intro x
  by_cases hx : x ∈ base.support
  · by_cases hxJ : x ∈ J
    · simp [RelativeRootProjection, hx, hxJ]
    · have hcoord := root_span_coord_zero P base J hJ hspan x hx hxJ
      have ha := base_coeff_coord P base coeff hCoeff a x hx
      have hb := base_coeff_coord P base coeff hCoeff b x hx
      have hzero : coeff a x = coeff b x := by
        have hz : (coeff a x : ℚ) - (coeff b x : ℚ) = 0 := by
          simpa [map_sub, ha, hb] using hcoord
        exact_mod_cast sub_eq_zero.mp hz
      simp [RelativeRootProjection, hx, hxJ, hzero]
  · simp [RelativeRootProjection, hx]

omit [IsAlgClosed k] in
private lemma source_simple_support
    (S : RelativeRootRepresentationSource K) :
    S.base.support = S.D.simple.toFinite.toFinset := by
  ext gamma
  simp only [Set.Finite.mem_toFinset]
  exact (S.rootSystemRealization.2.2.2.1 gamma).symm

omit [IsAlgClosed k] in
private lemma source_simple_set
    (S : RelativeRootRepresentationSource K) :
    (S.base.support : Set S.D.Root) = S.D.simple := by
  ext gamma
  exact (S.rootSystemRealization.2.2.2.1 gamma).symm

omit [IsAlgClosed k] in
private lemma source_J_subset_support
    (S : RelativeRootRepresentationSource K) :
    S.J ⊆ S.base.support := by
  intro gamma hgamma
  exact (S.rootSystemRealization.2.2.2.1 gamma).1 (S.J_simple hgamma)

private lemma subsystem_relativeRootProjection_eq_zero
    (S : RelativeRootRepresentationSource K) {delta : S.D.Root}
    (hdelta : delta ∈ RootSubsystemSpan S.D S.J) :
    RelativeRootProjection S.coeff S.D.simple S.J delta = 0 := by
  letI := Fintype.ofFinite S.D.Root
  have hspan := (S.root_mem_span_iff_mem_rootSubsystemSpan delta).mpr hdelta
  have hzero := root_mem_span_projection_zero S.pairing S.base S.J
    (source_J_subset_support S) S.coeff S.simpleRootExpansion hspan
  rw [source_simple_set S] at hzero
  exact hzero

private lemma subsystem_relativeRootHeight_eq_zero
    (S : RelativeRootRepresentationSource K) {delta : S.D.Root}
    (hdelta : delta ∈ RootSubsystemSpan S.D S.J) :
    RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J delta = 0 := by
  letI := Fintype.ofFinite S.D.Root
  apply relativeRootHeight_eq_zero_of_projection_eq_zero
  rw [← source_simple_support S]
  rw [source_simple_set S]
  exact subsystem_relativeRootProjection_eq_zero S hdelta

private lemma valid_term_mem_fiber
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (alpha : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root})
    (q : ChevalleyCommutatorTerm S.D.Root)
    (hvalid : IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) delta alpha.1 q)
    (hqj : q.j = 1) :
    q.root ∈ relativeRootFiberAtHeight S.D S.coeff S.J S.height S.root := by
  letI := Fintype.ofFinite S.D.Root
  have hspanDelta := (S.root_mem_span_iff_mem_rootSubsystemSpan delta).mpr hdelta
  have hspan : S.pairing.root q.root - S.pairing.root alpha.1 ∈
      Submodule.span ℚ (S.pairing.root '' S.J) := by
    have hroot := hvalid.2.2
    simp only [Equiv.refl_apply, hqj, Nat.cast_one, one_smul] at hroot
    rw [hroot]
    simpa [add_sub_cancel_right] using
      (Submodule.smul_mem (Submodule.span ℚ (S.pairing.root '' S.J))
        (q.i : ℚ) hspanDelta)
  have hprojection := projection_eq_of_root_sub_mem_span S.pairing S.base S.J
    (source_J_subset_support S) S.coeff S.simpleRootExpansion hspan
  have hheightDelta := subsystem_relativeRootHeight_eq_zero S hdelta
  have hheight := relativeRootHeight_of_validChevalleyCommutatorTerm
    S.D S.pairing (Equiv.refl S.D.Root) S.base S.J S.coeff
      S.simpleRootExpansion q hvalid
  rw [source_simple_support S] at hheight
  simp only [Equiv.refl_apply] at hheight
  have hqheight : RelativeRootHeight S.coeff
      S.D.simple.toFinite.toFinset S.J q.root = S.height := by
    rw [hheight, hheightDelta, alpha.2.2, hqj]
    simp
  refine ⟨⟨Set.mem_univ _, ?_⟩, hqheight⟩
  rw [← source_simple_set S]
  exact hprojection.trans (by
    rw [source_simple_set S]
    exact alpha.2.1.2)

private lemma valid_term_root_element_mem_layer
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (alpha : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root})
    (q : ChevalleyCommutatorTerm S.D.Root)
    (hvalid : IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) delta alpha.1 q) (a : k) :
    S.C.x q.root a ∈ sourceRelativeRootLayer S.D
      S.D.simple.toFinite.toFinset S.coeff S.J S.height := by
  letI := Fintype.ofFinite S.D.Root
  have hheightDelta := subsystem_relativeRootHeight_eq_zero S hdelta
  have hheight := relativeRootHeight_of_validChevalleyCommutatorTerm
    S.D S.pairing (Equiv.refl S.D.Root) S.base S.J S.coeff
      S.simpleRootExpansion q hvalid
  rw [source_simple_support S] at hheight
  simp only [Equiv.refl_apply] at hheight
  have hbound : (S.height : ℤ) ≤ RelativeRootHeight S.coeff
      S.D.simple.toFinite.toFinset S.J q.root := by
    rw [hheight, hheightDelta, alpha.2.2]
    have hqj : (1 : ℤ) ≤ q.j := by exact_mod_cast Nat.succ_le_of_lt hvalid.2.1
    have hheightpos : (0 : ℤ) < S.height := by exact_mod_cast S.height_pos
    nlinarith
  rw [sourceRelativeRootLayer, RelativeRootSeries, RootSubgroupGenerated]
  apply Subgroup.subset_closure
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨q.root, ?_, ?_⟩
  · simpa using hbound
  rw [← (S.chevalleySystem.1 q.root).2]
  exact ⟨a, rfl⟩

private lemma valid_term_root_element_mem_next_layer
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (alpha : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root})
    (q : ChevalleyCommutatorTerm S.D.Root)
    (hvalid : IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) delta alpha.1 q)
    (hqj : q.j ≠ 1) (a : k) :
    S.C.x q.root a ∈ sourceRelativeRootLayer S.D
      S.D.simple.toFinite.toFinset S.coeff S.J (S.height + 1) := by
  letI := Fintype.ofFinite S.D.Root
  have hheightDelta := subsystem_relativeRootHeight_eq_zero S hdelta
  have hheight := relativeRootHeight_of_validChevalleyCommutatorTerm
    S.D S.pairing (Equiv.refl S.D.Root) S.base S.J S.coeff
      S.simpleRootExpansion q hvalid
  rw [source_simple_support S] at hheight
  simp only [Equiv.refl_apply] at hheight
  have hqj : (2 : ℤ) ≤ q.j := by
    have : 0 < q.j := hvalid.2.1
    omega
  have hbound : (S.height + 1 : ℕ) ≤ RelativeRootHeight S.coeff
      S.D.simple.toFinite.toFinset S.J q.root := by
    rw [hheight, hheightDelta, alpha.2.2]
    have hheightpos : (0 : ℤ) < S.height := by exact_mod_cast S.height_pos
    norm_num
    nlinarith
  rw [sourceRelativeRootLayer, RelativeRootSeries, RootSubgroupGenerated]
  apply Subgroup.subset_closure
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨q.root, ?_, ?_⟩
  · simpa using hbound
  rw [← (S.chevalleySystem.1 q.root).2]
  exact ⟨a, rfl⟩

omit [IsAlgClosed k] in
private lemma chevalleyRoot_mem_levi
    (S : RelativeRootRepresentationSource K) {delta : S.D.Root}
    (hdelta : delta ∈ RootSubsystemSpan S.D S.J) (s : k) :
    S.C.x delta s ∈ S.L := by
  have hxroot : S.C.x delta s ∈ S.D.rootSubgroup delta := by
    change S.C.x delta s ∈ (S.D.rootSubgroup delta : Set (Variety.Point K))
    have : S.C.x delta s ∈ Set.range (S.C.x delta) := ⟨s, rfl⟩
    simpa only [(S.chevalleySystem.1 delta).2] using this
  have hxlevi : S.C.x delta s ∈
      standardLeviRootFactor S.D (RootSubsystemSpan S.D S.J) := by
    apply rootSubgroup_le_RootSubgroupGenerated S.D (Or.inl hdelta)
    exact hxroot
  rw [S.levi_alignment]
  change S.C.x delta s ∈ closure
    (Subgroup.closure ((S.T : Set (Variety.Point K)) ∪
      standardLeviRootFactor S.D (RootSubsystemSpan S.D S.J)) :
        Set (Variety.Point K))
  apply subset_closure
  apply Subgroup.subset_closure
  exact Set.mem_union_right _ hxlevi

private noncomputable def chevalleyRootLeviPoint
    (S : RelativeRootRepresentationSource K) (delta : S.D.Root)
    (hdelta : delta ∈ RootSubsystemSpan S.D S.J) (s : k) :
    Variety.Point S.L.carrierVariety :=
  S.L.pointEquiv.symm ⟨S.C.x delta s, chevalleyRoot_mem_levi S hdelta s⟩

omit [IsAlgClosed k] in
private lemma chevalleyRootLeviPoint_include
    (S : RelativeRootRepresentationSource K) (delta : S.D.Root)
    (hdelta : delta ∈ RootSubsystemSpan S.D S.J) (s : k) :
    S.L.includePoint (chevalleyRootLeviPoint S delta hdelta s) =
      S.C.x delta s := by
  change (S.L.pointEquiv
    (S.L.pointEquiv.symm ⟨S.C.x delta s, chevalleyRoot_mem_levi S hdelta s⟩)).1 = _
  rw [S.L.pointEquiv.apply_symm_apply]

private theorem root_string_action_nat
    (S : RelativeRootRepresentationSource K) (M : RelativeRootFiberModule S)
    (hNonsingular : ¬ IsUSingular S.classification (ringChar k))
    (W : Submodule k M.V) (hW : IsInvariantSubmodule M.representation W)
    (alpha beta : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root})
    (delta : S.D.Root) (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (n : ℕ) (hn : 0 < n)
    (hroot : S.pairing.root beta.1 =
      S.pairing.root alpha.1 + n • S.pairing.root delta)
    (halpha : ∀ t, M.rootVector (alpha, t) ∈ W) :
    ∀ t, M.rootVector (beta, t) ∈ W := by
  classical
  letI := relativeRootLayerQuotientGroup S
  letI := S.pairing.indexNeg
  have hdeltaHeight := subsystem_relativeRootHeight_eq_zero S hdelta
  have hne : delta ≠ alpha.1 := by
    intro h
    subst delta
    rw [alpha.2.2] at hdeltaHeight
    have : (0 : ℤ) < S.height := by exact_mod_cast S.height_pos
    omega
  have hnotopp : S.pairing.root delta ≠ -S.pairing.root alpha.1 := by
    letI := Fintype.ofFinite S.D.Root
    intro hneg
    have hidx : delta = S.pairing.reflectionPerm alpha.1 alpha.1 :=
      S.pairing.root.injective <| by
        rw [S.pairing.root_reflectionPerm, S.pairing.reflection_apply_self]
        exact hneg
    have hnegHeight := relativeRootHeight_reflectionPerm_self S.pairing S.base S.J
      S.coeff S.simpleRootExpansion alpha.1
    rw [source_simple_support S] at hnegHeight
    rw [← hidx, hdeltaHeight, alpha.2.2] at hnegHeight
    have : (0 : ℤ) < S.height := by exact_mod_cast S.height_pos
    omega
  have hlin : LinearIndependent ℚ
      ![S.pairing.root delta, S.pairing.root alpha.1] :=
    RootPairing.IsReduced.linearIndependent (P := S.pairing) hne hnotopp
  rw [LinearIndependent.pair_iff] at hlin
  have hLI : AreLinearlyIndependentRoots S.D S.pairing
      (Equiv.refl S.D.Root) delta alpha.1 := by
    simpa [AreLinearlyIndependentRoots] using hlin
  rcases S.chevalleySystem.2.2.2.2.1 delta alpha.1 hLI with
    ⟨order, coefficient, hnodup, _hordered, hvalid, hcoefficient, hformula⟩
  let target : ChevalleyCommutatorTerm S.D.Root :=
    { i := n, j := 1, root := beta.1 }
  have htargetValid : IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) delta alpha.1 target := by
    refine ⟨hn, by simp [target], ?_⟩
    simpa [target, add_comm, Nat.cast_smul_eq_nsmul] using hroot
  have htargetMem : target ∈ order := (hvalid target).2 htargetValid
  have htargetCoefficient : coefficient target ≠ 0 :=
    S.expectedChevalleyCoefficient_ne_zero hNonsingular
      (hcoefficient target htargetMem)
  let Term := {q : ChevalleyCommutatorTerm S.D.Root // q ∈ order}
  let validTerm : ∀ q : Term, IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) delta alpha.1 q.1 := fun q =>
    (hvalid q.1).1 q.2
  let fiberTerm (q : Term) (hqj : q.1.j = 1) :
      {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root} :=
    ⟨q.1.root, valid_term_mem_fiber S hdelta alpha q.1 (validTerm q) hqj⟩
  let parameter (s a : k) (q : Term) : k :=
    coefficient q.1 * s ^ q.1.i * (-a) ^ q.1.j
  let layerTerm (s a : k) (q : Term) :
      sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
        S.coeff S.J S.height :=
    ⟨S.C.x q.1.root (parameter s a q),
      valid_term_root_element_mem_layer S hdelta alpha q.1
        (validTerm q) (parameter s a q)⟩
  let quotientTerm (s a : k) (q : Term) :
      relativeRootFiberQuotientSubgroup S :=
    if hqj : q.1.j = 1 then
      relativeRootFiberQuotientGenerator S
        (fiberTerm q hqj, parameter s a q)
    else 1
  have hquotientTerm (s a : k) (q : Term) :
      (quotientTerm s a q : relativeRootLayerQuotient S) =
        QuotientGroup.mk' _ (layerTerm s a q) := by
    by_cases hqj : q.1.j = 1
    · simp only [quotientTerm, dif_pos hqj,
        relativeRootFiberQuotientGenerator_coe]
      congr 1
      apply Subtype.ext
      rw [relativeRootLayerElement_coe]
    · simp only [quotientTerm, dif_neg hqj, Subgroup.coe_one]
      symm
      apply (QuotientGroup.eq_one_iff (layerTerm s a q)).2
      exact valid_term_root_element_mem_next_layer S hdelta alpha q.1
        (validTerm q) hqj (parameter s a q)
  have hxzero (gamma : S.D.Root) : S.C.x gamma 0 = 1 := by
    simpa using S.chevalleySystem.2.2.2.1 gamma 0 0
  have hxneg (gamma : S.D.Root) (a : k) :
      S.C.x gamma (-a) = (S.C.x gamma a)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [S.chevalleySystem.2.2.2.1 gamma (-a) a]
    simpa using hxzero gamma
  have hconjugate (s a : k) :
      (S.C.x delta s)⁻¹ * S.C.x alpha.1 a * S.C.x delta s =
        (order.map fun q =>
          S.C.x q.root (coefficient q * s ^ q.i * (-a) ^ q.j)).prod *
            S.C.x alpha.1 a := by
    have hcomm := hformula s (-a)
    rw [hxneg alpha.1 a] at hcomm
    simp only [inv_inv] at hcomm
    calc
      (S.C.x delta s)⁻¹ * S.C.x alpha.1 a * S.C.x delta s =
          ((S.C.x delta s)⁻¹ * S.C.x alpha.1 a * S.C.x delta s *
            (S.C.x alpha.1 a)⁻¹) * S.C.x alpha.1 a := by
              simp [mul_assoc]
      _ = (order.map fun q =>
          S.C.x q.root (coefficient q * s ^ q.i * (-a) ^ q.j)).prod *
            S.C.x alpha.1 a := by
              exact congrArg (fun x => x * S.C.x alpha.1 a) hcomm
  have hgenerator (s a : k) :
      M.conjugatedGenerator (chevalleyRootLeviPoint S delta hdelta s)⁻¹ (alpha, a) =
        (order.attach.map fun q => quotientTerm s a q).prod *
          relativeRootFiberQuotientGenerator S (alpha, a) := by
    apply Subtype.ext
    rcases M.conjugatedGenerator_inv_value
      (chevalleyRootLeviPoint S delta hdelta s) (alpha, a) with
      ⟨y, hy, hqy⟩
    let qmk : sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
        S.coeff S.J S.height →* relativeRootLayerQuotient S :=
      QuotientGroup.mk' _
    have hqy' :
        (M.conjugatedGenerator (chevalleyRootLeviPoint S delta hdelta s)⁻¹ (alpha, a) :
          relativeRootLayerQuotient S) = qmk y := hqy
    have hprod :
        (relativeRootFiberQuotientSubgroup S).subtype
            ((order.attach.map fun q => quotientTerm s a q).prod) =
          qmk ((order.attach.map fun q => layerTerm s a q).prod) := by
      induction order.attach with
      | nil => simp
      | cons q qs ih =>
          simp only [List.map_cons, List.prod_cons, map_mul]
          have hqterm :
              (relativeRootFiberQuotientSubgroup S).subtype (quotientTerm s a q) =
                qmk (layerTerm s a q) := hquotientTerm s a q
          rw [hqterm, ih]
    have hgen :
        (relativeRootFiberQuotientGenerator S (alpha, a) :
          relativeRootLayerQuotient S) =
        qmk (relativeRootLayerElement S alpha.1 alpha.2 a) :=
      relativeRootFiberQuotientGenerator_coe S (alpha, a)
    have hlayer : y =
        (order.attach.map fun q => layerTerm s a q).prod *
          relativeRootLayerElement S alpha.1 alpha.2 a := by
      apply Subtype.ext
      have hambientMap :
          (order.attach.map fun q => (layerTerm s a q : Variety.Point K)) =
            order.map fun q =>
              S.C.x q.root (coefficient q * s ^ q.i * (-a) ^ q.j) := by
        calc
          _ = order.attach.map (fun q =>
                S.C.x q.1.root
                  (coefficient q.1 * s ^ q.1.i * (-a) ^ q.1.j)) := by
              apply List.map_congr_left
              intro q hq
              rfl
          _ = _ := @List.attach_map_val _ _ order (fun q =>
            S.C.x q.root (coefficient q * s ^ q.i * (-a) ^ q.j))
      calc
        (y : Variety.Point K) =
            (S.L.includePoint (chevalleyRootLeviPoint S delta hdelta s))⁻¹ *
              S.C.x alpha.1 a *
                S.L.includePoint (chevalleyRootLeviPoint S delta hdelta s) := hy
        _ = (order.map fun q =>
              S.C.x q.root (coefficient q * s ^ q.i * (-a) ^ q.j)).prod *
                S.C.x alpha.1 a := by
              rw [chevalleyRootLeviPoint_include]
              exact hconjugate s a
        _ = (order.attach.map fun q =>
              (layerTerm s a q : Variety.Point K)).prod *
                S.C.x alpha.1 a := by rw [hambientMap]
        _ = (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
                S.coeff S.J S.height).subtype
              ((order.attach.map fun q => layerTerm s a q).prod) *
            (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
                S.coeff S.J S.height).subtype
              (relativeRootLayerElement S alpha.1 alpha.2 a) := by
                rw [map_list_prod, List.map_map]
                have hrel :
                    (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
                      S.coeff S.J S.height).subtype
                        (relativeRootLayerElement S alpha.1 alpha.2 a) =
                      S.C.x alpha.1 a :=
                  relativeRootLayerElement_coe S alpha.1 alpha.2 a
                rw [hrel]
                have hmaps :
                    (order.attach.map fun q =>
                      (layerTerm s a q : Variety.Point K)) =
                    order.attach.map
                      ((sourceRelativeRootLayer S.D
                        S.D.simple.toFinite.toFinset S.coeff S.J S.height).subtype ∘
                          fun q => layerTerm s a q) := by
                  apply List.map_congr_left
                  intro q hq
                  rfl
                rw [hmaps]
        _ = (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
                S.coeff S.J S.height).subtype
              ((order.attach.map fun q => layerTerm s a q).prod *
                relativeRootLayerElement S alpha.1 alpha.2 a) :=
            (map_mul (sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
              S.coeff S.J S.height).subtype _ _).symm
        _ = _ := rfl
    calc
      (M.conjugatedGenerator (chevalleyRootLeviPoint S delta hdelta s)⁻¹ (alpha, a) :
          relativeRootLayerQuotient S) = qmk y := hqy'
      _ = qmk
          ((order.attach.map fun q => layerTerm s a q).prod *
            relativeRootLayerElement S alpha.1 alpha.2 a) := congrArg qmk hlayer
      _ = qmk ((order.attach.map fun q => layerTerm s a q).prod) *
          qmk (relativeRootLayerElement S alpha.1 alpha.2 a) := by
              exact map_mul qmk _ _
      _ = (relativeRootFiberQuotientSubgroup S).subtype
            ((order.attach.map fun q => quotientTerm s a q).prod) *
          (relativeRootFiberQuotientGenerator S (alpha, a) :
            relativeRootLayerQuotient S) := congrArg₂ (· * ·) hprod.symm hgen.symm
      _ = (relativeRootFiberQuotientSubgroup S).subtype
          ((order.attach.map fun q => quotientTerm s a q).prod *
            relativeRootFiberQuotientGenerator S (alpha, a)) :=
        (map_mul (relativeRootFiberQuotientSubgroup S).subtype
          ((order.attach.map fun q => quotientTerm s a q).prod)
          (relativeRootFiberQuotientGenerator S (alpha, a))).symm
      _ = _ := rfl
  let baseVector (a : k) (q : Term) : M.V :=
    if hqj : q.1.j = 1 then
      M.rootVector (fiberTerm q hqj, coefficient q.1 * (-a))
    else 0
  have hterm (s a : k) (q : Term) :
      Multiplicative.toAdd (M.pointEquiv (quotientTerm s a q)) =
        s ^ q.1.i • baseVector a q := by
    by_cases hqj : q.1.j = 1
    · simp only [quotientTerm, dif_pos hqj, baseVector]
      rw [← M.rootVector_value]
      rw [show parameter s a q = s ^ q.1.i * (coefficient q.1 * (-a)) by
        simp [parameter, hqj]
        ring]
      rw [M.rootVector_smul]
    · simp [quotientTerm, baseVector, hqj]
  have haction (s a : k) :
      (M.representation.action (chevalleyRootLeviPoint S delta hdelta s)⁻¹).1
          (M.rootVector (alpha, a)) =
        (order.attach.map fun q => s ^ q.1.i • baseVector a q).sum +
          M.rootVector (alpha, a) := by
    have hagree := M.representation_agrees_with_conjugation
      (chevalleyRootLeviPoint S delta hdelta s)⁻¹
      (relativeRootFiberQuotientGenerator S (alpha, a))
    rw [M.conjugationAction_generator, hgenerator s a] at hagree
    have hadd := congrArg Multiplicative.toAdd hagree.symm
    simp only [map_mul, map_list_prod, List.map_map, toAdd_mul, toAdd_ofAdd] at hadd
    have hsum :
        Multiplicative.toAdd
            ((order.attach.map fun q => M.pointEquiv (quotientTerm s a q)).prod) =
          (order.attach.map fun q => s ^ q.1.i • baseVector a q).sum := by
      induction order.attach with
      | nil => rfl
      | cons q qs ih =>
          simp only [List.map_cons, List.prod_cons, List.sum_cons, toAdd_mul]
          rw [hterm s a q, ih]
    have hsum' :
        Multiplicative.toAdd
            ((order.attach.map
              (M.pointEquiv ∘ fun q => quotientTerm s a q)).prod) =
          (order.attach.map fun q => s ^ q.1.i • baseVector a q).sum := by
      rw [show (order.attach.map
          (M.pointEquiv ∘ fun q => quotientTerm s a q)) =
          (order.attach.map fun q => M.pointEquiv (quotientTerm s a q)) by
        apply List.map_congr_left
        intro q hq
        rfl]
      exact hsum
    rw [M.rootVector_value, hadd, hsum']
  have hevaluation (s a : k) :
      (order.attach.map fun q => s ^ q.1.i • baseVector a q).sum ∈ W := by
    have hacted := hW (chevalleyRootLeviPoint S delta hdelta s)⁻¹
      (M.rootVector (alpha, a)) (halpha a)
    rw [haction s a] at hacted
    simpa only [add_sub_cancel_right] using W.sub_mem hacted (halpha a)
  let degreeCount : ℕ := (order.map fun q => q.i).sum + 1
  have hdegree (q : Term) : q.1.i < degreeCount := by
    apply Nat.lt_succ_of_le
    apply List.le_sum_of_mem
    exact List.mem_map.mpr ⟨q.1, q.2, rfl⟩
  let degree (q : Term) : Fin degreeCount := ⟨q.1.i, hdegree q⟩
  let terms : Finset Term := order.attach.toFinset
  let coefficientVector (a : k) (r : Fin degreeCount) : M.V :=
    ∑ q ∈ terms, if degree q = r then baseVector a q else 0
  have hpolynomial (s a : k) :
      ∑ r : Fin degreeCount, s ^ (r : ℕ) • coefficientVector a r =
        (order.attach.map fun q => s ^ q.1.i • baseVector a q).sum := by
    rw [← List.sum_toFinset _ hnodup.attach]
    simp only [coefficientVector, Finset.smul_sum, smul_ite, smul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_eq_single (degree q)]
    · simp [degree]
    · intro r _ hr
      simp [hr.symm]
    · intro h
      exact (h (Finset.mem_univ (degree q))).elim
  let targetTerm : Term := ⟨target, htargetMem⟩
  have htargetDegree : degree targetTerm = ⟨n, hdegree targetTerm⟩ := rfl
  have hsame_of_degree_of_j_one (q : Term) (hqi : degree q = degree targetTerm)
      (hqj : q.1.j = 1) : q = targetTerm := by
    apply Subtype.ext
    rw [ChevalleyCommutatorTerm.mk.injEq]
    refine ⟨Fin.ext_iff.mp hqi, ?_, ?_⟩
    · simpa [target] using hqj
    · apply S.pairing.root.injective
      have hqroot := (validTerm q).2.2
      simp only [Equiv.refl_apply, hqj, Nat.cast_one, one_smul] at hqroot
      rw [hqroot, hroot]
      have hqin : q.1.i = n := Fin.ext_iff.mp hqi
      rw [hqin]
      rw [Nat.cast_smul_eq_nsmul]
      abel
  have htargetVector (a : k) :
      coefficientVector a (degree targetTerm) =
        M.rootVector (beta, coefficient target * (-a)) := by
    simp only [coefficientVector]
    rw [Finset.sum_eq_single targetTerm]
    · simp [targetTerm, target, baseVector, fiberTerm]
    · intro q hq hqne
      by_cases hqi : degree q = degree targetTerm
      · have hqj : q.1.j ≠ 1 := by
          intro hj
          exact hqne (hsame_of_degree_of_j_one q hqi hj)
        simp [hqi, baseVector, hqj]
      · simp [hqi]
    · intro hnotmem
      apply (hnotmem ?_).elim
      simpa only [terms, List.mem_toFinset] using
        List.mem_attach order targetTerm
  have htargetVectorMem (a : k) :
      M.rootVector (beta, coefficient target * (-a)) ∈ W := by
    rw [← htargetVector a]
    exact W.coeff_mem_of_sum_pow_smul_mem (coefficientVector a)
      (fun i : Fin degreeCount => Infinite.natEmbedding k i.1)
      ((Infinite.natEmbedding k).injective.comp Fin.val_injective)
      (fun i => by
        rw [hpolynomial]
        exact hevaluation _ a)
      (degree targetTerm)
  intro t
  let a : k := -((coefficient target)⁻¹ * t)
  have ha : coefficient target * (-a) = t := by
    simp only [a, neg_neg]
    field_simp
  rw [← ha]
  exact htargetVectorMem a

public theorem RelativeRootFiberModule.rootVector_mem_of_levi_root_string
    (S : RelativeRootRepresentationSource K) (M : RelativeRootFiberModule S)
    (hNonsingular : ¬ IsUSingular S.classification (ringChar k))
    (W : Submodule k M.V) (hW : IsInvariantSubmodule M.representation W)
    {alpha beta : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}}
    (hstring : ∃ delta : S.D.Root, delta ∈ RootSubsystemSpan S.D S.J ∧
      ∃ n : ℤ, S.pairing.root beta.1 =
        S.pairing.root alpha.1 + n • S.pairing.root delta)
    (halpha : ∀ t, M.rootVector (alpha, t) ∈ W) :
    ∀ t, M.rootVector (beta, t) ∈ W := by
  rcases hstring with ⟨delta, hdelta, n, hroot⟩
  cases n with
  | ofNat n =>
      cases n with
      | zero =>
          simp only [Int.ofNat_eq_natCast, Nat.cast_zero, zero_zsmul, add_zero] at hroot
          have hab : beta = alpha :=
            Subtype.ext (S.pairing.root.injective hroot)
          subst beta
          exact halpha
      | succ n =>
          simp only [Int.ofNat_eq_natCast, natCast_zsmul] at hroot
          exact root_string_action_nat S M hNonsingular W hW alpha beta delta hdelta
            (n + 1) (Nat.zero_lt_succ n) hroot halpha
  | negSucc n =>
      let deltaNeg : S.D.Root := S.D.neg delta
      have hdeltaNeg : deltaNeg ∈ RootSubsystemSpan S.D S.J := by
        change S.D.rootWeight delta ∈
          Subgroup.closure (S.D.rootWeight '' S.J) at hdelta
        change S.D.rootWeight (S.D.neg delta) ∈
          Subgroup.closure (S.D.rootWeight '' S.J)
        rw [S.isRealization.2.2.2.1 delta]
        exact Subgroup.inv_mem _ hdelta
      have hrootNeg : S.pairing.root deltaNeg = -S.pairing.root delta := by
        change S.pairing.root (S.D.neg delta) = -S.pairing.root delta
        rw [show S.D.neg delta = S.pairing.reflectionPerm delta delta by
          simpa using S.rootSystemRealization.2.2.1 delta]
        rw [S.pairing.root_reflectionPerm, S.pairing.reflection_apply_self]
      simp only [negSucc_zsmul] at hroot
      exact root_string_action_nat S M hNonsingular W hW alpha beta deltaNeg
        hdeltaNeg (n + 1) (Nat.zero_lt_succ n) (by
          rw [hroot, hrootNeg]
          simp) halpha

end Theory.AlgebraicGroup
