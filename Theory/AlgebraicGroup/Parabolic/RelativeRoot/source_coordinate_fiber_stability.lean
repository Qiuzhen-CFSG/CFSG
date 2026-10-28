module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.SourceLayerCoordinateModel
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.SourceQuotientCoordinateRegularity
public import Theory.AlgebraicGroup.Bor1.NormalWeights

/-!
Coordinate stability of the source relative-root fiber.

The exact-height source quotient is modeled by coordinate functions indexed by
the height fiber.  The submodule of vectors supported on that fiber is
equipped with membership and single-coordinate specifications for downstream
coordinate models.  It is
preserved by source torus points and by every Levi root generator: the
surviving Chevalley commutator terms have the same projected root.  The
rational coordinate representation and its Zariski-closed subspace stabilizer
then extend this preservation from the aligned generators to all source-Levi
points.  This is the coordinate-stability step in the relative-root module
construction following GLS3, Section 1.14.
-/

universe u
namespace Theory.AlgebraicGroup
open Set
local notation "Submodule" => _root_.Submodule
set_option linter.style.haveILetI false
variable {k : Type u} [Field k] [IsAlgClosed k]

public noncomputable def sourceRelativeRootFiberCoordinateSubmodule {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Submodule k (RelativeRootSourceExactIndex S → k) :=
  { carrier := {v | ∀ eta, eta.1 ∉ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root → v eta = 0}
    zero_mem' := by intro eta h; simp
    add_mem' := by intro v w hv hw eta h; simp [hv eta h, hw eta h]
    smul_mem' := by intro c v hv eta h; simp [hv eta h] }

omit [IsAlgClosed k] in
/-- Membership in the fiber coordinate submodule is exactly vanishing off the
selected relative-root fiber. -/
public theorem sourceRelativeRootFiberCoordinateSubmodule_mem_iff
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (v : RelativeRootSourceExactIndex S → k) :
    v ∈ sourceRelativeRootFiberCoordinateSubmodule S ↔
      ∀ eta, eta.1 ∉ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root → v eta = 0 := by
  rfl

omit [IsAlgClosed k] in
/-- A single exact-height coordinate supported at a fiber root belongs to the
fiber coordinate submodule. -/
public theorem sourceRelativeRootFiberCoordinateSubmodule_single_mem {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root}) (t : k) :
    letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
    Pi.single (⟨gamma.1, gamma.2.2⟩ : RelativeRootSourceExactIndex S) t ∈
      sourceRelativeRootFiberCoordinateSubmodule S := by
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  intro eta heta
  by_cases h : eta = ⟨gamma.1, gamma.2.2⟩
  · subst eta
    exact (heta gamma.2).elim
  · simp [Pi.single, h]

private lemma sourceRelativeRootFiberCoordinateSubmodule_projection_eq_of_root_sub_mem_span
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
  have base_coeff_coord
      (a x : ι) (hx : x ∈ base.support) :
      (base.toWeightBasis.repr (P.root a)) ⟨x, hx⟩ = (coeff a x : ℚ) := by
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
    · intro y hy hyx
      simp [hyx]
  have root_span_coord_zero (z : M)
      (hz : z ∈ Submodule.span ℚ (P.root '' J))
      (x : ι) (hx : x ∈ base.support) (hxJ : x ∉ J) :
      (base.toWeightBasis.repr z) ⟨x, hx⟩ = 0 := by
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
  apply Finsupp.ext
  intro x
  by_cases hx : x ∈ base.support
  · by_cases hxJ : x ∈ J
    · simp [RelativeRootProjection, hx, hxJ]
    · have hcoord := root_span_coord_zero (P.root a - P.root b) hspan x hx hxJ
      have ha := base_coeff_coord a x hx
      have hb := base_coeff_coord b x hx
      have hzero : coeff a x = coeff b x := by
        have hz : (coeff a x : ℚ) - (coeff b x : ℚ) = 0 := by
          simpa [map_sub, ha, hb] using hcoord
        exact_mod_cast sub_eq_zero.mp hz
      simp [RelativeRootProjection, hx, hxJ, hzero]
  · simp [RelativeRootProjection, hx]

private lemma sourceRelativeRootFiberCoordinateSubmodule_valid_mem_fiber {K : Variety k} [AlgebraicGroup K]
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
  have hJ : S.J ⊆ S.base.support := by
    intro j hj
    exact (S.rootSystemRealization.2.2.2.1 j).mp (S.J_simple hj)
  have hprojection := sourceRelativeRootFiberCoordinateSubmodule_projection_eq_of_root_sub_mem_span S.pairing S.base S.J
    hJ S.coeff S.simpleRootExpansion hspan
  have hheightDelta := S.relativeRootHeight_eq_zero_of_mem_rootSubsystemSpan hdelta
  have hheight := relativeRootHeight_of_validChevalleyCommutatorTerm
    S.D S.pairing (Equiv.refl S.D.Root) S.base S.J S.coeff
      S.simpleRootExpansion q hvalid
  have hbase : S.base.support = S.D.simple.toFinite.toFinset := by
    ext gamma
    simp only [Set.Finite.mem_toFinset]
    exact (S.rootSystemRealization.2.2.2.1 gamma).symm
  rw [hbase] at hheight
  simp only [Equiv.refl_apply] at hheight
  have hqheight : RelativeRootHeight S.coeff
      S.D.simple.toFinite.toFinset S.J q.root = S.height := by
    rw [hheight, hheightDelta, alpha.2.2, hqj]
    simp
  refine ⟨⟨Set.mem_univ _, ?_⟩, hqheight⟩
  have hbaseSet : (S.base.support : Set S.D.Root) = S.D.simple := by
    ext gamma
    exact (S.rootSystemRealization.2.2.2.1 gamma).symm
  rw [← hbaseSet]
  exact hprojection.trans (by
    rw [hbaseSet]
    exact alpha.2.1.2)

omit [IsAlgClosed k] in
private lemma sourceRelativeRootFiberCoordinateSubmodule_sum_single {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (v : RelativeRootSourceExactIndex S → k) :
    letI : Finite (RelativeRootSourceExactIndex S) := by infer_instance
    letI : Fintype (RelativeRootSourceExactIndex S) :=
      Fintype.ofFinite _
    letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
    v = ∑ gamma, Pi.single gamma (v gamma) := by
  classical
  letI : Finite (RelativeRootSourceExactIndex S) := by infer_instance
  letI := Fintype.ofFinite (RelativeRootSourceExactIndex S)
  funext eta
  simp

private lemma sourceRelativeRootFiberCoordinateSubmodule_torus_preserves {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (s : Variety.Point S.T.carrierVariety) :
    ∀ v, v ∈ sourceRelativeRootFiberCoordinateSubmodule S →
      sourceCoordinateActionValue S (sourceTorusLeviPoint S s) v ∈ sourceRelativeRootFiberCoordinateSubmodule S := by
  classical
  letI : Finite (RelativeRootSourceExactIndex S) := by infer_instance
  letI := Fintype.ofFinite (RelativeRootSourceExactIndex S)
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  intro v hv
  rw [sourceRelativeRootFiberCoordinateSubmodule_sum_single S v]
  rw [← S.sourceLayerCarrierCoordinateLinearAction_apply]
  rw [map_sum]
  apply Submodule.sum_mem
  intro gamma hgamma
  rw [S.sourceLayerCarrierCoordinateLinearAction_apply]
  by_cases hF : gamma.1 ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root
  · let gammaF : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root} := ⟨gamma.1, hF⟩
    rw [sourceCoordinateConjugation_torus_single]
    simpa using sourceRelativeRootFiberCoordinateSubmodule_single_mem S gammaF
      (((S.D.rootWeight gamma.1).pointCharacter s)⁻¹ * v gamma)
  · have hvzero : v gamma = 0 := hv gamma hF
    rw [sourceCoordinateConjugation_torus_single]
    simp [hvzero]

private lemma sourceRelativeRootFiberCoordinateSubmodule_root_preserves {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (delta : S.D.Root) (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (s : k) :
    ∀ v, v ∈ sourceRelativeRootFiberCoordinateSubmodule S →
      sourceCoordinateActionValue S (sourceLeviRootPoint S delta hdelta s) v ∈ sourceRelativeRootFiberCoordinateSubmodule S := by
  classical
  letI : Finite (RelativeRootSourceExactIndex S) := by infer_instance
  letI := Fintype.ofFinite (RelativeRootSourceExactIndex S)
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  letI : DecidableEq S.D.Root := Classical.decEq _
  intro v hv
  rw [sourceRelativeRootFiberCoordinateSubmodule_sum_single S v]
  rw [← S.sourceLayerCarrierCoordinateLinearAction_apply]
  rw [map_sum]
  apply Submodule.sum_mem
  intro gamma hgamma
  rw [S.sourceLayerCarrierCoordinateLinearAction_apply]
  by_cases hF : gamma.1 ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root
  · let gammaF : {gamma : S.D.Root // gamma ∈ relativeRootFiberAtHeight
        S.D S.coeff S.J S.height S.root} := ⟨gamma.1, hF⟩
    rcases sourceCoordinateConjugation_root_single S delta hdelta gamma with
      ⟨order, coefficient, hnodup, hvalid, hcoeff, hformula⟩
    rw [hformula]
    change ∀ (eta : RelativeRootSourceExactIndex S), eta.1 ∉ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root → _
    intro eta heta
    simp only [Pi.add_apply]
    have hsum : ∀ (xs : List (RelativeRootSourceExactIndex S → k)),
        xs.sum eta = (xs.map (fun f => f eta)).sum := by
      intro xs
      induction xs with
      | nil => rfl
      | cons f fs ih => simp [ih]
    have hne : eta ≠ gamma := by
      intro h
      subst eta
      exact heta hF
    rw [hsum]
    induction order.attach with
    | nil => simp [Pi.single, hne]
    | cons q qs ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [add_assoc, ih]
        by_cases hqj : q.1.j = 1
        · by_cases hqr : q.1.root = eta.1
          · have hqF := sourceRelativeRootFiberCoordinateSubmodule_valid_mem_fiber S hdelta
                ⟨gamma.1, hF⟩ q.1
                ((hvalid q.1).1 q.2) hqj
            exact (heta (by simpa [hqr] using hqF)).elim
          · simp [hqr]
        · simp [hqj]
  · have hvzero : v gamma = 0 := hv gamma hF
    rw [show (Pi.single gamma (v gamma) : RelativeRootSourceExactIndex S → k) = 0 by
      ext eta
      by_cases h : eta = gamma
      · subst eta
        simp [hvzero]
      · simp [Pi.single, h]]
    rw [← S.sourceLayerCarrierCoordinateLinearAction_apply]
    simp

private lemma sourceRelativeRootFiberCoordinateSubmodule_map_eq_of_preserves {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (hpres : ∀ v, v ∈ sourceRelativeRootFiberCoordinateSubmodule S →
      sourceCoordinateActionValue S l v ∈ sourceRelativeRootFiberCoordinateSubmodule S) :
    Submodule.map
      (S.sourceLayerCoordinateRationalRepresentation.action l : Module.End k
        (RelativeRootSourceExactIndex S → k)) (sourceRelativeRootFiberCoordinateSubmodule S) = sourceRelativeRootFiberCoordinateSubmodule S := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.map_le_iff_le_comap]
    intro v hv
    have h := hpres v hv
    rw [← S.sourceLayerCarrierCoordinateLinearAction_apply] at h
    exact h
  · exact LinearEquiv.finrank_map_eq
      ((S.sourceLayerCoordinateRationalRepresentation.action l).toLinearEquiv)
      (sourceRelativeRootFiberCoordinateSubmodule S)

public theorem sourceRelativeRootFiberCoordinateSubmodule_stable {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    ∀ l : Variety.Point S.L.carrierVariety,
      Submodule.map
        (S.sourceLayerCoordinateRationalRepresentation.action l : Module.End k
          (RelativeRootSourceExactIndex S → k)) (sourceRelativeRootFiberCoordinateSubmodule S) = sourceRelativeRootFiberCoordinateSubmodule S := by
  classical
  letI := Fintype.ofFinite (RelativeRootSourceExactIndex S)
  have sourceRootSubsystemSpan_neg_mem
      {delta : S.D.Root} (hdelta : delta ∈ RootSubsystemSpan S.D S.J) :
      S.D.neg delta ∈ RootSubsystemSpan S.D S.J := by
    letI := Fintype.ofFinite S.D.Root
    apply (S.root_mem_span_iff_mem_rootSubsystemSpan (S.D.neg delta)).mp
    have hspan := (S.root_mem_span_iff_mem_rootSubsystemSpan delta).mpr hdelta
    have hnegroot : S.pairing.root (S.D.neg delta) =
        -S.pairing.root delta := by
      calc
        S.pairing.root (S.D.neg delta) =
            S.pairing.root (S.pairing.reflectionPerm delta delta) := by
          congr 1
          simpa using S.rootSystemRealization.2.2.1 delta
        _ = -S.pairing.root delta := by
          rw [S.pairing.root_reflectionPerm, S.pairing.reflection_apply_self]
    rw [hnegroot]
    exact Submodule.neg_mem _ hspan
  let Z : Set (Variety.Point S.L.carrierVariety) :=
    {l | Submodule.map
      (S.sourceLayerCoordinateRationalRepresentation.action l : Module.End k
        (RelativeRootSourceExactIndex S → k)) (sourceRelativeRootFiberCoordinateSubmodule S) = sourceRelativeRootFiberCoordinateSubmodule S}
  have hZclosed : IsZariskiClosed S.L.carrierVariety Z := by
    exact Bor1.RationalRepresentation.subspaceStabilizer_isZariskiClosed_Bor1
      S.sourceLayerCoordinateRationalRepresentation
      S.sourceLayerCoordinateRationalRepresentation_isRational (sourceRelativeRootFiberCoordinateSubmodule S)
  have hZambient : IsZariskiClosed K (S.L.includePoint '' Z) := by
    change IsZariskiClosed K
      ((fun y : Variety.Point S.L.carrierVariety =>
        (Variety.closedSubvarietyPointEquiv S.L.isZariskiClosed y).1) '' Z)
    exact closedSubvariety_image_isZariskiClosed S.L.isZariskiClosed hZclosed
  let H : Subgroup (Variety.Point S.L.carrierVariety) := {
    carrier := Z
    one_mem' := by
      change Submodule.map
        (S.sourceLayerCoordinateRationalRepresentation.action 1 : Module.End k
          (RelativeRootSourceExactIndex S → k)) (sourceRelativeRootFiberCoordinateSubmodule S) = sourceRelativeRootFiberCoordinateSubmodule S
      apply le_antisymm
      · rw [Submodule.map_le_iff_le_comap]
        intro v hv
        simpa using hv
      · intro v hv
        rw [Submodule.mem_map]
        refine ⟨v, hv, ?_⟩
        simp
    mul_mem' := by
      intro x y hx hy
      change Submodule.map
        (S.sourceLayerCoordinateRationalRepresentation.action (x * y) : Module.End k
          (RelativeRootSourceExactIndex S → k)) (sourceRelativeRootFiberCoordinateSubmodule S) = sourceRelativeRootFiberCoordinateSubmodule S
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.map_le_iff_le_comap]
        intro v hv
        change (S.sourceLayerCoordinateRationalRepresentation.action (x * y) : Module.End k
          (RelativeRootSourceExactIndex S → k)) v ∈ sourceRelativeRootFiberCoordinateSubmodule S
        rw [map_mul]
        have hyv : (S.sourceLayerCoordinateRationalRepresentation.action y : Module.End k
            (RelativeRootSourceExactIndex S → k)) v ∈ sourceRelativeRootFiberCoordinateSubmodule S := by
          have hm : (S.sourceLayerCoordinateRationalRepresentation.action y : Module.End k
              (RelativeRootSourceExactIndex S → k)) v ∈ Submodule.map
                (S.sourceLayerCoordinateRationalRepresentation.action y : Module.End k
                  (RelativeRootSourceExactIndex S → k)) (sourceRelativeRootFiberCoordinateSubmodule S) :=
            Submodule.mem_map_of_mem hv
          rw [hy] at hm
          exact hm
        have hxm : (S.sourceLayerCoordinateRationalRepresentation.action x : Module.End k
            (RelativeRootSourceExactIndex S → k))
            ((S.sourceLayerCoordinateRationalRepresentation.action y : Module.End k
              (RelativeRootSourceExactIndex S → k)) v) ∈ sourceRelativeRootFiberCoordinateSubmodule S := by
          have hm : (S.sourceLayerCoordinateRationalRepresentation.action x : Module.End k
              (RelativeRootSourceExactIndex S → k))
              ((S.sourceLayerCoordinateRationalRepresentation.action y : Module.End k
                (RelativeRootSourceExactIndex S → k)) v) ∈ Submodule.map
                  (S.sourceLayerCoordinateRationalRepresentation.action x : Module.End k
                    (RelativeRootSourceExactIndex S → k)) (sourceRelativeRootFiberCoordinateSubmodule S) :=
            Submodule.mem_map_of_mem hyv
          rw [hx] at hm
          exact hm
        exact hxm
      · exact LinearEquiv.finrank_map_eq
          ((S.sourceLayerCoordinateRationalRepresentation.action (x * y)).toLinearEquiv)
          (sourceRelativeRootFiberCoordinateSubmodule S)
    inv_mem' := by
      intro x hx
      change Submodule.map
        (S.sourceLayerCoordinateRationalRepresentation.action x⁻¹ : Module.End k
          (RelativeRootSourceExactIndex S → k)) (sourceRelativeRootFiberCoordinateSubmodule S) = sourceRelativeRootFiberCoordinateSubmodule S
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.map_le_iff_le_comap]
        intro v hv
        have hm : v ∈ Submodule.map
            (S.sourceLayerCoordinateRationalRepresentation.action x : Module.End k
              (RelativeRootSourceExactIndex S → k)) (sourceRelativeRootFiberCoordinateSubmodule S) := by
          rw [hx]
          exact hv
        rcases hm with ⟨u, hu, heq⟩
        have heq' : (S.sourceLayerCoordinateRationalRepresentation.action x⁻¹ : Module.End k
            (RelativeRootSourceExactIndex S → k)) v = u := by
          rw [← heq]
          rw [map_inv]
          exact (S.sourceLayerCoordinateRationalRepresentation.action x).toLinearEquiv.left_inv u
        change (S.sourceLayerCoordinateRationalRepresentation.action x⁻¹ : Module.End k
          (RelativeRootSourceExactIndex S → k)) v ∈ sourceRelativeRootFiberCoordinateSubmodule S
        rw [heq']
        exact hu
      · exact LinearEquiv.finrank_map_eq
          ((S.sourceLayerCoordinateRationalRepresentation.action x⁻¹).toLinearEquiv)
          (sourceRelativeRootFiberCoordinateSubmodule S)
  }
  have hrootfactor : standardLeviRootFactor S.D (RootSubsystemSpan S.D S.J) ≤
      H.map S.L.inclusion.onPoints := by
    rw [standardLeviRootFactor, RootSubgroupGenerated_le_iff]
    intro delta hdelta x hx
    have hdeltaSpan : delta ∈ RootSubsystemSpan S.D S.J := by
      rcases hdelta with hdelta | ⟨beta, hbeta, rfl⟩
      · exact hdelta
      · exact sourceRootSubsystemSpan_neg_mem hbeta
    have hxrange : x ∈ Set.range (S.C.x delta) := by
      rw [(S.chevalleySystem.1 delta).2]
      exact hx
    rcases hxrange with ⟨s, rfl⟩
    change S.C.x delta s ∈ H.map S.L.inclusion.onPoints
    refine ⟨sourceLeviRootPoint S delta hdeltaSpan s, ?_, ?_⟩
    · exact sourceRelativeRootFiberCoordinateSubmodule_map_eq_of_preserves S _
        (sourceRelativeRootFiberCoordinateSubmodule_root_preserves S delta hdeltaSpan s)
    · exact sourceLeviRootPoint_include S delta hdeltaSpan s
  have htorus : S.T.toSubgroup ≤ H.map S.L.inclusion.onPoints := by
    intro x hx
    let s : Variety.Point S.T.carrierVariety := S.T.pointEquiv.symm ⟨x, hx⟩
    have hs : S.T.includePoint s = x := by
      change (S.T.pointEquiv (S.T.pointEquiv.symm ⟨x, hx⟩)).1 = x
      rw [S.T.pointEquiv.apply_symm_apply]
    refine ⟨sourceTorusLeviPoint S s, ?_, ?_⟩
    · exact sourceRelativeRootFiberCoordinateSubmodule_map_eq_of_preserves S _ (sourceRelativeRootFiberCoordinateSubmodule_torus_preserves S s)
    · exact hs ▸ sourceTorusLeviPoint_include S s
  have hraw :
      ((S.T : Set (Variety.Point K)) ∪
        standardLeviRootFactor S.D (RootSubsystemSpan S.D S.J)) ⊆
        (H.map S.L.inclusion.onPoints : Set (Variety.Point K)) := by
    intro x hx
    rcases hx with hx | hx
    · exact htorus hx
    · exact hrootfactor hx
  have hgen : Subgroup.closure
      ((S.T : Set (Variety.Point K)) ∪
        standardLeviRootFactor S.D (RootSubsystemSpan S.D S.J)) ≤
      H.map S.L.inclusion.onPoints := (Subgroup.closure_le _).mpr hraw
  have hmapcarrier :
      (H.map S.L.inclusion.onPoints : Set (Variety.Point K)) =
        S.L.includePoint '' Z := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l, hl, rfl⟩
  have hAclosed : IsZariskiClosed K
      (H.map S.L.inclusion.onPoints : Set (Variety.Point K)) := by
    rw [hmapcarrier]
    exact hZambient
  have hclosure : ∀ x ∈ closure
      ((Subgroup.closure ((S.T : Set (Variety.Point K)) ∪
        standardLeviRootFactor S.D (RootSubsystemSpan S.D S.J)) :
          Set (Variety.Point K))),
      x ∈ (H.map S.L.inclusion.onPoints : Set (Variety.Point K)) := by
    intro x hx
    exact closure_minimal hgen
      (Variety.isClosed_iff_isZariskiClosed.mpr hAclosed) hx
  intro l
  have hlclosure : S.L.includePoint l ∈ closure
      ((Subgroup.closure ((S.T : Set (Variety.Point K)) ∪
        standardLeviRootFactor S.D (RootSubsystemSpan S.D S.J)) :
          Set (Variety.Point K))) := by
    have hlmem : S.L.includePoint l ∈ S.L.toClosedSubgroup.toSubgroup :=
      (S.L.pointEquiv l).2
    have halign : S.L.toClosedSubgroup.toSubgroup =
        (subgroupZariskiClosure K
          (Subgroup.closure ((S.T : Set (Variety.Point K)) ∪
            standardLeviRootFactor S.D (RootSubsystemSpan S.D S.J)))).toSubgroup := by
      exact congrArg (fun H : ClosedSubgroup K => H.toClosedSubgroup.toSubgroup)
        S.levi_alignment
    rw [halign] at hlmem
    dsimp [subgroupZariskiClosure, ClosedSubgroup.ofSubgroup] at hlmem
    exact hlmem
  rcases hclosure _ hlclosure with ⟨l', hl', heq⟩
  have hl'eq : l' = l := by
    apply S.L.pointEquiv.injective
    apply Subtype.ext
    exact heq
  simpa [H, Z, hl'eq] using hl'

end Theory.AlgebraicGroup
