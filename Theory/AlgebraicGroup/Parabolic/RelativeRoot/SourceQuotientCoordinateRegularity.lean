module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.SourceLayerCoordinateQuotient
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.SourceQuotientConjugation
public import Theory.AlgebraicGroup.Representations.Matrix

/-!
Regular source-Levi conjugation on exact relative-root coordinates.

For a `RelativeRootRepresentationSource S`, the exact-height source layer
quotient is identified with the coordinate space indexed by roots of height
`S.height`.  This module proves that the transported source-Levi conjugation
acts by linear automorphisms and that their matrix entries vary regularly.

The proof first computes conjugation on coordinate basis vectors.  Source
torus points scale a root coordinate by the inverse root character.  A source
Levi root element acts by the height-preserving terms of the Chevalley
commutator formula; modulo the next layer, precisely the terms with second
exponent one survive.  These generator computations give linearity on the
abstract source-Levi generators.  Polynomial coordinate columns and the
closed source-layer normalizer interface then extend linearity through the
Zariski closure identified with `S.L` by `S.levi_alignment`.

Finally, the regular coordinate columns are assembled into matrix and inverse
matrix coefficients.  They define an algebraic-group morphism to
`glVarietyOf`, hence a `RationalRepresentation`, with a computation theorem
that recovers ambient conjugation on every `QuotientGroup.mk'` class.  The
argument is entirely source-level and does not use the later relative-root
fiber module or the numbered representation theorems.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private def Variety.Morphism.codRestrictClosedSubgroup'
    {X K : Variety k} [AlgebraicGroup K]
    (f : Variety.Morphism X K) (H : ClosedSubgroup K)
    (hmap : ∀ x, f.toFun x ∈ H.toSubgroup) :
    Variety.Morphism X H.carrierVariety where
  toFun := fun x => H.pointEquiv.symm ⟨f.toFun x, hmap x⟩
  regular := by
    intro i
    rcases f.regular i with ⟨p, hp⟩
    refine ⟨p, fun x => ?_⟩
    change (H.pointEquiv (H.pointEquiv.symm ⟨f.toFun x, hmap x⟩)).val.val i =
      evalPolynomial x.val p
    rw [H.pointEquiv.apply_symm_apply]
    exact hp x

omit [IsAlgClosed k] in
private theorem sourceExactRootElement_mem_layer
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) (t : k) :
    S.C.x gamma.1 t ∈ sourceRelativeRootLayer S.D
      S.D.simple.toFinite.toFinset S.coeff S.J S.height := by
  rw [sourceRelativeRootLayer, RelativeRootSeries, RootSubgroupGenerated]
  apply Subgroup.subset_closure
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨gamma.1, ?_, ?_⟩
  · have hgamma : relativeRootSourceHeight S gamma.1 = S.height := gamma.2
    simpa [relativeRootSourceHeight] using
      (show (S.height : Int) ≤ relativeRootSourceHeight S gamma.1 by omega)
  · rw [← (S.chevalleySystem.1 gamma.1).2]
    exact ⟨t, rfl⟩

private noncomputable def sourceConjugationLayerColumnMorphism
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) (t : k) :
    Variety.Morphism S.L.carrierVariety
      (S.sourceSimpleLayerClosedSubgroup S.height).carrierVariety := by
  let c := (AlgebraicGroup.conjugateMorphism K (S.C.x gamma.1 t)).comp
    S.L.inclusion.toVariety
  exact c.codRestrictClosedSubgroup'
    (S.sourceSimpleLayerClosedSubgroup S.height) (fun l => by
      change S.L.includePoint l * S.C.x gamma.1 t * (S.L.includePoint l)⁻¹ ∈
        sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
          S.coeff S.J S.height
      have hnorm := S.levi_le_sourceRelativeRootLayer_normalizer S.height
        (S.L.pointEquiv l).2
      rw [Subgroup.mem_normalizer_iff] at hnorm
      exact (hnorm _).mp (sourceExactRootElement_mem_layer S gamma t))

private noncomputable def sourceCoordinateConjugationColumnMorphism
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) (t : k) :
    letI := S.coordinateAlgebraicGroup
    Variety.Morphism S.L.carrierVariety
      (RelativeRootSourceCoordinateSpace S) := by
  letI := S.coordinateAlgebraicGroup
  exact S.sourceLayerCoordinateQuotientMorphism.toVariety.comp
    (sourceConjugationLayerColumnMorphism S gamma t)

private theorem sourceCoordinateConjugationColumnMorphism_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) (t : k)
    (l : Variety.Point S.L.carrierVariety) :
    letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
    letI := S.coordinateAlgebraicGroup
    S.coordinatePointEquiv
        ((sourceCoordinateConjugationColumnMorphism S gamma t).toFun l) =
      (S.sourceLayerCarrierCoordinateConjugationAction).smul l
        (Multiplicative.ofAdd
          (Pi.single gamma t : RelativeRootSourceExactIndex S → k)) := by
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  letI := S.coordinateAlgebraicGroup
  have hinverse :
      (relativeRootLayerQuotient_coordinateEquiv S).symm
          (Multiplicative.ofAdd
            (Pi.single gamma t : RelativeRootSourceExactIndex S → k)) =
        QuotientGroup.mk' (sourceAbstractNextLayer S)
          (relativeRootLayerExactElement S gamma t) := by
    apply (relativeRootLayerQuotient_coordinateEquiv S).injective
    simpa using (relativeRootLayerQuotient_coordinateEquiv_root S gamma t).symm
  rw [S.sourceLayerCarrierCoordinateConjugationAction_apply]
  change S.coordinatePointEquiv
      ((sourceCoordinateConjugationColumnMorphism S gamma t).toFun l) =
    relativeRootLayerQuotient_coordinateEquiv S
      ((S.sourceLayerCarrierQuotientConjugationAction).smul l
        ((relativeRootLayerQuotient_coordinateEquiv S).symm
          (Multiplicative.ofAdd
            (Pi.single gamma t : RelativeRootSourceExactIndex S → k))))
  change S.coordinatePointEquiv
      (S.sourceLayerCoordinateQuotientMorphism.onPoints
        ((sourceConjugationLayerColumnMorphism S gamma t).toFun l)) = _
  rw [S.sourceLayerCoordinateQuotientMorphism_point]
  apply congrArg (relativeRootLayerQuotient_coordinateEquiv S)
  rw [hinverse]
  rw [S.sourceLayerCarrierQuotientConjugationAction_mk]
  congr 1
  apply Subtype.ext
  change (sourceSimpleLayerPointEquiv S S.height
      ((sourceConjugationLayerColumnMorphism S gamma t).toFun l)).1 =
    S.L.includePoint l *
      (relativeRootLayerExactElement S gamma t : Variety.Point K) *
        (S.L.includePoint l)⁻¹
  rw [relativeRootLayerExactElement_value]
  rfl

/-- The underlying additive coordinate vector obtained from transported
source-Levi quotient conjugation. -/
@[expose]
public noncomputable def sourceCoordinateActionValue
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (v : RelativeRootSourceExactIndex S → k) :
    RelativeRootSourceExactIndex S → k :=
  Multiplicative.toAdd
    ((S.sourceLayerCarrierCoordinateConjugationAction).smul l
      (Multiplicative.ofAdd v))

private theorem sourceCoordinateActionValue_single
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) (t : k)
    (l : Variety.Point S.L.carrierVariety) :
    letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
    sourceCoordinateActionValue S l (Pi.single gamma t) =
      ((sourceCoordinateConjugationColumnMorphism S gamma t).toFun l).val := by
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  letI := S.coordinateAlgebraicGroup
  have h := (sourceCoordinateConjugationColumnMorphism_apply S gamma t l).symm
  rw [S.coordinatePointEquiv_apply] at h
  simpa [sourceCoordinateActionValue] using congrArg Multiplicative.toAdd h

omit [IsAlgClosed k] in
/-- Every source-torus point lies in the aligned source Levi. -/
public theorem sourceTorus_mem_levi
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (s : Variety.Point S.T.carrierVariety) :
    S.T.includePoint s ∈ S.L :=
  S.torus_le_levi (S.T.pointEquiv s).2

/-- A source-torus point regarded as a point of the aligned source Levi. -/
@[expose]
public noncomputable def sourceTorusLeviPoint
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (s : Variety.Point S.T.carrierVariety) :
    Variety.Point S.L.carrierVariety :=
  S.L.pointEquiv.symm ⟨S.T.includePoint s, sourceTorus_mem_levi S s⟩

omit [IsAlgClosed k] in
/-- Including a source-torus point through the source Levi recovers its
ambient point. -/
public theorem sourceTorusLeviPoint_include
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (s : Variety.Point S.T.carrierVariety) :
    S.L.includePoint (sourceTorusLeviPoint S s) = S.T.includePoint s := by
  change (S.L.pointEquiv
    (S.L.pointEquiv.symm ⟨S.T.includePoint s, sourceTorus_mem_levi S s⟩)).1 = _
  rw [S.L.pointEquiv.apply_symm_apply]

/-- Source-torus conjugation scales an exact root coordinate by the inverse
of its root character. -/
public theorem sourceCoordinateConjugation_torus_single
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (s : Variety.Point S.T.carrierVariety)
    (gamma : RelativeRootSourceExactIndex S) (t : k) :
    letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
    sourceCoordinateActionValue S (sourceTorusLeviPoint S s) (Pi.single gamma t) =
      Pi.single gamma
        (((S.D.rootWeight gamma.1).pointCharacter s)⁻¹ * t) := by
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  letI := S.coordinateAlgebraicGroup
  have hinverse :
      (relativeRootLayerQuotient_coordinateEquiv S).symm
          (Multiplicative.ofAdd
            (Pi.single gamma t : RelativeRootSourceExactIndex S → k)) =
        QuotientGroup.mk' (sourceAbstractNextLayer S)
          (relativeRootLayerExactElement S gamma t) := by
    apply (relativeRootLayerQuotient_coordinateEquiv S).injective
    simpa using (relativeRootLayerQuotient_coordinateEquiv_root S gamma t).symm
  have hconj :
      S.T.includePoint s * S.C.x gamma.1 t * (S.T.includePoint s)⁻¹ =
        S.C.x gamma.1
          (((S.D.rootWeight gamma.1).pointCharacter s)⁻¹ * t) := by
    have hweight := S.isRealization.2.2.1 gamma.1
    have h := hweight.2 (S.chevalleyParametrization gamma.1) t s⁻¹
    rw [S.chevalleyParametrization_value,
      S.chevalleyParametrization_value] at h
    change (S.T.inclusion.onPoints s⁻¹)⁻¹ * S.C.x gamma.1 t *
        S.T.inclusion.onPoints s⁻¹ = _ at h
    rw [map_inv] at h
    rw [map_inv] at h
    have hinclude : S.T.includePoint s = S.T.inclusion.onPoints s := rfl
    rw [hinclude]
    simpa only [inv_inv] using h
  apply Multiplicative.ofAdd.injective
  rw [sourceCoordinateActionValue]
  rw [S.sourceLayerCarrierCoordinateConjugationAction_apply]
  rw [hinverse]
  rw [S.sourceLayerCarrierQuotientConjugationAction_mk]
  have hmk :
      (QuotientGroup.mk' (sourceAbstractNextLayer S))
          (⟨S.L.includePoint (sourceTorusLeviPoint S s) *
              (relativeRootLayerExactElement S gamma t : Variety.Point K) *
              (S.L.includePoint (sourceTorusLeviPoint S s))⁻¹, by
            have hnorm := S.levi_le_sourceRelativeRootLayer_normalizer S.height
              (S.L.pointEquiv (sourceTorusLeviPoint S s)).2
            rw [Subgroup.mem_normalizer_iff] at hnorm
            exact (hnorm _).mp (relativeRootLayerExactElement S gamma t).2⟩ :
            sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
              S.coeff S.J S.height) =
        QuotientGroup.mk' (sourceAbstractNextLayer S)
          (relativeRootLayerExactElement S gamma
            (((S.D.rootWeight gamma.1).pointCharacter s)⁻¹ * t)) := by
    congr 1
    apply Subtype.ext
    change S.L.includePoint (sourceTorusLeviPoint S s) *
        (relativeRootLayerExactElement S gamma t : Variety.Point K) *
          (S.L.includePoint (sourceTorusLeviPoint S s))⁻¹ =
      (relativeRootLayerExactElement S gamma
        (((S.D.rootWeight gamma.1).pointCharacter s)⁻¹ * t) : Variety.Point K)
    rw [relativeRootLayerExactElement_value,
      relativeRootLayerExactElement_value]
    rw [sourceTorusLeviPoint_include]
    exact hconj
  rw [hmk]
  simpa using relativeRootLayerQuotient_coordinateEquiv_root S gamma
    (((S.D.rootWeight gamma.1).pointCharacter s)⁻¹ * t)

private lemma sourceLeviRoot_exactRoot_linearIndependent
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (delta : S.D.Root) (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (gamma : RelativeRootSourceExactIndex S) :
    AreLinearlyIndependentRoots S.D S.pairing
      (Equiv.refl S.D.Root) delta gamma.1 := by
  letI := Fintype.ofFinite S.D.Root
  letI := S.pairing.indexNeg
  have hdeltaHeight :=
    S.relativeRootHeight_eq_zero_of_mem_rootSubsystemSpan hdelta
  have hne : delta ≠ gamma.1 := by
    intro h
    subst delta
    rw [gamma.2] at hdeltaHeight
    have hheightpos : (0 : ℤ) < S.height := by
      exact_mod_cast S.height_pos
    omega
  have hnotopp : S.pairing.root delta ≠ -S.pairing.root gamma.1 := by
    intro hneg
    have hidx : delta = S.pairing.reflectionPerm gamma.1 gamma.1 :=
      S.pairing.root.injective <| by
        rw [S.pairing.root_reflectionPerm, S.pairing.reflection_apply_self]
        exact hneg
    have hnegHeight := relativeRootHeight_reflectionPerm_self S.pairing S.base S.J
      S.coeff S.simpleRootExpansion gamma.1
    rw [S.base_support_eq_simple_toFinset] at hnegHeight
    rw [← hidx, hdeltaHeight, gamma.2] at hnegHeight
    have hheightpos : (0 : ℤ) < S.height := by
      exact_mod_cast S.height_pos
    omega
  have hlin : LinearIndependent ℚ
      ![S.pairing.root delta, S.pairing.root gamma.1] :=
    RootPairing.IsReduced.linearIndependent (P := S.pairing) hne hnotopp
  rw [LinearIndependent.pair_iff] at hlin
  simpa [AreLinearlyIndependentRoots] using hlin

private lemma sourceValidCommutatorTerm_exactHeight
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (gamma : RelativeRootSourceExactIndex S)
    (q : ChevalleyCommutatorTerm S.D.Root)
    (hvalid : IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) delta gamma.1 q)
    (hqj : q.j = 1) :
    RelativeRootHeight S.coeff S.D.simple.toFinite.toFinset S.J q.root =
      S.height := by
  letI := Fintype.ofFinite S.D.Root
  have hdeltaHeight :=
    S.relativeRootHeight_eq_zero_of_mem_rootSubsystemSpan hdelta
  have hheight := relativeRootHeight_of_validChevalleyCommutatorTerm
    S.D S.pairing (Equiv.refl S.D.Root) S.base S.J S.coeff
      S.simpleRootExpansion q hvalid
  rw [S.base_support_eq_simple_toFinset] at hheight
  simp only [Equiv.refl_apply] at hheight
  rw [hheight, hdeltaHeight, gamma.2, hqj]
  simp

private lemma sourceValidCommutatorTerm_mem_layer
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (gamma : RelativeRootSourceExactIndex S)
    (q : ChevalleyCommutatorTerm S.D.Root)
    (hvalid : IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) delta gamma.1 q) (a : k) :
    S.C.x q.root a ∈ sourceRelativeRootLayer S.D
      S.D.simple.toFinite.toFinset S.coeff S.J S.height := by
  letI := Fintype.ofFinite S.D.Root
  have hdeltaHeight :=
    S.relativeRootHeight_eq_zero_of_mem_rootSubsystemSpan hdelta
  have hheight := relativeRootHeight_of_validChevalleyCommutatorTerm
    S.D S.pairing (Equiv.refl S.D.Root) S.base S.J S.coeff
      S.simpleRootExpansion q hvalid
  rw [S.base_support_eq_simple_toFinset] at hheight
  simp only [Equiv.refl_apply] at hheight
  have hbound : (S.height : ℤ) ≤ RelativeRootHeight S.coeff
      S.D.simple.toFinite.toFinset S.J q.root := by
    rw [hheight, hdeltaHeight, gamma.2]
    have hqj : (1 : ℤ) ≤ q.j := by
      exact_mod_cast Nat.succ_le_of_lt hvalid.2.1
    have hheightpos : (0 : ℤ) < S.height := by
      exact_mod_cast S.height_pos
    nlinarith
  rw [sourceRelativeRootLayer, RelativeRootSeries, RootSubgroupGenerated]
  apply Subgroup.subset_closure
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨q.root, by simpa using hbound, ?_⟩
  rw [← (S.chevalleySystem.1 q.root).2]
  exact ⟨a, rfl⟩

private lemma sourceValidCommutatorTerm_mem_nextLayer
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (gamma : RelativeRootSourceExactIndex S)
    (q : ChevalleyCommutatorTerm S.D.Root)
    (hvalid : IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) delta gamma.1 q)
    (hqj : q.j ≠ 1) (a : k) :
    S.C.x q.root a ∈ sourceRelativeRootLayer S.D
      S.D.simple.toFinite.toFinset S.coeff S.J (S.height + 1) := by
  letI := Fintype.ofFinite S.D.Root
  have hdeltaHeight :=
    S.relativeRootHeight_eq_zero_of_mem_rootSubsystemSpan hdelta
  have hheight := relativeRootHeight_of_validChevalleyCommutatorTerm
    S.D S.pairing (Equiv.refl S.D.Root) S.base S.J S.coeff
      S.simpleRootExpansion q hvalid
  rw [S.base_support_eq_simple_toFinset] at hheight
  simp only [Equiv.refl_apply] at hheight
  have hqj' : (2 : ℤ) ≤ q.j := by
    have : 0 < q.j := hvalid.2.1
    omega
  have hbound : (S.height + 1 : ℕ) ≤ RelativeRootHeight S.coeff
      S.D.simple.toFinite.toFinset S.J q.root := by
    rw [hheight, hdeltaHeight, gamma.2]
    have hheightpos : (0 : ℤ) < S.height := by
      exact_mod_cast S.height_pos
    norm_num
    nlinarith
  rw [sourceRelativeRootLayer, RelativeRootSeries, RootSubgroupGenerated]
  apply Subgroup.subset_closure
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨q.root, by simpa using hbound, ?_⟩
  rw [← (S.chevalleySystem.1 q.root).2]
  exact ⟨a, rfl⟩

omit [IsAlgClosed k] in
/-- A source root-subgroup element with root in the Levi subsystem lies in
the aligned source Levi. -/
public lemma sourceLeviRoot_mem_levi
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    {delta : S.D.Root} (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (s : k) : S.C.x delta s ∈ S.L := by
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

/-- A source root-subgroup element whose root lies in the Levi subsystem,
regarded as a point of the aligned source Levi. -/
@[expose]
public noncomputable def sourceLeviRootPoint
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (delta : S.D.Root) (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (s : k) : Variety.Point S.L.carrierVariety :=
  S.L.pointEquiv.symm ⟨S.C.x delta s, sourceLeviRoot_mem_levi S hdelta s⟩

omit [IsAlgClosed k] in
/-- Including a source Levi root point recovers the corresponding Chevalley
root element. -/
public lemma sourceLeviRootPoint_include
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (delta : S.D.Root) (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (s : k) :
    S.L.includePoint (sourceLeviRootPoint S delta hdelta s) = S.C.x delta s := by
  change (S.L.pointEquiv
    (S.L.pointEquiv.symm
      ⟨S.C.x delta s, sourceLeviRoot_mem_levi S hdelta s⟩)).1 = _
  rw [S.L.pointEquiv.apply_symm_apply]

/-- The exact Chevalley coordinate formula for conjugating one source-layer
coordinate by a root-subgroup generator in the Levi subsystem.  Modulo the
next layer, exactly the commutator terms with second exponent one survive. -/
public theorem sourceCoordinateConjugation_root_single
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (delta : S.D.Root) (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (gamma : RelativeRootSourceExactIndex S) :
    letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
    letI : DecidableEq S.D.Root := Classical.decEq _
    ∃ (order : List (ChevalleyCommutatorTerm S.D.Root))
      (coefficient : ChevalleyCommutatorTerm S.D.Root → k),
      order.Nodup ∧
      (∀ q, q ∈ order ↔ IsValidChevalleyCommutatorTerm S.D S.pairing
        (Equiv.refl S.D.Root) delta gamma.1 q) ∧
      (∀ q ∈ order, HasExpectedChevalleyCoefficient S.D S.pairing
        (Equiv.refl S.D.Root) delta gamma.1 q (coefficient q)) ∧
      ∀ s t,
        sourceCoordinateActionValue S (sourceLeviRootPoint S delta hdelta s)
            (Pi.single gamma t) =
          (order.attach.map fun q =>
            fun eta => if q.1.j = 1 ∧ q.1.root = eta.1 then
              coefficient q.1 * (-s) ^ q.1.i * (-t)
            else 0).sum + Pi.single gamma t := by
  letI := S.coordinateAlgebraicGroup
  letI := Fintype.ofFinite S.D.Root
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  letI : DecidableEq S.D.Root := Classical.decEq _
  letI : (sourceAbstractNextLayer S).Normal :=
    sourceRelativeRootLayer_next_normal S
  have hLI := sourceLeviRoot_exactRoot_linearIndependent S delta hdelta gamma
  rcases S.chevalleySystem.2.2.2.2.1 delta gamma.1 hLI with
    ⟨order, coefficient, hnodup, _hordered, hvalid, hcoefficient, hformula⟩
  refine ⟨order, coefficient, hnodup, hvalid, hcoefficient, ?_⟩
  intro s t
  let Term := {q : ChevalleyCommutatorTerm S.D.Root // q ∈ order}
  let validTerm : ∀ q : Term, IsValidChevalleyCommutatorTerm S.D S.pairing
      (Equiv.refl S.D.Root) delta gamma.1 q.1 := fun q =>
    (hvalid q.1).1 q.2
  let parameter (q : Term) : k :=
    coefficient q.1 * (-s) ^ q.1.i * (-t) ^ q.1.j
  let layerTerm (q : Term) :
      sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
        S.coeff S.J S.height :=
    ⟨S.C.x q.1.root (parameter q),
      sourceValidCommutatorTerm_mem_layer S hdelta gamma q.1
        (validTerm q) (parameter q)⟩
  let exactTerm (q : Term) (hqj : q.1.j = 1) :
      RelativeRootSourceExactIndex S :=
    ⟨q.1.root,
      sourceValidCommutatorTerm_exactHeight S hdelta gamma q.1
        (validTerm q) hqj⟩
  let quotientVector (q : Term) : RelativeRootSourceExactIndex S → k :=
    if hqj : q.1.j = 1 then Pi.single (exactTerm q hqj) (parameter q) else 0
  have hterm (q : Term) :
      relativeRootLayerQuotient_coordinateEquiv S
          (show relativeRootLayerQuotient S from
            QuotientGroup.mk' (sourceAbstractNextLayer S) (layerTerm q)) =
        Multiplicative.ofAdd (quotientVector q) := by
    by_cases hqj : q.1.j = 1
    · simp only [quotientVector, dif_pos hqj]
      have hroot := relativeRootLayerQuotient_coordinateEquiv_root S
        (exactTerm q hqj) (parameter q)
      rw [show layerTerm q =
          relativeRootLayerExactElement S (exactTerm q hqj) (parameter q) by
        apply Subtype.ext
        change S.C.x q.1.root (parameter q) =
          (relativeRootLayerExactElement S (exactTerm q hqj)
            (parameter q) : Variety.Point K)
        exact (relativeRootLayerExactElement_value S
          (exactTerm q hqj) (parameter q)).symm]
      simpa only [sourceAbstractNextLayer] using hroot
    · simp only [quotientVector, dif_neg hqj]
      have hqone :
          (show relativeRootLayerQuotient S from
            QuotientGroup.mk' (sourceAbstractNextLayer S) (layerTerm q)) = 1 :=
        (QuotientGroup.eq_one_iff (layerTerm q)).2
          (sourceValidCommutatorTerm_mem_nextLayer S hdelta gamma q.1
            (validTerm q) hqj (parameter q))
      calc
        relativeRootLayerQuotient_coordinateEquiv S
            (show relativeRootLayerQuotient S from
              QuotientGroup.mk' (sourceAbstractNextLayer S) (layerTerm q)) =
            relativeRootLayerQuotient_coordinateEquiv S 1 :=
          congrArg (relativeRootLayerQuotient_coordinateEquiv S) hqone
        _ = Multiplicative.ofAdd (0 : RelativeRootSourceExactIndex S → k) := by
          simp
  have hxzero (alpha : S.D.Root) : S.C.x alpha 0 = 1 := by
    simpa using S.chevalleySystem.2.2.2.1 alpha 0 0
  have hxneg (alpha : S.D.Root) (a : k) :
      S.C.x alpha (-a) = (S.C.x alpha a)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [S.chevalleySystem.2.2.2.1 alpha (-a) a]
    simpa using hxzero alpha
  have hconjugate :
      S.C.x delta s * S.C.x gamma.1 t * (S.C.x delta s)⁻¹ =
        (order.map fun q =>
          S.C.x q.root
            (coefficient q * (-s) ^ q.i * (-t) ^ q.j)).prod *
          S.C.x gamma.1 t := by
    have hcomm := hformula (-s) (-t)
    rw [hxneg delta s, hxneg gamma.1 t] at hcomm
    simp only [inv_inv] at hcomm
    calc
      S.C.x delta s * S.C.x gamma.1 t * (S.C.x delta s)⁻¹ =
          (S.C.x delta s * S.C.x gamma.1 t * (S.C.x delta s)⁻¹ *
            (S.C.x gamma.1 t)⁻¹) * S.C.x gamma.1 t := by
              simp [mul_assoc]
      _ = (order.map fun q =>
          S.C.x q.root
            (coefficient q * (-s) ^ q.i * (-t) ^ q.j)).prod *
            S.C.x gamma.1 t :=
        congrArg (fun x => x * S.C.x gamma.1 t) hcomm
  let qmk (x : sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
      S.coeff S.J S.height) : relativeRootLayerQuotient S :=
    show relativeRootLayerQuotient S from
      QuotientGroup.mk' (sourceAbstractNextLayer S) x
  have hquotient :
      (S.sourceLayerCarrierQuotientConjugationAction).smul
          (sourceLeviRootPoint S delta hdelta s)
          (qmk (relativeRootLayerExactElement S gamma t)) =
        (order.attach.map fun q => qmk (layerTerm q)).prod *
          qmk (relativeRootLayerExactElement S gamma t) := by
    dsimp only [qmk]
    rw [S.sourceLayerCarrierQuotientConjugationAction_mk]
    have hmapTerms :
        QuotientGroup.mk' (sourceAbstractNextLayer S)
            (order.attach.map layerTerm).prod =
          (order.attach.map fun q =>
            QuotientGroup.mk' (sourceAbstractNextLayer S) (layerTerm q)).prod := by
      calc
        QuotientGroup.mk' (sourceAbstractNextLayer S)
              (order.attach.map layerTerm).prod =
            ((order.attach.map layerTerm).map
              (QuotientGroup.mk' (sourceAbstractNextLayer S))).prod :=
          map_list_prod (QuotientGroup.mk' (sourceAbstractNextLayer S))
            (order.attach.map layerTerm)
        _ = _ := by
          rw [List.map_map]
          apply congrArg List.prod
          apply List.map_congr_left
          intro q _hq
          rfl
    rw [← hmapTerms, ← map_mul]
    congr 1
    apply Subtype.ext
    calc
      (S.L.includePoint (sourceLeviRootPoint S delta hdelta s) *
          (relativeRootLayerExactElement S gamma t : Variety.Point K) *
            (S.L.includePoint (sourceLeviRootPoint S delta hdelta s))⁻¹) =
          S.C.x delta s * S.C.x gamma.1 t * (S.C.x delta s)⁻¹ := by
        rw [sourceLeviRootPoint_include, relativeRootLayerExactElement_value]
      _ = (order.map fun q =>
          S.C.x q.root
            (coefficient q * (-s) ^ q.i * (-t) ^ q.j)).prod *
          S.C.x gamma.1 t := hconjugate
      _ = ((order.attach.map layerTerm).prod *
          relativeRootLayerExactElement S gamma t :
            sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
              S.coeff S.J S.height) := by
        change (order.map fun q =>
            S.C.x q.root
              (coefficient q * (-s) ^ q.i * (-t) ^ q.j)).prod *
              S.C.x gamma.1 t =
          ((order.attach.map layerTerm).prod :
            sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
              S.coeff S.J S.height) *
            (relativeRootLayerExactElement S gamma t : Variety.Point K)
        rw [relativeRootLayerExactElement_value]
        congr 1
        symm
        rw [SubmonoidClass.coe_list_prod]
        rw [List.map_map]
        apply congrArg List.prod
        calc
          order.attach.map (Subtype.val ∘ layerTerm) =
              order.attach.map (fun q =>
                S.C.x q.1.root
                  (coefficient q.1 * (-s) ^ q.1.i * (-t) ^ q.1.j)) := by
            apply List.map_congr_left
            intro q _hq
            rfl
          _ = _ := @List.attach_map_val _ _ order (fun q =>
              S.C.x q.root
                (coefficient q * (-s) ^ q.i * (-t) ^ q.j))
  have hinverse :
      (relativeRootLayerQuotient_coordinateEquiv S).symm
          (Multiplicative.ofAdd
            (Pi.single gamma t : RelativeRootSourceExactIndex S → k)) =
        qmk (relativeRootLayerExactElement S gamma t) := by
    apply (relativeRootLayerQuotient_coordinateEquiv S).injective
    rw [(relativeRootLayerQuotient_coordinateEquiv S).apply_symm_apply]
    simpa only [qmk, sourceAbstractNextLayer] using
      (relativeRootLayerQuotient_coordinateEquiv_root S gamma t).symm
  have hcoordinate :
      Multiplicative.ofAdd
          (sourceCoordinateActionValue S
            (sourceLeviRootPoint S delta hdelta s) (Pi.single gamma t)) =
        (order.attach.map fun q => Multiplicative.ofAdd (quotientVector q)).prod *
          Multiplicative.ofAdd (Pi.single gamma t) := by
    rw [sourceCoordinateActionValue]
    rw [ofAdd_toAdd]
    rw [S.sourceLayerCarrierCoordinateConjugationAction_apply]
    rw [hinverse, hquotient, map_mul, map_list_prod, List.map_map]
    congr 1
    · apply congrArg List.prod
      apply List.map_congr_left
      intro q _hq
      exact hterm q
    · simpa only [qmk, sourceAbstractNextLayer] using
        relativeRootLayerQuotient_coordinateEquiv_root S gamma t
  have hadd := congrArg Multiplicative.toAdd hcoordinate
  simp only [toAdd_ofAdd, toAdd_mul] at hadd
  rw [hadd]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _hq
  by_cases hqj : q.1.j = 1
  · simp only [quotientVector, dif_pos hqj]
    funext eta
    by_cases hroot : q.1.root = eta.1
    · have heq : exactTerm q hqj = eta := by
        apply Subtype.ext
        exact hroot
      subst eta
      change (Pi.single (exactTerm q hqj)
          (coefficient q.1 * (-s) ^ q.1.i * (-t) ^ q.1.j) :
            RelativeRootSourceExactIndex S → k) (exactTerm q hqj) = _
      rw [Pi.single_eq_same]
      rw [if_pos ⟨hqj, rfl⟩]
      simp only [hqj, pow_one]
    · have hne : exactTerm q hqj ≠ eta := by
        intro heq
        exact hroot (congrArg Subtype.val heq)
      change (Pi.single (exactTerm q hqj)
          (coefficient q.1 * (-s) ^ q.1.i * (-t) ^ q.1.j) :
            RelativeRootSourceExactIndex S → k) eta = _
      rw [Pi.single_eq_of_ne hne.symm]
      rw [if_neg (fun h => hroot h.2)]
  · simp only [quotientVector, dif_neg hqj]
    funext eta
    change (0 : RelativeRootSourceExactIndex S → k) eta = _
    rw [Pi.zero_apply]
    rw [if_neg (fun h => hqj h.1)]

private noncomputable def sourceCoordinateAddEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety) :
    (RelativeRootSourceExactIndex S → k) ≃+
      (RelativeRootSourceExactIndex S → k) :=
  MulEquiv.toAdditive
    (S.sourceLayerCarrierCoordinateConjugationHom l)

private theorem sourceCoordinateAddEquiv_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (v : RelativeRootSourceExactIndex S → k) :
    sourceCoordinateAddEquiv S l v = sourceCoordinateActionValue S l v :=
  rfl

private theorem sourceCoordinateActionValue_add
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (v w : RelativeRootSourceExactIndex S → k) :
    sourceCoordinateActionValue S l (v + w) =
      sourceCoordinateActionValue S l v + sourceCoordinateActionValue S l w := by
  simp [← sourceCoordinateAddEquiv_apply]

private def SourceCoordinateLinearAt
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety) : Prop :=
  ∀ (a : k) (v : RelativeRootSourceExactIndex S → k),
    sourceCoordinateActionValue S l (a • v) =
      a • sourceCoordinateActionValue S l v

private theorem sourceCoordinateLinearAt_of_single
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety) :
    letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
    (∀ (a : k) (gamma : RelativeRootSourceExactIndex S) (t : k),
      sourceCoordinateActionValue S l (a • Pi.single gamma t) =
        a • sourceCoordinateActionValue S l (Pi.single gamma t)) →
    SourceCoordinateLinearAt S l := by
  letI := Fintype.ofFinite (RelativeRootSourceExactIndex S)
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  intro hsingle a v
  have hv : v = ∑ gamma, Pi.single gamma (v gamma) := by
    funext eta
    simp
  rw [hv]
  change (sourceCoordinateAddEquiv S l) (a • ∑ gamma, Pi.single gamma (v gamma)) =
    a • (sourceCoordinateAddEquiv S l) (∑ gamma, Pi.single gamma (v gamma))
  rw [Finset.smul_sum, map_sum, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro gamma _
  exact hsingle a gamma (v gamma)

private theorem sourceCoordinateConjugation_torus_linearAt
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (s : Variety.Point S.T.carrierVariety) :
    SourceCoordinateLinearAt S (sourceTorusLeviPoint S s) := by
  apply sourceCoordinateLinearAt_of_single
  intro a gamma t
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  letI : DecidableEq S.D.Root := Classical.decEq _
  have hsingle : a • (Pi.single gamma t : RelativeRootSourceExactIndex S → k) =
      Pi.single gamma (a * t) := by
    funext eta
    simp [Pi.single_apply, smul_eq_mul]
  rw [hsingle, sourceCoordinateConjugation_torus_single,
    sourceCoordinateConjugation_torus_single]
  funext eta
  simp [Pi.single_apply, smul_eq_mul]
  split <;> rename_i h
  · subst eta
    ring
  · rfl

private theorem sourceCoordinateConjugation_root_linearAt
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (delta : S.D.Root) (hdelta : delta ∈ RootSubsystemSpan S.D S.J)
    (s : k) :
    SourceCoordinateLinearAt S (sourceLeviRootPoint S delta hdelta s) := by
  apply sourceCoordinateLinearAt_of_single
  intro a gamma t
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  letI : DecidableEq S.D.Root := Classical.decEq _
  rcases sourceCoordinateConjugation_root_single S delta hdelta gamma with
    ⟨order, coefficient, _hnodup, _hvalid, _hcoefficient, hformula⟩
  have hsingle : a • (Pi.single gamma t : RelativeRootSourceExactIndex S → k) =
      Pi.single gamma (a * t) := by
    funext eta
    simp [Pi.single_apply, smul_eq_mul]
  rw [hsingle, hformula s (a * t), hformula s t]
  funext eta
  simp only [Pi.add_apply, Pi.smul_apply]
  have hsumApply (xs : List (RelativeRootSourceExactIndex S → k)) :
      xs.sum eta = (xs.map fun f => f eta).sum := by
    induction xs with
    | nil => rfl
    | cons f fs ih =>
        simp only [List.sum_cons, List.map_cons]
        rw [Pi.add_apply, ih]
  rw [hsumApply, hsumApply]
  simp only [List.map_map]
  change
    (order.attach.map fun q =>
        if q.1.j = 1 ∧ q.1.root = eta.1 then
          coefficient q.1 * (-s) ^ q.1.i * (-(a * t)) else 0).sum +
        (Pi.single gamma (a * t) : RelativeRootSourceExactIndex S → k) eta =
      a * ((order.attach.map fun q =>
        if q.1.j = 1 ∧ q.1.root = eta.1 then
          coefficient q.1 * (-s) ^ q.1.i * (-t) else 0).sum +
        (Pi.single gamma t : RelativeRootSourceExactIndex S → k) eta)
  rw [mul_add]
  congr 1
  · induction order.attach with
    | nil => simp
    | cons q qs ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        by_cases hterm : q.1.j = 1 ∧ q.1.root = eta.1
        · rw [if_pos hterm, if_pos hterm]
          ring
        · rw [if_neg hterm, if_neg hterm]
          ring
  · simp [Pi.single_apply]

private theorem sourceCoordinateActionValue_mul
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (a b : Variety.Point S.L.carrierVariety)
    (v : RelativeRootSourceExactIndex S → k) :
    sourceCoordinateActionValue S (a * b) v =
      sourceCoordinateActionValue S a (sourceCoordinateActionValue S b v) := by
  change Multiplicative.toAdd
      ((S.sourceLayerCarrierCoordinateConjugationHom (a * b))
        (Multiplicative.ofAdd v)) = _
  rw [map_mul]
  rfl

private noncomputable def sourceCoordinateLinearSubgroup
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Subgroup (Variety.Point S.L.carrierVariety) where
  carrier := {l | SourceCoordinateLinearAt S l}
  one_mem' := by
    intro a v
    change Multiplicative.toAdd
      ((S.sourceLayerCarrierCoordinateConjugationHom 1)
        (Multiplicative.ofAdd (a • v))) =
      a • Multiplicative.toAdd
        ((S.sourceLayerCarrierCoordinateConjugationHom 1)
          (Multiplicative.ofAdd v))
    rw [map_one]
    rfl
  mul_mem' := by
    intro x y hx hy a v
    rw [sourceCoordinateActionValue_mul]
    rw [hy]
    rw [hx]
    rw [sourceCoordinateActionValue_mul]
  inv_mem' := by
    intro x hx a v
    apply (sourceCoordinateAddEquiv S x).injective
    simp only [sourceCoordinateAddEquiv_apply]
    rw [← sourceCoordinateActionValue_mul]
    rw [mul_inv_cancel]
    rw [hx]
    rw [← sourceCoordinateActionValue_mul]
    rw [mul_inv_cancel]
    change sourceCoordinateActionValue S 1 (a • v) =
      a • sourceCoordinateActionValue S 1 v
    change Multiplicative.toAdd
        ((S.sourceLayerCarrierCoordinateConjugationHom 1)
          (Multiplicative.ofAdd (a • v))) =
      a • Multiplicative.toAdd
        ((S.sourceLayerCarrierCoordinateConjugationHom 1)
          (Multiplicative.ofAdd v))
    rw [map_one]
    rfl

private noncomputable def sourceCoordinateLinearAmbientSubgroup
    {K : Variety k} [AlgebraicGroup K]
  (S : RelativeRootRepresentationSource K) :
    Subgroup (Variety.Point K) :=
  (sourceCoordinateLinearSubgroup S).map S.L.inclusion.onPoints

private theorem sourceTorus_le_sourceCoordinateLinearAmbientSubgroup
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    S.T.toSubgroup ≤ sourceCoordinateLinearAmbientSubgroup S := by
  intro x hx
  let s : Variety.Point S.T.carrierVariety := S.T.pointEquiv.symm ⟨x, hx⟩
  let l := sourceTorusLeviPoint S s
  change x ∈ (sourceCoordinateLinearSubgroup S).map S.L.inclusion.onPoints
  refine ⟨l, sourceCoordinateConjugation_torus_linearAt S s, ?_⟩
  change S.L.includePoint l = x
  rw [sourceTorusLeviPoint_include]
  change (S.T.pointEquiv s).1 = x
  simp [s]

private lemma sourceRootSubsystemSpan_neg_mem
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
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

private theorem sourceLeviRootFactor_le_sourceCoordinateLinearAmbientSubgroup
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    standardLeviRootFactor S.D (RootSubsystemSpan S.D S.J) ≤
      sourceCoordinateLinearAmbientSubgroup S := by
  rw [standardLeviRootFactor, RootSubgroupGenerated_le_iff]
  intro delta hdelta x hx
  have hdeltaSpan : delta ∈ RootSubsystemSpan S.D S.J := by
    rcases hdelta with hdelta | ⟨beta, hbeta, rfl⟩
    · exact hdelta
    · exact sourceRootSubsystemSpan_neg_mem S hbeta
  have hxrange : x ∈ Set.range (S.C.x delta) := by
    rw [(S.chevalleySystem.1 delta).2]
    exact hx
  rcases hxrange with ⟨s, rfl⟩
  let l := sourceLeviRootPoint S delta hdeltaSpan s
  change S.C.x delta s ∈
    (sourceCoordinateLinearSubgroup S).map S.L.inclusion.onPoints
  refine ⟨l, sourceCoordinateConjugation_root_linearAt S delta hdeltaSpan s, ?_⟩
  exact sourceLeviRootPoint_include S delta hdeltaSpan s

private theorem sourceLeviGenerators_le_sourceCoordinateLinearAmbientSubgroup
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Subgroup.closure ((S.T : Set (Variety.Point K)) ∪
        standardLeviRootFactor S.D (RootSubsystemSpan S.D S.J)) ≤
      sourceCoordinateLinearAmbientSubgroup S := by
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · exact sourceTorus_le_sourceCoordinateLinearAmbientSubgroup S hx
  · exact sourceLeviRootFactor_le_sourceCoordinateLinearAmbientSubgroup S hx

private noncomputable def sourceCoordinateColumnPolynomialFunction
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) (t : k)
    (eta : RelativeRootSourceExactIndex S) :
    S.L.carrierVariety.PolynomialFunction :=
  Variety.PolynomialFunction.pullback
    (sourceCoordinateConjugationColumnMorphism S gamma t)
    (Variety.PolynomialFunction.ofPolynomial
      (RelativeRootSourceCoordinateSpace S) (MvPolynomial.X eta))

private theorem sourceCoordinateColumnPolynomialFunction_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) (t : k)
    (eta : RelativeRootSourceExactIndex S)
    (l : Variety.Point S.L.carrierVariety) :
    sourceCoordinateColumnPolynomialFunction S gamma t eta l =
      ((sourceCoordinateConjugationColumnMorphism S gamma t).toFun l).val eta := by
  change evalPolynomial
      ((sourceCoordinateConjugationColumnMorphism S gamma t).toFun l).val
        (MvPolynomial.X eta) = _
  simp [evalPolynomial]

private noncomputable def sourceCoordinateColumnAmbientExtension
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) (t : k)
    (eta : RelativeRootSourceExactIndex S) : K.PolynomialFunction :=
  Classical.choose
    (S.L.exists_polynomialFunction_extension
      (sourceCoordinateColumnPolynomialFunction S gamma t eta))

private theorem sourceCoordinateColumnAmbientExtension_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (gamma : RelativeRootSourceExactIndex S) (t : k)
    (eta : RelativeRootSourceExactIndex S)
    (l : Variety.Point S.L.carrierVariety) :
    sourceCoordinateColumnAmbientExtension S gamma t eta
        (S.L.inclusion.onPoints l) =
      ((sourceCoordinateConjugationColumnMorphism S gamma t).toFun l).val eta := by
  rw [sourceCoordinateColumnAmbientExtension]
  rw [Classical.choose_spec
    (S.L.exists_polynomialFunction_extension
      (sourceCoordinateColumnPolynomialFunction S gamma t eta))]
  exact sourceCoordinateColumnPolynomialFunction_apply S gamma t eta l

private def polynomialFunctionToAffineLineMorphism
    {V : Variety k} (f : V.PolynomialFunction) :
    Variety.Morphism V (affineSpaceVariety k PUnit) where
  toFun := fun x => affineSpacePoint (fun _ => f x)
  regular := by
    intro i
    cases i
    exact f.representedBy

private theorem sourceCoordinateConjugation_single_homogeneous
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (a : k) (gamma : RelativeRootSourceExactIndex S) (t : k) :
    letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
    sourceCoordinateActionValue S l (Pi.single gamma (a * t)) =
      a • sourceCoordinateActionValue S l (Pi.single gamma t) := by
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  apply funext
  intro eta
  let f := sourceCoordinateColumnAmbientExtension S gamma (a * t) eta
  let g := a • sourceCoordinateColumnAmbientExtension S gamma t eta
  let F := polynomialFunctionToAffineLineMorphism f
  let G := polynomialFunctionToAffineLineMorphism g
  let Z : Set (Variety.Point K) := {x | F.toFun x = G.toFun x}
  have hZclosed : IsZariskiClosed K Z := by
    exact Variety.Morphism.isZariskiClosed_equalizer F G
  have hlinearZ : sourceCoordinateLinearAmbientSubgroup S ≤ Z := by
    intro x hx
    rcases hx with ⟨l', hl', hxl'⟩
    change F.toFun x = G.toFun x
    apply Variety.Point.ext
    funext i
    cases i
    change f x = g x
    subst x
    rw [show f (S.L.inclusion.onPoints l') =
        ((sourceCoordinateConjugationColumnMorphism S gamma (a * t)).toFun l').val eta by
      exact sourceCoordinateColumnAmbientExtension_apply S gamma (a * t) eta l']
    rw [show g (S.L.inclusion.onPoints l') =
        a * ((sourceCoordinateConjugationColumnMorphism S gamma t).toFun l').val eta by
      dsimp only [g]
      rw [polynomialFunction_smul_apply]
      rw [sourceCoordinateColumnAmbientExtension_apply]]
    rw [← sourceCoordinateActionValue_single S gamma (a * t) l']
    rw [← sourceCoordinateActionValue_single S gamma t l']
    have hl := hl' a (Pi.single gamma t)
    have hsingle :
        a • (Pi.single gamma t : RelativeRootSourceExactIndex S → k) =
          Pi.single gamma (a * t) := by
      funext zeta
      simp [Pi.single_apply, smul_eq_mul]
    rw [hsingle] at hl
    exact congrFun hl eta
  have hgenZ :
      (Subgroup.closure ((S.T : Set (Variety.Point K)) ∪
          standardLeviRootFactor S.D (RootSubsystemSpan S.D S.J)) :
          Set (Variety.Point K)) ⊆ Z :=
    fun x hx => hlinearZ (sourceLeviGenerators_le_sourceCoordinateLinearAmbientSubgroup S hx)
  have hlclosure : S.L.includePoint l ∈ closure
      (Subgroup.closure ((S.T : Set (Variety.Point K)) ∪
        standardLeviRootFactor S.D (RootSubsystemSpan S.D S.J)) :
          Set (Variety.Point K)) := by
    have hl : S.L.includePoint l ∈ S.L.toSubgroup := by
      change (S.L.pointEquiv l).1 ∈ S.L.toSubgroup
      exact (S.L.pointEquiv l).2
    have halign := congrArg (fun H : ClosedSubgroup K => H.toSubgroup)
      S.levi_alignment
    have hl' : S.L.includePoint l ∈
        (subgroupZariskiClosure K
          (Subgroup.closure ((S.T : Set (Variety.Point K)) ∪
            standardLeviRootFactor S.D
              (RootSubsystemSpan S.D S.J)))).toSubgroup := by
      rw [← halign]
      exact hl
    exact hl'
  have hlZ : S.L.includePoint l ∈ Z :=
    closure_minimal hgenZ
      (Variety.isClosed_iff_isZariskiClosed.mpr hZclosed) hlclosure
  have heq := congrArg (fun y : Variety.Point (affineSpaceVariety k PUnit) =>
      y.val PUnit.unit) hlZ
  change f (S.L.includePoint l) = g (S.L.includePoint l) at heq
  dsimp only [f, g] at heq
  rw [polynomialFunction_smul_apply] at heq
  have hinclude : S.L.includePoint l = S.L.inclusion.onPoints l := rfl
  rw [hinclude] at heq
  rw [sourceCoordinateColumnAmbientExtension_apply,
    sourceCoordinateColumnAmbientExtension_apply] at heq
  simp only [Pi.smul_apply]
  rw [sourceCoordinateActionValue_single S gamma (a * t) l]
  rw [sourceCoordinateActionValue_single S gamma t l]
  exact heq

private theorem sourceCoordinateConjugation_linearAt
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety) :
    SourceCoordinateLinearAt S l := by
  apply sourceCoordinateLinearAt_of_single
  intro a gamma t
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  have hsingle :
      a • (Pi.single gamma t : RelativeRootSourceExactIndex S → k) =
        Pi.single gamma (a * t) := by
    funext eta
    simp [Pi.single_apply, smul_eq_mul]
  rw [hsingle]
  exact sourceCoordinateConjugation_single_homogeneous S l a gamma t

/-- The linear equivalence underlying source-Levi coordinate conjugation at
a fixed Levi point. -/
public noncomputable def sourceCoordinateLinearEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety) :
    (RelativeRootSourceExactIndex S → k) ≃ₗ[k]
      (RelativeRootSourceExactIndex S → k) where
  toAddEquiv := sourceCoordinateAddEquiv S l
  map_smul' := by
    intro a v
    change sourceCoordinateAddEquiv S l (a • v) =
      a • sourceCoordinateAddEquiv S l v
    rw [sourceCoordinateAddEquiv_apply, sourceCoordinateAddEquiv_apply]
    exact sourceCoordinateConjugation_linearAt S l a v

private theorem sourceCoordinateLinearEquiv_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (v : RelativeRootSourceExactIndex S → k) :
    sourceCoordinateLinearEquiv S l v = sourceCoordinateActionValue S l v :=
  rfl

/-- The transported source-Levi coordinate action as a homomorphism into
linear automorphisms of the exact-height coordinate space. -/
@[expose]
public noncomputable def
    RelativeRootRepresentationSource.sourceLayerCarrierCoordinateLinearAction
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    Variety.Point S.L.carrierVariety →*
      LinearMap.GeneralLinearGroup k (RelativeRootSourceExactIndex S → k) where
  toFun := fun l ↦ LinearMap.GeneralLinearGroup.ofLinearEquiv
    (sourceCoordinateLinearEquiv S l)
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change sourceCoordinateActionValue S 1 v = v
    change Multiplicative.toAdd
      ((S.sourceLayerCarrierCoordinateConjugationHom 1)
        (Multiplicative.ofAdd v)) = v
    rw [map_one]
    rfl
  map_mul' := by
    intro a b
    apply Units.ext
    apply LinearMap.ext
    intro v
    change sourceCoordinateActionValue S (a * b) v =
      sourceCoordinateActionValue S a (sourceCoordinateActionValue S b v)
    exact sourceCoordinateActionValue_mul S a b v

/-- Evaluating the source coordinate linear action gives the original
transported quotient-conjugation coordinate function. -/
public theorem
    RelativeRootRepresentationSource.sourceLayerCarrierCoordinateLinearAction_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (v : RelativeRootSourceExactIndex S → k) :
    (((S.sourceLayerCarrierCoordinateLinearAction l :
      LinearMap.GeneralLinearGroup k (RelativeRootSourceExactIndex S → k)) :
        Module.End k (RelativeRootSourceExactIndex S → k)) v) =
      sourceCoordinateActionValue S l v :=
  sourceCoordinateLinearEquiv_apply S l v

/-- Source-Levi conjugation on exact-height coordinates, packaged as a
rational-representation candidate. -/
@[expose]
public noncomputable def
    RelativeRootRepresentationSource.sourceLayerCoordinateRationalRepresentation
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    RationalRepresentation S.L.carrierVariety
      (RelativeRootSourceExactIndex S → k) where
  action := S.sourceLayerCarrierCoordinateLinearAction

private noncomputable def sourceCoordinateVectorPolynomialFunction
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (v : RelativeRootSourceExactIndex S → k)
    (eta : RelativeRootSourceExactIndex S) :
    S.L.carrierVariety.PolynomialFunction := by
  letI := Fintype.ofFinite (RelativeRootSourceExactIndex S)
  exact ∑ gamma, sourceCoordinateColumnPolynomialFunction S gamma (v gamma) eta

omit [IsAlgClosed k] in
private theorem polynomialFunction_finset_sum_apply
    {V : Variety k} {I : Type u}
    (s : Finset I) (f : I → V.PolynomialFunction)
    (x : Variety.Point V) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      simp only [Variety.PolynomialFunction.toFun, Subring.coe_add, Pi.add_apply]
      exact congrArg (fun z ↦ f a x + z) ih

omit [IsAlgClosed k] in
private theorem function_finset_sum_apply
    {I : Type u} {A : Type u}
    (s : Finset I) (f : I → A → k) (x : A) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [Pi.add_apply, ih]

private theorem sourceCoordinateVectorPolynomialFunction_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (v : RelativeRootSourceExactIndex S → k)
    (eta : RelativeRootSourceExactIndex S)
    (l : Variety.Point S.L.carrierVariety) :
    sourceCoordinateVectorPolynomialFunction S v eta l =
      sourceCoordinateActionValue S l v eta := by
  letI := Fintype.ofFinite (RelativeRootSourceExactIndex S)
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  have hv : v = ∑ gamma, Pi.single gamma (v gamma) := by
    funext zeta
    simp
  rw [sourceCoordinateVectorPolynomialFunction]
  rw [polynomialFunction_finset_sum_apply Finset.univ]
  simp_rw [sourceCoordinateColumnPolynomialFunction_apply]
  have hcolumn : ∀ gamma,
      ((sourceCoordinateConjugationColumnMorphism S gamma (v gamma)).toFun l).val eta =
        sourceCoordinateActionValue S l (Pi.single gamma (v gamma)) eta := by
    intro gamma
    exact congrFun (sourceCoordinateActionValue_single S gamma (v gamma) l) eta |>.symm
  simp_rw [hcolumn]
  calc
    (∑ gamma, sourceCoordinateActionValue S l
        (Pi.single gamma (v gamma)) eta) =
        sourceCoordinateActionValue S l
          (∑ gamma, Pi.single gamma (v gamma)) eta := by
      have hmap := map_sum (sourceCoordinateAddEquiv S l)
        (fun gamma ↦ Pi.single gamma (v gamma)) Finset.univ
      simp only [sourceCoordinateAddEquiv_apply] at hmap
      rw [← function_finset_sum_apply Finset.univ]
      exact congrFun hmap.symm eta
    _ = sourceCoordinateActionValue S l v eta := by rw [← hv]

omit [IsAlgClosed k] in
private theorem basis_repr_eq_sum_pi_single
    {I : Type u} [Fintype I] [DecidableEq I]
    (b : Module.Basis (Fin (Module.finrank k (I → k))) k (I → k))
    (w : I → k) (i : Fin (Module.finrank k (I → k))) :
    b.repr w i = ∑ eta, b.repr (Pi.single eta 1) i * w eta := by
  have hw : w = ∑ eta, w eta • (Pi.single eta 1 : I → k) := by
    funext zeta
    simp [Pi.single_apply]
  calc
    b.repr w i = b.repr (∑ eta, w eta • (Pi.single eta 1 : I → k)) i := by
      exact congrArg (fun z ↦ b.repr z i) hw
    _ = ∑ eta, w eta * b.repr (Pi.single eta 1) i := by
      rw [map_sum]
      simp
    _ = ∑ eta, b.repr (Pi.single eta 1) i * w eta := by
      apply Finset.sum_congr rfl
      intro eta _
      ring

private noncomputable def sourceCoordinateMatrixCoefficient
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (b : Module.Basis
      (Fin (Module.finrank k (RelativeRootSourceExactIndex S → k))) k
      (RelativeRootSourceExactIndex S → k))
    (i j : Fin (Module.finrank k (RelativeRootSourceExactIndex S → k))) :
    S.L.carrierVariety.PolynomialFunction := by
  letI := Fintype.ofFinite (RelativeRootSourceExactIndex S)
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  exact ∑ eta, (b.repr (Pi.single eta 1) i) •
    sourceCoordinateVectorPolynomialFunction S (b j) eta

private theorem sourceCoordinateMatrixCoefficient_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (b : Module.Basis
      (Fin (Module.finrank k (RelativeRootSourceExactIndex S → k))) k
      (RelativeRootSourceExactIndex S → k))
    (i j : Fin (Module.finrank k (RelativeRootSourceExactIndex S → k)))
    (l : Variety.Point S.L.carrierVariety) :
    sourceCoordinateMatrixCoefficient S b i j l =
      b.repr (((S.sourceLayerCarrierCoordinateLinearAction l :
        LinearMap.GeneralLinearGroup k (RelativeRootSourceExactIndex S → k)) :
          Module.End k (RelativeRootSourceExactIndex S → k)) (b j)) i := by
  letI := Fintype.ofFinite (RelativeRootSourceExactIndex S)
  letI : DecidableEq (RelativeRootSourceExactIndex S) := Classical.decEq _
  rw [sourceCoordinateMatrixCoefficient]
  rw [polynomialFunction_finset_sum_apply Finset.univ]
  simp_rw [polynomialFunction_smul_apply]
  simp_rw [sourceCoordinateVectorPolynomialFunction_apply]
  change (∑ eta, b.repr (Pi.single eta 1) i *
      sourceCoordinateActionValue S l (b j) eta) = _
  rw [← basis_repr_eq_sum_pi_single b (sourceCoordinateActionValue S l (b j)) i]
  exact congrArg (fun z ↦ b.repr z i)
    (S.sourceLayerCarrierCoordinateLinearAction_apply l (b j)).symm

private noncomputable def sourceCoordinateInverseMatrixCoefficient
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (b : Module.Basis
      (Fin (Module.finrank k (RelativeRootSourceExactIndex S → k))) k
      (RelativeRootSourceExactIndex S → k))
    (i j : Fin (Module.finrank k (RelativeRootSourceExactIndex S → k))) :
    S.L.carrierVariety.PolynomialFunction :=
  Variety.PolynomialFunction.pullback
    (AlgebraicGroup.invMorphism S.L.carrierVariety)
    (sourceCoordinateMatrixCoefficient S b i j)

private theorem sourceCoordinateInverseMatrixCoefficient_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (b : Module.Basis
      (Fin (Module.finrank k (RelativeRootSourceExactIndex S → k))) k
      (RelativeRootSourceExactIndex S → k))
    (i j : Fin (Module.finrank k (RelativeRootSourceExactIndex S → k)))
    (l : Variety.Point S.L.carrierVariety) :
    sourceCoordinateInverseMatrixCoefficient S b i j l =
      b.repr (((((S.sourceLayerCarrierCoordinateLinearAction l)⁻¹ :
        LinearMap.GeneralLinearGroup k (RelativeRootSourceExactIndex S → k)) :
          Module.End k (RelativeRootSourceExactIndex S → k)) (b j))) i := by
  change sourceCoordinateMatrixCoefficient S b i j l⁻¹ = _
  rw [sourceCoordinateMatrixCoefficient_apply]
  simp

/-- The algebraic-group morphism whose rational points are the source-layer
coordinate linear automorphisms. -/
public noncomputable def
    RelativeRootRepresentationSource.sourceLayerCoordinateRepresentationMorphism
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    AlgebraicGroup.Morphism S.L.carrierVariety
      (glVarietyOf k (RelativeRootSourceExactIndex S → k)) := by
  let b := Module.finBasis k (RelativeRootSourceExactIndex S → k)
  exact generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    b S.sourceLayerCarrierCoordinateLinearAction
    (sourceCoordinateMatrixCoefficient S b)
    (sourceCoordinateInverseMatrixCoefficient S b)
    (sourceCoordinateMatrixCoefficient_apply S b)
    (sourceCoordinateInverseMatrixCoefficient_apply S b)

/-- The regular source-layer coordinate morphism agrees pointwise with the
linear coordinate action. -/
public theorem
    RelativeRootRepresentationSource.sourceLayerCoordinateRepresentationMorphism_point
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety) :
    let b := Module.finBasis k (RelativeRootSourceExactIndex S → k)
    glPointEquivOf k (RelativeRootSourceExactIndex S → k) b
        (S.sourceLayerCoordinateRepresentationMorphism.onPoints l) =
      S.sourceLayerCarrierCoordinateLinearAction l := by
  let b := Module.finBasis k (RelativeRootSourceExactIndex S → k)
  change glPointEquivOf k (RelativeRootSourceExactIndex S → k) b
      (generalLinearRepresentationPoint b
        (S.sourceLayerCarrierCoordinateLinearAction l)) = _
  exact glPointEquivOf_generalLinearRepresentationPoint b _

/-- The source-layer coordinate representation is rational. -/
public theorem
    RelativeRootRepresentationSource.sourceLayerCoordinateRationalRepresentation_isRational
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K) :
    IsRationalRepresentation S.sourceLayerCoordinateRationalRepresentation := by
  refine ⟨Module.finBasis k (RelativeRootSourceExactIndex S → k),
    S.sourceLayerCoordinateRepresentationMorphism, ?_⟩
  exact S.sourceLayerCoordinateRepresentationMorphism_point

/-- On a quotient class represented by `x`, the coordinate representation is
ambient conjugation by the included source-Levi point, followed by the exact
layer coordinate equivalence. -/
public theorem
    RelativeRootRepresentationSource.sourceLayerCoordinateRationalRepresentation_agrees_mk
    {K : Variety k} [AlgebraicGroup K]
    (S : RelativeRootRepresentationSource K)
    (l : Variety.Point S.L.carrierVariety)
    (x : sourceRelativeRootLayer S.D S.D.simple.toFinite.toFinset
      S.coeff S.J S.height) :
    Multiplicative.ofAdd
        (((S.sourceLayerCoordinateRationalRepresentation.action l :
          LinearMap.GeneralLinearGroup k (RelativeRootSourceExactIndex S → k)) :
            Module.End k (RelativeRootSourceExactIndex S → k))
          (Multiplicative.toAdd
            (relativeRootLayerQuotient_coordinateEquiv S
              (QuotientGroup.mk' (sourceAbstractNextLayer S) x)))) =
      relativeRootLayerQuotient_coordinateEquiv S
        (QuotientGroup.mk' (sourceAbstractNextLayer S)
          ⟨S.L.includePoint l * x.1 * (S.L.includePoint l)⁻¹, by
            have hnorm := S.levi_le_sourceRelativeRootLayer_normalizer S.height
              (S.L.pointEquiv l).2
            rw [Subgroup.mem_normalizer_iff] at hnorm
            exact (hnorm x.1).mp x.2⟩) := by
  change Multiplicative.ofAdd
      (((S.sourceLayerCarrierCoordinateLinearAction l :
        LinearMap.GeneralLinearGroup k (RelativeRootSourceExactIndex S → k)) :
          Module.End k (RelativeRootSourceExactIndex S → k))
        (Multiplicative.toAdd
          (relativeRootLayerQuotient_coordinateEquiv S
            (QuotientGroup.mk' (sourceAbstractNextLayer S) x)))) = _
  rw [S.sourceLayerCarrierCoordinateLinearAction_apply]
  rw [sourceCoordinateActionValue]
  simp only [ofAdd_toAdd]
  rw [S.sourceLayerCarrierCoordinateConjugationAction_apply]
  rw [MulEquiv.symm_apply_apply]
  rw [S.sourceLayerCarrierQuotientConjugationAction_mk]

end Theory.AlgebraicGroup
