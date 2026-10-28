module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.Setup
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicBounds
public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicCoordinateIndependence

/-!
# Exact relative-root layer coordinates

This module identifies every positive adjacent quotient in a
`ParabolicRelativeRootSetup` with the direct product of the additive root
coordinates at that exact relative height.  It transports the setup to the
standard-parabolic relative-root API, whose maintained generation theorem gives
surjectivity and whose filtered Chevalley collection theorem gives genuine
coordinate independence.

The same transport also exposes the first-layer identity
`S.U.toSubgroup = S.layer 1`, which lets consumers move between the ambient
unipotent radical and the coordinate filtration without rebuilding the
standard-parabolic setup.

The forward homomorphism first reindexes `S.layerRootIndex i` by the standard
exact-height root subtype, applies the standard Chevalley coordinate product,
and transports across the definitional equality of the two filtrations.
Injectivity is therefore the exact-height collection theorem rather than a
Borel root-product uniqueness assumption.  Surjectivity is inherited from the
exact-height generation API.  Their inverse multiplicative equivalence sends
the quotient class of `S.C.x alpha t` to
`Multiplicative.ofAdd (Pi.single alpha t)`.

This is the coordinate form of the usual Chevalley collection argument for an
adjacent relative-root layer.  It uses only the root-realization and Chevalley
data stored in the setup.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open scoped IsMulCommutative

variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable def ParabolicRelativeRootSetup.toStandardCoordinateSetup
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) :
    StandardParabolicRelativeRootSetup K := by
  letI := Fintype.ofFinite S.D.Root
  letI := Fintype.ofFinite S.ι
  refine
    { T := S.T
      B := S.B
      U := S.U
      D := S.D
      C := S.C
      finiteActualRoot := S.finiteActualRoot
      ι := S.ι
      X := S.X
      Y := S.Y
      finiteRoot := S.finiteRoot
      addCommGroupX := S.addCommGroupX
      addCommGroupY := S.addCommGroupY
      integralPairing := S.pairing
      integralRootSystem := S.isRootSystem
      integralCrystallographic := S.isCrystallographic
      integralReduced := S.isReduced
      integralBase := S.base
      rootEquiv := S.rootEquiv
      weightEquiv := S.weightEquiv
      positiveRoots := S.positiveRoots
      J := S.J
      sigmaJ := S.sigmaJ
      coeff := S.coeff
      integralRootAdditionRealization := S.integralRootAdditionRealization
      actualRootDatum := S.actualRootDatum
      integralSimpleRootExpansion := S.simpleRootExpansion
      standardParabolic := S.standardParabolic
      unipotentRootGeneration := S.unipotentRootGeneration
      XQ := S.XQ
      YQ := S.YQ
      addCommGroupXQ := S.addCommGroupXQ
      moduleXQ := S.moduleXQ
      addCommGroupYQ := S.addCommGroupYQ
      moduleYQ := S.moduleYQ
      rationalPairing := S.rootPairing
      rationalRootSystem := S.rootPairingIsRootSystem
      rationalCrystallographic := S.rootPairingIsCrystallographic
      rationalReduced := S.rootPairingIsReduced
      rationalBase := S.rootBase
      baseSupport_eq := S.rootBase_support.trans rfl
      rationalRootRealization := S.rootSystemRealization
      rationalRootAdditionRealization := S.rationalRootAdditionRealization
      rationalSimpleRootExpansion := S.rootSimpleRootExpansion
      chevalleySystem := S.chevalleySystem
      maxRelativeHeight := S.maxRelativeHeight
      relativeHeight_le := by
        intro alpha
        exact S.rootBase_support ▸ S.relativeHeight_le alpha }

omit [IsAlgClosed k] in
private lemma ParabolicRelativeRootSetup.toStandardCoordinateSetup_layer
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) :
    (S.toStandardCoordinateSetup.layer i : Subgroup (Variety.Point K)) =
      S.layer i := by
  simp [ParabolicRelativeRootSetup.toStandardCoordinateSetup,
    StandardParabolicRelativeRootSetup.layer,
    ParabolicRelativeRootSetup.layer, RelativeRootSeries,
    S.rootBase_support]
  rfl

omit [IsAlgClosed k] in
/-- The unipotent radical is the first layer of its relative-root
filtration. -/
public lemma ParabolicRelativeRootSetup.unipotent_eq_first_layer
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) :
    S.U.toSubgroup = S.layer 1 := by
  rw [← S.toStandardCoordinateSetup_layer 1]
  exact standardParabolicUnipotentRadical_eq_firstRelativeRootLayer
    S.toStandardCoordinateSetup

omit [IsAlgClosed k] in
/-- Adjacent relative-root layers are nested. -/
public lemma parabolicRelativeRootLayer_succ_le
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) :
    S.layer (i + 1) ≤ S.layer i := by
  letI := Fintype.ofFinite S.ι
  exact relativeRootSeries_antitone S.D S.rootEquiv S.base.support
    S.coeff S.J (Nat.le_succ i)

omit [IsAlgClosed k] in
/-- The next layer is normal in every positive relative-root layer. -/
public lemma parabolicRelativeRootLayer_next_normal
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    ((S.layer (i + 1)).subgroupOf (S.layer i)).Normal := by
  letI := Fintype.ofFinite S.ι
  rw [ParabolicRelativeRootSetup.layer,
    ParabolicRelativeRootSetup.layer, ← S.rootBase_support]
  exact relativeRootSeries_next_layer_normal S.D S.C S.rootPairing
    S.rootEquiv S.rootBase S.coeff S.rootSimpleRootExpansion
    S.chevalleySystem S.J i hi

omit [IsAlgClosed k] in
/-- Every positive adjacent relative-root quotient is commutative. -/
public lemma parabolicRelativeRootLayer_quotient_commutative
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    let hN := parabolicRelativeRootLayer_next_normal S i hi
    let := hN
    IsMulCommutative
      (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) := by
  dsimp only
  letI := Fintype.ofFinite S.ι
  let := parabolicRelativeRootLayer_next_normal S i hi
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  have hcomm : ⁅S.layer i, S.layer i⁆ ≤ S.layer (i + 1) := by
    simpa only [ParabolicRelativeRootSetup.layer, ← S.rootBase_support] using
      relativeRootSeries_commutator_same_layer_le_next_layer S.D S.C
        S.rootPairing S.rootEquiv S.rootBase S.coeff
        S.rootSimpleRootExpansion S.chevalleySystem S.J i hi
  have hmap : (_root_.commutator (S.layer i)).map (S.layer i).subtype ≤
      S.layer (i + 1) := by
    rw [Subgroup.map_subtype_commutator]
    exact hcomm
  simpa [Subgroup.comap_subtype] using
    (Subgroup.map_le_iff_le_comap.mp hmap)

private noncomputable def ParabolicRelativeRootSetup.layerRootIndexEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) :
    S.layerRootIndex i ≃ S.toStandardCoordinateSetup.ExactHeightRoot i where
  toFun alpha :=
    ⟨alpha.1, by
      change RelativeRootHeight S.coeff S.rootBase.support
        (S.rootEquiv '' S.J) (S.rootEquiv alpha.1) = i
      rw [S.rootBase_support]
      exact alpha.2⟩
  invFun alpha :=
    ⟨alpha.1, by
      have h := alpha.2
      change RelativeRootHeight S.coeff S.rootBase.support
        (S.rootEquiv '' S.J) (S.rootEquiv alpha.1) = i at h
      rw [← S.rootBase_support]
      exact h⟩
  left_inv alpha := Subtype.ext (by rfl)
  right_inv alpha := Subtype.ext (by rfl)

private noncomputable def ParabolicRelativeRootSetup.layerCoordinateReindexEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) :
    Multiplicative (S.layerRootIndex i → k) ≃*
      Multiplicative
        (S.toStandardCoordinateSetup.ExactHeightRoot i → k) := by
  change (S.layerRootIndex i → Multiplicative k) ≃*
    (S.toStandardCoordinateSetup.ExactHeightRoot i → Multiplicative k)
  exact MulEquiv.arrowCongr (S.layerRootIndexEquiv i) (MulEquiv.refl _)

omit [IsAlgClosed k] in
private lemma ParabolicRelativeRootSetup.layerCoordinateReindexEquiv_single
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ)
    (alpha : S.layerRootIndex i) (t : k) :
    letI : DecidableEq (S.layerRootIndex i) := Classical.decEq _
    letI : DecidableEq (S.toStandardCoordinateSetup.ExactHeightRoot i) :=
      Classical.decEq _
    S.layerCoordinateReindexEquiv i
        (Multiplicative.ofAdd (Pi.single alpha t)) =
      (Pi.mulSingle (S.layerRootIndexEquiv i alpha)
        (Multiplicative.ofAdd t) :
          S.toStandardCoordinateSetup.ExactHeightRoot i → Multiplicative k) := by
  classical
  ext beta
  simp only [ParabolicRelativeRootSetup.layerCoordinateReindexEquiv]
  change (Pi.single alpha t : S.layerRootIndex i → k)
      ((S.layerRootIndexEquiv i).symm beta) =
    (Pi.single (S.layerRootIndexEquiv i alpha) t :
      S.toStandardCoordinateSetup.ExactHeightRoot i → k) beta
  have hiff : (S.layerRootIndexEquiv i).symm beta = alpha ↔
      beta = S.layerRootIndexEquiv i alpha := by
    constructor
    · intro h
      simpa using congrArg (S.layerRootIndexEquiv i) h
    · intro h
      simpa using congrArg (S.layerRootIndexEquiv i).symm h
  simp only [Pi.single_apply, hiff]

omit [IsAlgClosed k] in
private lemma standardParabolicRelativeRootLayer_coordinateHom_mulSingle
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (alpha : S.ExactHeightRoot i) (t : k) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    letI := hN
    letI : DecidableEq (S.ExactHeightRoot i) := Classical.decEq _
    standardParabolicRelativeRootLayer_coordinateHom S i hi
        (Pi.mulSingle alpha (Multiplicative.ofAdd t) :
          S.ExactHeightRoot i → Multiplicative k) =
      standardParabolicRelativeRootLayer_rootCoordinateHom S i hi alpha
        (Multiplicative.ofAdd t) := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype (S.ExactHeightRoot i) := by
    unfold StandardParabolicRelativeRootSetup.ExactHeightRoot
    infer_instance
  dsimp only
  letI := standardParabolicRelativeRootLayer_next_normal S i hi
  letI := standardParabolicRelativeRootLayer_quotient_commutative S i hi
  rw [standardParabolicRelativeRootLayer_coordinateHom_apply]
  have h := congrArg
    (fun g => g alpha)
    ((Pi.monoidHomMulEquiv
      (fun _ : S.ExactHeightRoot i => Multiplicative k)
      (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i))).apply_symm_apply
        (fun beta =>
          standardParabolicRelativeRootLayer_rootCoordinateHom S i hi beta))
  simpa [Pi.monoidHomMulEquiv] using
    DFunLike.congr_fun h (Multiplicative.ofAdd t)

private noncomputable def ParabolicRelativeRootSetup.layerQuotientEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    let hSN := standardParabolicRelativeRootLayer_next_normal
      S.toStandardCoordinateSetup i hi
    letI := hSN
    let hN := parabolicRelativeRootLayer_next_normal S i hi
    letI := hN
    (S.toStandardCoordinateSetup.layer i ⧸
        (S.toStandardCoordinateSetup.layer (i + 1)).subgroupOf
          (S.toStandardCoordinateSetup.layer i)) ≃*
      (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) := by
  dsimp only
  letI := standardParabolicRelativeRootLayer_next_normal
    S.toStandardCoordinateSetup i hi
  letI := parabolicRelativeRootLayer_next_normal S i hi
  exact QuotientGroup.equivQuotientSubgroupOfOfEq
    (S.toStandardCoordinateSetup_layer (i + 1))
    (S.toStandardCoordinateSetup_layer i)

/-- The product of the exact-height Chevalley coordinates in the adjacent
relative-root quotient. -/
public noncomputable def parabolicRelativeRootLayer_coordinateHom
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    let hN := parabolicRelativeRootLayer_next_normal S i hi
    letI := hN
    Multiplicative (S.layerRootIndex i → k) →*
      (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) := by
  dsimp only
  letI := standardParabolicRelativeRootLayer_next_normal
    S.toStandardCoordinateSetup i hi
  letI := parabolicRelativeRootLayer_next_normal S i hi
  exact (S.layerQuotientEquiv i hi).toMonoidHom.comp
    ((standardParabolicRelativeRootLayer_coordinateHom
      S.toStandardCoordinateSetup i hi).comp
        (S.layerCoordinateReindexEquiv i).toMonoidHom)

/-- Exact-height Chevalley coordinates are independent in the adjacent
relative-root quotient. -/
public theorem parabolicRelativeRootLayer_coordinateHom_injective
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    Function.Injective (parabolicRelativeRootLayer_coordinateHom S i hi) := by
  letI := standardParabolicRelativeRootLayer_next_normal
    S.toStandardCoordinateSetup i hi
  letI := parabolicRelativeRootLayer_next_normal S i hi
  intro a b h
  apply (S.layerCoordinateReindexEquiv i).injective
  apply standardParabolicRelativeRootLayer_coordinateHom_injective
    S.toStandardCoordinateSetup i hi
  apply (S.layerQuotientEquiv i hi).injective
  exact h

omit [IsAlgClosed k] in
/-- Exact-height Chevalley coordinates generate the adjacent relative-root
quotient. -/
public theorem parabolicRelativeRootLayer_coordinateHom_surjective
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    Function.Surjective (parabolicRelativeRootLayer_coordinateHom S i hi) := by
  letI := standardParabolicRelativeRootLayer_next_normal
    S.toStandardCoordinateSetup i hi
  letI := parabolicRelativeRootLayer_next_normal S i hi
  intro q
  obtain ⟨b, hb⟩ :=
    standardParabolicRelativeRootLayer_coordinateHom_surjective
      S.toStandardCoordinateSetup i hi ((S.layerQuotientEquiv i hi).symm q)
  obtain ⟨a, ha⟩ := (S.layerCoordinateReindexEquiv i).surjective b
  refine ⟨a, ?_⟩
  change S.layerQuotientEquiv i hi
      (standardParabolicRelativeRootLayer_coordinateHom
        S.toStandardCoordinateSetup i hi
        (S.layerCoordinateReindexEquiv i a)) = q
  rw [ha, hb, MulEquiv.apply_symm_apply]

/-- The exact-height coordinate homomorphism is bijective. -/
public theorem parabolicRelativeRootLayer_coordinateHom_bijective
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    Function.Bijective (parabolicRelativeRootLayer_coordinateHom S i hi) :=
  ⟨parabolicRelativeRootLayer_coordinateHom_injective S i hi,
    parabolicRelativeRootLayer_coordinateHom_surjective S i hi⟩

omit [IsAlgClosed k] in
/-- The Chevalley root element associated with one exact-height coordinate. -/
public noncomputable def ParabolicRelativeRootSetup.layerRootElement
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ)
    (alpha : S.layerRootIndex i) (t : k) : S.layer i :=
  ⟨S.C.x alpha.1 t, by
    rw [ParabolicRelativeRootSetup.layer, RelativeRootSeries,
      RootSubgroupGenerated]
    apply Subgroup.subset_closure
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨alpha.1, by rw [alpha.2], ?_⟩
    rw [← (S.chevalleySystem.1 alpha.1).2]
    exact ⟨t, rfl⟩⟩

omit [IsAlgClosed k] in
/-- The underlying ambient point of an exact-height layer root element is its
Chevalley root element. -/
public theorem ParabolicRelativeRootSetup.layerRootElement_value
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ)
    (alpha : S.layerRootIndex i) (t : k) :
    (S.layerRootElement i alpha t : Variety.Point K) = S.C.x alpha.1 t := by
  rfl

omit [IsAlgClosed k] in
/-- A single exact-height coordinate maps to its Chevalley root element in the
adjacent quotient. -/
public theorem parabolicRelativeRootLayer_coordinateHom_single
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (alpha : S.layerRootIndex i) (t : k) :
    let hN := parabolicRelativeRootLayer_next_normal S i hi
    letI := hN
    letI : DecidableEq (S.layerRootIndex i) := Classical.decEq _
    parabolicRelativeRootLayer_coordinateHom S i hi
        (Multiplicative.ofAdd (Pi.single alpha t)) =
      QuotientGroup.mk'
        ((S.layer (i + 1)).subgroupOf (S.layer i))
        (S.layerRootElement i alpha t) := by
  classical
  dsimp only
  letI := parabolicRelativeRootLayer_next_normal S i hi
  letI := standardParabolicRelativeRootLayer_next_normal
    S.toStandardCoordinateSetup i hi
  change S.layerQuotientEquiv i hi
      (standardParabolicRelativeRootLayer_coordinateHom
        S.toStandardCoordinateSetup i hi
        (S.layerCoordinateReindexEquiv i
          (Multiplicative.ofAdd (Pi.single alpha t)))) = _
  rw [ParabolicRelativeRootSetup.layerCoordinateReindexEquiv_single]
  rw [standardParabolicRelativeRootLayer_coordinateHom_mulSingle]
  rw [standardParabolicRelativeRootLayer_rootCoordinateHom_apply]
  simp only [StandardParabolicRelativeRootSetup.ExactHeightRoot.root_eq_coe]
  rfl

/-- The inverse coordinate equivalence from the adjacent quotient to its direct
product of exact-height additive root coordinates. -/
public noncomputable def parabolicRelativeRootLayer_quotientCoordinateEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    let hN := parabolicRelativeRootLayer_next_normal S i hi
    letI := hN
    (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) ≃*
      Multiplicative (S.layerRootIndex i → k) := by
  dsimp only
  letI := parabolicRelativeRootLayer_next_normal S i hi
  exact (MulEquiv.ofBijective
    (parabolicRelativeRootLayer_coordinateHom S i hi)
    (parabolicRelativeRootLayer_coordinateHom_bijective S i hi)).symm

/-- Reconstructing a quotient class from its exact-height coordinates returns
the original class. -/
public theorem parabolicRelativeRootLayer_coordinateHom_quotientCoordinateEquiv
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (q : let hN := parabolicRelativeRootLayer_next_normal S i hi
      letI := hN
      S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) :
    let hN := parabolicRelativeRootLayer_next_normal S i hi
    letI := hN
    parabolicRelativeRootLayer_coordinateHom S i hi
        (parabolicRelativeRootLayer_quotientCoordinateEquiv S i hi q) = q := by
  dsimp only
  letI := parabolicRelativeRootLayer_next_normal S i hi
  let e := MulEquiv.ofBijective
    (parabolicRelativeRootLayer_coordinateHom S i hi)
    (parabolicRelativeRootLayer_coordinateHom_bijective S i hi)
  exact e.apply_symm_apply q

/-- Quotient coordinates of a Chevalley root element are the corresponding
single additive coordinate. -/
public theorem parabolicRelativeRootLayer_quotientCoordinateEquiv_root
    {K : Variety k} [AlgebraicGroup K]
    (S : ParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (alpha : S.layerRootIndex i) (t : k) :
    let hN := parabolicRelativeRootLayer_next_normal S i hi
    letI := hN
    letI : DecidableEq (S.layerRootIndex i) := Classical.decEq _
    parabolicRelativeRootLayer_quotientCoordinateEquiv S i hi
        (QuotientGroup.mk'
          ((S.layer (i + 1)).subgroupOf (S.layer i))
          (S.layerRootElement i alpha t)) =
      Multiplicative.ofAdd (Pi.single alpha t) := by
  classical
  dsimp only
  letI := parabolicRelativeRootLayer_next_normal S i hi
  let e := MulEquiv.ofBijective
    (parabolicRelativeRootLayer_coordinateHom S i hi)
    (parabolicRelativeRootLayer_coordinateHom_bijective S i hi)
  change e.symm
      (QuotientGroup.mk'
        ((S.layer (i + 1)).subgroupOf (S.layer i))
        (S.layerRootElement i alpha t)) =
    Multiplicative.ofAdd (Pi.single alpha t)
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  change QuotientGroup.mk'
      ((S.layer (i + 1)).subgroupOf (S.layer i))
      (S.layerRootElement i alpha t) =
    parabolicRelativeRootLayer_coordinateHom S i hi
      (Multiplicative.ofAdd (Pi.single alpha t))
  exact (parabolicRelativeRootLayer_coordinateHom_single S i hi alpha t).symm

end Theory.AlgebraicGroup
