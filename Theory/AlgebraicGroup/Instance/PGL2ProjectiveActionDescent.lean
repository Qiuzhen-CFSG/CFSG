module

public import Theory.AlgebraicGroup.Instance.PGL2ProjectionFaithfullyFlat
public import Theory.AlgebraicGroup.Instance.PGL2ProjectiveKernelPair
import all Theory.AlgebraicGroup.Instance.PGL2ProjectionFaithfullyFlat
import all Theory.AlgebraicGroup.Instance.PGL2ProjectiveKernelPair
import all Theory.AlgebraicGroup.Variety.AffineGeometricMorphism

/-!
# Descent of the projective SL2 action to PGL2

This module constructs the scheme morphism `PGL2 x P1 -> P1` by fpqc
descent of the standard projective-linear `SL2` action.  The affine central
projection is faithfully flat, and its base change over `PGL2 x P1` is
therefore an effective epimorphism.  Its kernel pair is compared explicitly
with `Spec (k[SL2] tensor_[k[PGL2]] k[SL2]) x P1`; the scheme-theoretic
kernel-pair equality proved in `PGL2ProjectiveKernelPair` supplies the descent
cocycle, including in characteristic two.

The final projection formula evaluates the descended morphism on every
rational point lifted from `SL2`.  It is the interface used by
`PGL2ProjectiveAction` to identify the descended map with Mathlib's PGL action
and package a genuine `MorphicAction`.

The construction is the fpqc form of the standard homogeneous-coordinate
action in Borel, *Linear Algebraic Groups*, Section 7.2.  The effective
descent input is `PGL2ProjectionFaithfullyFlat`; the full nonreduced
kernel-pair calculation is `PGL2ProjectiveKernelPair`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric

set_option maxHeartbeats 1000000

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem finrankFinTwo : Module.finrank k (Fin 2 -> k) = 2 := by
  rw [Module.finrank_fin_fun k]

public noncomputable abbrev projectiveRankTwo :=
  projectiveSpaceByCoordinates k
    (Fin (Module.finrank k (Fin 2 -> k)))

omit [IsAlgClosed k] in
public theorem projectiveRankTwo_eq_projectiveLine :
    projectiveRankTwo (k := k) = projectiveLine k := by
  simp only [projectiveRankTwo, projectiveLine, finrankFinTwo]

/-- The restricted projective action with its target written in the exact
coordinate model used by the kernel-pair calculation. -/
public noncomputable abbrev sl2ProjectiveRankTwoMorphicAction :
    MorphicAction
      (slVariety k (Module.finrank k (Fin 2 -> k)))
      (projectiveRankTwo (k := k)) :=
  sl2ProjectiveCoordinateMorphicAction (k := k)

/-- The restricted projective-linear action with its rank-two target
normalized to the geometric projective-line carrier. -/
@[expose] public noncomputable def sl2ProjectiveLineMorphicAction :
    MorphicAction
      (slVariety k (Module.finrank k (Fin 2 -> k)))
      (projectiveLine k) :=
  projectiveRankTwo_eq_projectiveLine (k := k) ▸
    sl2ProjectiveRankTwoMorphicAction (k := k)

private theorem symm_transport_morphicAction_smul
    {G : Variety k} [AlgebraicGroup G] {V W : Geometric k}
    (h : V = W) (A : MorphicAction G V) (g : Variety.Point G) (x : Point W) :
    h.symm ▸ (h ▸ A).toMulAction.smul g x =
      A.toMulAction.smul g (h.symm ▸ x) := by
  cases h
  rfl

/-- Undoing the carrier normalization identifies the projective-line `SL2`
action with the coordinate projective action. -/
public theorem sl2ProjectiveLineMorphicAction_smul_transport
    (s : Variety.Point
      (slVariety k (Module.finrank k (Fin 2 -> k))))
    (x : Point (projectiveLine k)) :
    let h := projectiveRankTwo_eq_projectiveLine (k := k)
    h.symm ▸ (sl2ProjectiveLineMorphicAction (k := k)).toMulAction.smul s x =
      (sl2ProjectiveRankTwoMorphicAction (k := k)).toMulAction.smul s
        (h.symm ▸ x) := by
  exact symm_transport_morphicAction_smul
    (projectiveRankTwo_eq_projectiveLine (k := k))
    (sl2ProjectiveRankTwoMorphicAction (k := k)) s x

private noncomputable abbrev SL2Scheme :=
  (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k)))).toScheme

private noncomputable abbrev PGL2Scheme :=
  (ofAffine (pgl2Variety (k := k))).toScheme

private noncomputable abbrev P1Scheme := (projectiveRankTwo (k := k)).toScheme

private theorem prodScheme_hom_ext {V W : Geometric k} {X : Scheme}
    {f g : X ⟶ (prod V W).toScheme}
    (hfst : f ≫ (fst V W).hom = g ≫ (fst V W).hom)
    (hsnd : f ≫ (snd V W).hom = g ≫ (snd V W).hom) : f = g := by
  apply pullback.hom_ext
  · exact hfst
  · exact hsnd

private theorem transportedAction_apply
    {G V W : Geometric k} {H : Variety k} [AlgebraicGroup H] (h : V = W)
    (f : Morphism (prod G V) V) (A : MorphicAction H V)
    (g : Point G) (s : Variety.Point H) (x : Point W)
    (hx : f (prodPoint g (h.symm ▸ x)) =
      A.toMulAction.smul s (h.symm ▸ x)) :
    (h ▸ f) (prodPoint g x) = (h ▸ A).toMulAction.smul s x := by
  cases h
  exact hx

private noncomputable abbrev PGL2P1Scheme :=
  (prod (ofAffine (pgl2Variety (k := k))) (projectiveRankTwo (k := k))).toScheme

private noncomputable abbrev actionCoverScheme :=
  pullback
    (fst (ofAffine (pgl2Variety (k := k))) (projectiveRankTwo (k := k))).hom
    (pgl2ProjectionGeometric (k := k)).hom

private noncomputable abbrev actionProjectionBaseChange :
    actionCoverScheme (k := k) ⟶ PGL2P1Scheme (k := k) :=
  pullback.fst
    (fst (ofAffine (pgl2Variety (k := k)))
      (projectiveRankTwo (k := k))).hom
    (pgl2ProjectionGeometric (k := k)).hom

private theorem actionProjectionBaseChange_effectiveEpi :
    EffectiveEpi (actionProjectionBaseChange (k := k)) := by
  exact pgl2ProjectionGeometric_baseChange_effectiveEpi
    (fst (ofAffine (pgl2Variety (k := k)))
      (projectiveRankTwo (k := k))).hom

/-- The source map from the base-changed cover to `SL2 x P1`. -/
private noncomputable def actionCoverToSL2P1 :
    actionCoverScheme (k := k) ⟶
      (prod
        (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k))))
        (projectiveRankTwo (k := k))).toScheme :=
  pullback.lift
    (pullback.snd
      (fst (ofAffine (pgl2Variety (k := k))) (projectiveRankTwo (k := k))).hom
      (pgl2ProjectionGeometric (k := k)).hom)
    (pullback.fst
      (fst (ofAffine (pgl2Variety (k := k))) (projectiveRankTwo (k := k))).hom
      (pgl2ProjectionGeometric (k := k)).hom ≫
        (snd (ofAffine (pgl2Variety (k := k))) (projectiveRankTwo (k := k))).hom)
    (by
      simp only [Category.assoc]
      rw [← (pgl2ProjectionGeometric (k := k)).commutes]
      rw [← pullback.condition_assoc]
      rw [(snd (ofAffine (pgl2Variety (k := k)))
        (projectiveRankTwo (k := k))).commutes]
      exact congrArg (fun q ↦ pullback.fst
          (fst (ofAffine (pgl2Variety (k := k)))
            (projectiveRankTwo (k := k))).hom
          (pgl2ProjectionGeometric (k := k)).hom ≫ q)
        (fst (ofAffine (pgl2Variety (k := k)))
          (projectiveRankTwo (k := k))).commutes)

@[reassoc]
private theorem actionCoverToSL2P1_fst :
    actionCoverToSL2P1 (k := k) ≫
        (fst
          (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k))))
          (projectiveRankTwo (k := k))).hom =
      pullback.snd
        (fst (ofAffine (pgl2Variety (k := k)))
          (projectiveRankTwo (k := k))).hom
        (pgl2ProjectionGeometric (k := k)).hom := by
  unfold actionCoverToSL2P1 fst prod
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem actionCoverToSL2P1_snd :
    actionCoverToSL2P1 (k := k) ≫
        (snd
          (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k))))
          (projectiveRankTwo (k := k))).hom =
      actionProjectionBaseChange (k := k) ≫
        (snd (ofAffine (pgl2Variety (k := k)))
          (projectiveRankTwo (k := k))).hom := by
  unfold actionCoverToSL2P1 actionProjectionBaseChange snd prod
  exact pullback.lift_snd _ _ _

/-- The restricted `SL2` action, viewed on the base-changed cover. -/
private noncomputable def actionOnCover :
  actionCoverScheme (k := k) ⟶ P1Scheme (k := k) :=
  actionCoverToSL2P1 (k := k) ≫
    (sl2ProjectiveRankTwoMorphicAction (k := k)).actionMorphism.hom

private noncomputable abbrev kernelPairSpec :=
  Spec (CommRingCat.of (sl2ProjectiveKernelPairRing (k := k)))

private noncomputable abbrev kernelPairP1 :=
  pullback
    (Spec.map (CommRingCat.ofHom
      (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
    (projectiveRankTwo (k := k)).structureMap

private noncomputable abbrev kernelPairLeftToSL2 :
    kernelPairSpec (k := k) ⟶ SL2Scheme (k := k) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom
      (R := coordinateRing (pgl2Variety (k := k)))
      (A := coordinateRing
        (slVariety k (Module.finrank k (Fin 2 -> k))))
      (B := coordinateRing
        (slVariety k (Module.finrank k (Fin 2 -> k))))))

private noncomputable abbrev kernelPairRightToSL2 :
    kernelPairSpec (k := k) ⟶ SL2Scheme (k := k) :=
  Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.includeRight :
      coordinateRing
          (slVariety k (Module.finrank k (Fin 2 -> k))) →ₐ[
        coordinateRing (pgl2Variety (k := k))]
          sl2ProjectiveKernelPairRing (k := k)).toRingHom))

private theorem kernelPairToPGL2_eq :
    kernelPairLeftToSL2 (k := k) ≫
        (pgl2ProjectionGeometric (k := k)).hom =
      kernelPairRightToSL2 (k := k) ≫
        (pgl2ProjectionGeometric (k := k)).hom := by
  unfold kernelPairLeftToSL2 kernelPairRightToSL2 kernelPairSpec SL2Scheme
  unfold pgl2ProjectionGeometric ofAffine_morphism
  change _ ≫ Spec.map (CommRingCat.ofHom
      (ofAffinePullback (pgl2Projection (k := k)).toVariety).toRingHom) =
    _ ≫ Spec.map (CommRingCat.ofHom
      (ofAffinePullback (pgl2Projection (k := k)).toVariety).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

private theorem kernelPairLeftToSL2_structure :
    kernelPairLeftToSL2 (k := k) ≫
        (ofAffine
          (slVariety k (Module.finrank k (Fin 2 -> k)))).structureMap =
      Spec.map (CommRingCat.ofHom
        (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))) := by
  unfold kernelPairLeftToSL2 kernelPairSpec SL2Scheme ofAffine
  rw [← Spec.map_comp]
  congr 1

private theorem kernelPairRightToSL2_structure :
    kernelPairRightToSL2 (k := k) ≫
        (ofAffine
          (slVariety k (Module.finrank k (Fin 2 -> k)))).structureMap =
      Spec.map (CommRingCat.ofHom
        (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))) := by
  unfold kernelPairRightToSL2 kernelPairSpec SL2Scheme ofAffine
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp [sl2ProjectiveKernelPairRing]

private noncomputable def kernelPairLeftToSL2P1 :
    kernelPairP1 (k := k) ⟶
      (prod
        (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k))))
        (projectiveRankTwo (k := k))).toScheme :=
  pullback.lift
    (pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
      (projectiveRankTwo (k := k)).structureMap ≫ kernelPairLeftToSL2 (k := k))
    (pullback.snd
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
      (projectiveRankTwo (k := k)).structureMap)
    (by
      simp only [Category.assoc]
      rw [kernelPairLeftToSL2_structure]
      exact pullback.condition)

private noncomputable def kernelPairRightToSL2P1 :
    kernelPairP1 (k := k) ⟶
      (prod
        (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k))))
        (projectiveRankTwo (k := k))).toScheme :=
  pullback.lift
    (pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
      (projectiveRankTwo (k := k)).structureMap ≫ kernelPairRightToSL2 (k := k))
    (pullback.snd
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
      (projectiveRankTwo (k := k)).structureMap)
    (by
      simp only [Category.assoc]
      rw [kernelPairRightToSL2_structure]
      exact pullback.condition)

@[reassoc]
private theorem kernelPairLeftToSL2P1_fst :
    kernelPairLeftToSL2P1 (k := k) ≫
        (fst
          (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k))))
          (projectiveRankTwo (k := k))).hom =
      pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
          (projectiveRankTwo (k := k)).structureMap ≫
        kernelPairLeftToSL2 (k := k) := by
  unfold kernelPairLeftToSL2P1 fst prod
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem kernelPairLeftToSL2P1_snd :
    kernelPairLeftToSL2P1 (k := k) ≫
        (snd
          (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k))))
          (projectiveRankTwo (k := k))).hom =
      pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
        (projectiveRankTwo (k := k)).structureMap := by
  unfold kernelPairLeftToSL2P1 snd prod
  exact pullback.lift_snd _ _ _

@[reassoc]
private theorem kernelPairRightToSL2P1_fst :
    kernelPairRightToSL2P1 (k := k) ≫
        (fst
          (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k))))
          (projectiveRankTwo (k := k))).hom =
      pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
          (projectiveRankTwo (k := k)).structureMap ≫
        kernelPairRightToSL2 (k := k) := by
  unfold kernelPairRightToSL2P1 fst prod
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem kernelPairRightToSL2P1_snd :
    kernelPairRightToSL2P1 (k := k) ≫
        (snd
          (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k))))
          (projectiveRankTwo (k := k))).hom =
      pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
        (projectiveRankTwo (k := k)).structureMap := by
  unfold kernelPairRightToSL2P1 snd prod
  exact pullback.lift_snd _ _ _

private theorem kernelPairLeftToSL2P1_action :
    kernelPairLeftToSL2P1 (k := k) ≫
        (sl2ProjectiveRankTwoMorphicAction (k := k)).actionMorphism.hom =
      sl2ProjectiveKernelPairLeftFamilyMap (k := k) := by
  change sl2ProjectiveKernelPairLeftSource (k := k) ≫
      (sl2ProjectiveMorphicAction (k := k)).actionMorphism.hom = _
  exact (sl2ProjectiveKernelPairActionBridge (k := k)).left

private noncomputable def kernelPairSpecIso :
    kernelPairSpec (k := k) ≅
      pullback (pgl2ProjectionGeometric (k := k)).hom
        (pgl2ProjectionGeometric (k := k)).hom :=
  (pullbackSpecIso
    (coordinateRing (pgl2Variety (k := k)))
    (coordinateRing (slVariety k (Module.finrank k (Fin 2 -> k))))
    (coordinateRing (slVariety k (Module.finrank k (Fin 2 -> k))))).symm

private theorem kernelPairSpecIso_hom_fst :
    (kernelPairSpecIso (k := k)).hom ≫
        pullback.fst (pgl2ProjectionGeometric (k := k)).hom
          (pgl2ProjectionGeometric (k := k)).hom =
      kernelPairLeftToSL2 (k := k) := by
  exact pullbackSpecIso_inv_fst _ _ _

private theorem kernelPairSpecIso_hom_snd :
    (kernelPairSpecIso (k := k)).hom ≫
        pullback.snd (pgl2ProjectionGeometric (k := k)).hom
          (pgl2ProjectionGeometric (k := k)).hom =
      kernelPairRightToSL2 (k := k) := by
  exact pullbackSpecIso_inv_snd _ _ _

private noncomputable def kernelPairBaseToPGL2P1 :
    kernelPairP1 (k := k) ⟶ PGL2P1Scheme (k := k) :=
  pullback.lift
    (pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
      (projectiveRankTwo (k := k)).structureMap ≫ kernelPairLeftToSL2 (k := k) ≫
        (pgl2ProjectionGeometric (k := k)).hom)
    (pullback.snd
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
      (projectiveRankTwo (k := k)).structureMap)
    (by
      simp only [Category.assoc]
      rw [(pgl2ProjectionGeometric (k := k)).commutes]
      rw [kernelPairLeftToSL2_structure]
      exact pullback.condition)

@[reassoc]
private theorem kernelPairBaseToPGL2P1_fst :
    kernelPairBaseToPGL2P1 (k := k) ≫
        (fst (ofAffine (pgl2Variety (k := k)))
          (projectiveRankTwo (k := k))).hom =
      pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
          (projectiveRankTwo (k := k)).structureMap ≫
        kernelPairLeftToSL2 (k := k) ≫
        (pgl2ProjectionGeometric (k := k)).hom := by
  unfold kernelPairBaseToPGL2P1 fst prod
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem kernelPairBaseToPGL2P1_snd :
    kernelPairBaseToPGL2P1 (k := k) ≫
        (snd (ofAffine (pgl2Variety (k := k)))
          (projectiveRankTwo (k := k))).hom =
      pullback.snd
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
          (projectiveRankTwo (k := k)).structureMap := by
  unfold kernelPairBaseToPGL2P1 snd prod
  exact pullback.lift_snd _ _ _

private noncomputable def kernelPairLeftToCover :
    kernelPairP1 (k := k) ⟶ actionCoverScheme (k := k) :=
  pullback.lift
    (kernelPairBaseToPGL2P1 (k := k))
    (pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
      (projectiveRankTwo (k := k)).structureMap ≫ kernelPairLeftToSL2 (k := k))
    (by
      unfold kernelPairBaseToPGL2P1 fst prod
      rw [pullback.lift_fst, Category.assoc])

private noncomputable def kernelPairRightToCover :
    kernelPairP1 (k := k) ⟶ actionCoverScheme (k := k) :=
  pullback.lift
    (kernelPairBaseToPGL2P1 (k := k))
    (pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
      (projectiveRankTwo (k := k)).structureMap ≫ kernelPairRightToSL2 (k := k))
    (by
      unfold kernelPairBaseToPGL2P1 fst prod
      rw [pullback.lift_fst, Category.assoc, kernelPairToPGL2_eq])

@[reassoc]
private theorem kernelPairLeftToCover_fst :
    kernelPairLeftToCover (k := k) ≫
        actionProjectionBaseChange (k := k) =
      kernelPairBaseToPGL2P1 (k := k) := by
  unfold kernelPairLeftToCover actionProjectionBaseChange
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem kernelPairLeftToCover_snd :
    kernelPairLeftToCover (k := k) ≫
        pullback.snd
          (fst (ofAffine (pgl2Variety (k := k)))
            (projectiveRankTwo (k := k))).hom
          (pgl2ProjectionGeometric (k := k)).hom =
      pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
          (projectiveRankTwo (k := k)).structureMap ≫
        kernelPairLeftToSL2 (k := k) := by
  unfold kernelPairLeftToCover
  exact pullback.lift_snd _ _ _

@[reassoc]
private theorem kernelPairRightToCover_fst :
    kernelPairRightToCover (k := k) ≫
        actionProjectionBaseChange (k := k) =
      kernelPairBaseToPGL2P1 (k := k) := by
  unfold kernelPairRightToCover actionProjectionBaseChange
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem kernelPairRightToCover_snd :
    kernelPairRightToCover (k := k) ≫
        pullback.snd
          (fst (ofAffine (pgl2Variety (k := k)))
            (projectiveRankTwo (k := k))).hom
          (pgl2ProjectionGeometric (k := k)).hom =
      pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
          (projectiveRankTwo (k := k)).structureMap ≫
        kernelPairRightToSL2 (k := k) := by
  unfold kernelPairRightToCover
  exact pullback.lift_snd _ _ _

private noncomputable def kernelPairToCoverKernelPair :
    kernelPairP1 (k := k) ⟶
      pullback
        (actionProjectionBaseChange (k := k))
        (actionProjectionBaseChange (k := k)) :=
  pullback.lift
    (kernelPairLeftToCover (k := k))
    (kernelPairRightToCover (k := k))
    (by
      unfold kernelPairLeftToCover kernelPairRightToCover
      rw [pullback.lift_fst, pullback.lift_fst])

@[reassoc]
private theorem kernelPairToCoverKernelPair_fst :
    kernelPairToCoverKernelPair (k := k) ≫
        pullback.fst
          (actionProjectionBaseChange (k := k))
          (actionProjectionBaseChange (k := k)) =
      kernelPairLeftToCover (k := k) := by
  unfold kernelPairToCoverKernelPair
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem kernelPairToCoverKernelPair_snd :
    kernelPairToCoverKernelPair (k := k) ≫
        pullback.snd
          (actionProjectionBaseChange (k := k))
          (actionProjectionBaseChange (k := k)) =
      kernelPairRightToCover (k := k) := by
  unfold kernelPairToCoverKernelPair
  exact pullback.lift_snd _ _ _

private noncomputable def coverKernelPairToSL2KernelPair :
    pullback
        (actionProjectionBaseChange (k := k))
        (actionProjectionBaseChange (k := k)) ⟶
      pullback (pgl2ProjectionGeometric (k := k)).hom
        (pgl2ProjectionGeometric (k := k)).hom :=
  pullback.lift
    (pullback.fst
      (actionProjectionBaseChange (k := k))
      (actionProjectionBaseChange (k := k)) ≫
        pullback.snd
          (fst (ofAffine (pgl2Variety (k := k))) (projectiveRankTwo (k := k))).hom
          (pgl2ProjectionGeometric (k := k)).hom)
    (pullback.snd
      (actionProjectionBaseChange (k := k))
      (actionProjectionBaseChange (k := k)) ≫
        pullback.snd
          (fst (ofAffine (pgl2Variety (k := k))) (projectiveRankTwo (k := k))).hom
          (pgl2ProjectionGeometric (k := k)).hom)
    (by
      have houter : actionProjectionBaseChange (k := k) ≫
            (fst (ofAffine (pgl2Variety (k := k)))
              (projectiveRankTwo (k := k))).hom =
          pullback.snd
              (fst (ofAffine (pgl2Variety (k := k)))
                (projectiveRankTwo (k := k))).hom
              (pgl2ProjectionGeometric (k := k)).hom ≫
            (pgl2ProjectionGeometric (k := k)).hom :=
        pullback.condition
      have hkernel :
          pullback.fst
              (actionProjectionBaseChange (k := k))
              (actionProjectionBaseChange (k := k)) ≫
            actionProjectionBaseChange (k := k) =
          pullback.snd
              (actionProjectionBaseChange (k := k))
              (actionProjectionBaseChange (k := k)) ≫
            actionProjectionBaseChange (k := k) :=
        pullback.condition
      calc
        pullback.fst
              (actionProjectionBaseChange (k := k))
              (actionProjectionBaseChange (k := k)) ≫
            pullback.snd
                (fst (ofAffine (pgl2Variety (k := k)))
                  (projectiveRankTwo (k := k))).hom
                (pgl2ProjectionGeometric (k := k)).hom ≫
              (pgl2ProjectionGeometric (k := k)).hom =
            (pullback.fst
                (actionProjectionBaseChange (k := k))
                (actionProjectionBaseChange (k := k)) ≫
              actionProjectionBaseChange (k := k)) ≫
                (fst (ofAffine (pgl2Variety (k := k)))
                  (projectiveRankTwo (k := k))).hom := by
              rw [Category.assoc, ← houter, ← Category.assoc]
        _ = (pullback.snd
                (actionProjectionBaseChange (k := k))
                (actionProjectionBaseChange (k := k)) ≫
              actionProjectionBaseChange (k := k)) ≫
                (fst (ofAffine (pgl2Variety (k := k)))
                  (projectiveRankTwo (k := k))).hom := by rw [hkernel]
        _ = pullback.snd
              (actionProjectionBaseChange (k := k))
              (actionProjectionBaseChange (k := k)) ≫
            pullback.snd
                (fst (ofAffine (pgl2Variety (k := k)))
                  (projectiveRankTwo (k := k))).hom
                (pgl2ProjectionGeometric (k := k)).hom ≫
              (pgl2ProjectionGeometric (k := k)).hom := by
            rw [Category.assoc, ← houter, ← Category.assoc])

@[reassoc]
private theorem coverKernelPairToSL2KernelPair_fst :
    coverKernelPairToSL2KernelPair (k := k) ≫
        pullback.fst (pgl2ProjectionGeometric (k := k)).hom
          (pgl2ProjectionGeometric (k := k)).hom =
      pullback.fst
          (actionProjectionBaseChange (k := k))
          (actionProjectionBaseChange (k := k)) ≫
        pullback.snd
          (fst (ofAffine (pgl2Variety (k := k)))
            (projectiveRankTwo (k := k))).hom
          (pgl2ProjectionGeometric (k := k)).hom := by
  unfold coverKernelPairToSL2KernelPair
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem coverKernelPairToSL2KernelPair_snd :
    coverKernelPairToSL2KernelPair (k := k) ≫
        pullback.snd (pgl2ProjectionGeometric (k := k)).hom
          (pgl2ProjectionGeometric (k := k)).hom =
      pullback.snd
          (actionProjectionBaseChange (k := k))
          (actionProjectionBaseChange (k := k)) ≫
        pullback.snd
          (fst (ofAffine (pgl2Variety (k := k)))
            (projectiveRankTwo (k := k))).hom
          (pgl2ProjectionGeometric (k := k)).hom := by
  unfold coverKernelPairToSL2KernelPair
  exact pullback.lift_snd _ _ _

private noncomputable def coverKernelPairToKernelPairSpec :
    pullback
        (actionProjectionBaseChange (k := k))
        (actionProjectionBaseChange (k := k)) ⟶
      kernelPairSpec (k := k) :=
  coverKernelPairToSL2KernelPair (k := k) ≫
    (kernelPairSpecIso (k := k)).inv

@[reassoc]
private theorem coverKernelPairToKernelPairSpec_left :
    coverKernelPairToKernelPairSpec (k := k) ≫
        kernelPairLeftToSL2 (k := k) =
      pullback.fst
          (actionProjectionBaseChange (k := k))
          (actionProjectionBaseChange (k := k)) ≫
        pullback.snd
          (fst (ofAffine (pgl2Variety (k := k))) (projectiveRankTwo (k := k))).hom
          (pgl2ProjectionGeometric (k := k)).hom := by
  unfold coverKernelPairToKernelPairSpec
  rw [Category.assoc, ← kernelPairSpecIso_hom_fst]
  rw [Iso.inv_hom_id_assoc]
  unfold coverKernelPairToSL2KernelPair
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem coverKernelPairToKernelPairSpec_right :
    coverKernelPairToKernelPairSpec (k := k) ≫
        kernelPairRightToSL2 (k := k) =
      pullback.snd
          (actionProjectionBaseChange (k := k))
          (actionProjectionBaseChange (k := k)) ≫
        pullback.snd
          (fst (ofAffine (pgl2Variety (k := k))) (projectiveRankTwo (k := k))).hom
          (pgl2ProjectionGeometric (k := k)).hom := by
  unfold coverKernelPairToKernelPairSpec
  rw [Category.assoc, ← kernelPairSpecIso_hom_snd]
  rw [Iso.inv_hom_id_assoc]
  unfold coverKernelPairToSL2KernelPair
  exact pullback.lift_snd _ _ _

private noncomputable def coverKernelPairToKernelPairP1 :
    pullback
        (actionProjectionBaseChange (k := k))
        (actionProjectionBaseChange (k := k)) ⟶
      kernelPairP1 (k := k) :=
  pullback.lift
    (coverKernelPairToKernelPairSpec (k := k))
    (pullback.fst
      (actionProjectionBaseChange (k := k))
      (actionProjectionBaseChange (k := k)) ≫
        actionProjectionBaseChange (k := k) ≫
        (snd (ofAffine (pgl2Variety (k := k))) (projectiveRankTwo (k := k))).hom)
    (by
      calc
        coverKernelPairToKernelPairSpec (k := k) ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))) =
            (coverKernelPairToKernelPairSpec (k := k) ≫
              kernelPairLeftToSL2 (k := k)) ≫
                (ofAffine
                  (slVariety k (Module.finrank k (Fin 2 -> k)))).structureMap := by
              rw [Category.assoc, kernelPairLeftToSL2_structure]
        _ = (pullback.fst
              (actionProjectionBaseChange (k := k))
              (actionProjectionBaseChange (k := k)) ≫
                pullback.snd
                  (fst (ofAffine (pgl2Variety (k := k)))
                    (projectiveRankTwo (k := k))).hom
                  (pgl2ProjectionGeometric (k := k)).hom) ≫
              (ofAffine
                (slVariety k (Module.finrank k (Fin 2 -> k)))).structureMap := by
              rw [coverKernelPairToKernelPairSpec_left]
        _ = (pullback.fst
                (actionProjectionBaseChange (k := k))
                (actionProjectionBaseChange (k := k)) ≫
              actionProjectionBaseChange (k := k) ≫
              (snd (ofAffine (pgl2Variety (k := k)))
                (projectiveRankTwo (k := k))).hom) ≫
            (projectiveRankTwo (k := k)).structureMap := by
              simp only [Category.assoc]
              rw [← (pgl2ProjectionGeometric (k := k)).commutes]
              rw [← pullback.condition_assoc]
              rw [pullback.condition_assoc]
              rw [(fst (ofAffine (pgl2Variety (k := k)))
                (projectiveRankTwo (k := k))).commutes]
              rw [(snd (ofAffine (pgl2Variety (k := k)))
                (projectiveRankTwo (k := k))).commutes]
              exact (pullback.condition_assoc
                (f := actionProjectionBaseChange (k := k))
                (g := actionProjectionBaseChange (k := k))
                (prod (ofAffine (pgl2Variety (k := k)))
                  (projectiveRankTwo (k := k))).structureMap).symm)

@[reassoc]
private theorem coverKernelPairToKernelPairP1_fst :
    coverKernelPairToKernelPairP1 (k := k) ≫
        pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
          (projectiveRankTwo (k := k)).structureMap =
      coverKernelPairToKernelPairSpec (k := k) := by
  unfold coverKernelPairToKernelPairP1
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem coverKernelPairToKernelPairP1_snd :
    coverKernelPairToKernelPairP1 (k := k) ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
          (projectiveRankTwo (k := k)).structureMap =
      pullback.fst
          (actionProjectionBaseChange (k := k))
          (actionProjectionBaseChange (k := k)) ≫
        actionProjectionBaseChange (k := k) ≫
        (snd (ofAffine (pgl2Variety (k := k)))
          (projectiveRankTwo (k := k))).hom := by
  unfold coverKernelPairToKernelPairP1
  exact pullback.lift_snd _ _ _

private theorem kernelPairToCoverKernelPair_toSpec :
    kernelPairToCoverKernelPair (k := k) ≫
        coverKernelPairToKernelPairSpec (k := k) =
      pullback.fst
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
        (projectiveRankTwo (k := k)).structureMap := by
  have h : kernelPairToCoverKernelPair (k := k) ≫
        coverKernelPairToSL2KernelPair (k := k) =
      pullback.fst
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
          (projectiveRankTwo (k := k)).structureMap ≫
        (kernelPairSpecIso (k := k)).hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, coverKernelPairToSL2KernelPair_fst,
        kernelPairSpecIso_hom_fst]
      rw [← Category.assoc, kernelPairToCoverKernelPair_fst,
        kernelPairLeftToCover_snd]
    · simp only [Category.assoc, coverKernelPairToSL2KernelPair_snd,
        kernelPairSpecIso_hom_snd]
      rw [← Category.assoc, kernelPairToCoverKernelPair_snd,
        kernelPairRightToCover_snd]
  unfold coverKernelPairToKernelPairSpec
  rw [← Category.assoc, h, Category.assoc,
    CategoryTheory.Iso.hom_inv_id, Category.comp_id]

private theorem kernelPairToCoverKernelPair_toP1 :
    kernelPairToCoverKernelPair (k := k) ≫
        coverKernelPairToKernelPairP1 (k := k) =
      𝟙 (kernelPairP1 (k := k)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, coverKernelPairToKernelPairP1_fst,
      kernelPairToCoverKernelPair_toSpec, Category.id_comp]
  · rw [Category.assoc, coverKernelPairToKernelPairP1_snd]
    rw [← Category.assoc, kernelPairToCoverKernelPair_fst]
    rw [← Category.assoc, kernelPairLeftToCover_fst]
    rw [kernelPairBaseToPGL2P1_snd, Category.id_comp]

@[reassoc]
private theorem coverKernelPairToKernelPairP1_base :
    coverKernelPairToKernelPairP1 (k := k) ≫
        kernelPairBaseToPGL2P1 (k := k) =
      pullback.fst
          (actionProjectionBaseChange (k := k))
          (actionProjectionBaseChange (k := k)) ≫
        actionProjectionBaseChange (k := k) := by
  apply prodScheme_hom_ext
  · rw [Category.assoc, kernelPairBaseToPGL2P1_fst]
    rw [← Category.assoc, coverKernelPairToKernelPairP1_fst]
    rw [← Category.assoc, coverKernelPairToKernelPairSpec_left]
    rw [Category.assoc]
    rw [← pullback.condition]
    simp only [Category.assoc]
  · rw [Category.assoc, kernelPairBaseToPGL2P1_snd,
      coverKernelPairToKernelPairP1_snd]
    simp only [Category.assoc]

private theorem coverKernelPairToKernelPairP1_leftCover :
    coverKernelPairToKernelPairP1 (k := k) ≫
        kernelPairLeftToCover (k := k) =
      pullback.fst
        (actionProjectionBaseChange (k := k))
        (actionProjectionBaseChange (k := k)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, kernelPairLeftToCover_fst,
      coverKernelPairToKernelPairP1_base]
  · rw [Category.assoc, kernelPairLeftToCover_snd]
    rw [← Category.assoc, coverKernelPairToKernelPairP1_fst,
      coverKernelPairToKernelPairSpec_left]

private theorem coverKernelPairToKernelPairP1_rightCover :
    coverKernelPairToKernelPairP1 (k := k) ≫
        kernelPairRightToCover (k := k) =
      pullback.snd
        (actionProjectionBaseChange (k := k))
        (actionProjectionBaseChange (k := k)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, kernelPairRightToCover_fst,
      coverKernelPairToKernelPairP1_base]
    exact pullback.condition
  · rw [Category.assoc, kernelPairRightToCover_snd]
    rw [← Category.assoc, coverKernelPairToKernelPairP1_fst,
      coverKernelPairToKernelPairSpec_right]

private theorem coverKernelPairToKernelPairP1_toCoverKernelPair :
    coverKernelPairToKernelPairP1 (k := k) ≫
        kernelPairToCoverKernelPair (k := k) =
      𝟙 (pullback
        (actionProjectionBaseChange (k := k))
        (actionProjectionBaseChange (k := k))) := by
  apply pullback.hom_ext
  · rw [Category.assoc, kernelPairToCoverKernelPair_fst,
      coverKernelPairToKernelPairP1_leftCover, Category.id_comp]
  · rw [Category.assoc, kernelPairToCoverKernelPair_snd,
      coverKernelPairToKernelPairP1_rightCover, Category.id_comp]

private noncomputable def kernelPairComparisonIso :
    kernelPairP1 (k := k) ≅
      pullback
        (actionProjectionBaseChange (k := k))
        (actionProjectionBaseChange (k := k)) where
  hom := kernelPairToCoverKernelPair (k := k)
  inv := coverKernelPairToKernelPairP1 (k := k)
  hom_inv_id := kernelPairToCoverKernelPair_toP1 (k := k)
  inv_hom_id := coverKernelPairToKernelPairP1_toCoverKernelPair (k := k)

private theorem kernelPairRightToSL2P1_action :
    kernelPairRightToSL2P1 (k := k) ≫
        (sl2ProjectiveRankTwoMorphicAction (k := k)).actionMorphism.hom =
      sl2ProjectiveKernelPairRightFamilyMap (k := k) := by
  change sl2ProjectiveKernelPairRightSource (k := k) ≫
      (sl2ProjectiveMorphicAction (k := k)).actionMorphism.hom = _
  exact (sl2ProjectiveKernelPairActionBridge (k := k)).right

private theorem kernelPairLeftToCover_action :
    kernelPairLeftToCover (k := k) ≫ actionOnCover (k := k) =
      sl2ProjectiveKernelPairLeftFamilyMap (k := k) := by
  unfold actionOnCover
  rw [← Category.assoc]
  have hsource : kernelPairLeftToCover (k := k) ≫
      actionCoverToSL2P1 (k := k) = kernelPairLeftToSL2P1 (k := k) := by
    apply prodScheme_hom_ext
    · rw [Category.assoc, actionCoverToSL2P1_fst,
        kernelPairLeftToSL2P1_fst, kernelPairLeftToCover_snd]
    · rw [Category.assoc, actionCoverToSL2P1_snd,
        kernelPairLeftToSL2P1_snd]
      rw [← Category.assoc, kernelPairLeftToCover_fst,
        kernelPairBaseToPGL2P1_snd]
  rw [hsource]
  exact kernelPairLeftToSL2P1_action (k := k)

private theorem kernelPairRightToCover_action :
    kernelPairRightToCover (k := k) ≫ actionOnCover (k := k) =
      sl2ProjectiveKernelPairRightFamilyMap (k := k) := by
  unfold actionOnCover
  rw [← Category.assoc]
  have hsource : kernelPairRightToCover (k := k) ≫
      actionCoverToSL2P1 (k := k) = kernelPairRightToSL2P1 (k := k) := by
    apply prodScheme_hom_ext
    · rw [Category.assoc, actionCoverToSL2P1_fst,
        kernelPairRightToSL2P1_fst, kernelPairRightToCover_snd]
    · rw [Category.assoc, actionCoverToSL2P1_snd,
        kernelPairRightToSL2P1_snd]
      rw [← Category.assoc, kernelPairRightToCover_fst,
        kernelPairBaseToPGL2P1_snd]
  rw [hsource]
  exact kernelPairRightToSL2P1_action (k := k)

private theorem actionOnCover_kernelPair :
    pullback.fst
        (actionProjectionBaseChange (k := k))
        (actionProjectionBaseChange (k := k)) ≫
          actionOnCover (k := k) =
      pullback.snd
        (actionProjectionBaseChange (k := k))
        (actionProjectionBaseChange (k := k)) ≫
          actionOnCover (k := k) := by
  rw [← cancel_epi (kernelPairComparisonIso (k := k)).hom]
  change kernelPairToCoverKernelPair (k := k) ≫ _ ≫ _ =
    kernelPairToCoverKernelPair (k := k) ≫ _ ≫ _
  unfold kernelPairToCoverKernelPair
  rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc,
    kernelPairLeftToCover_action, kernelPairRightToCover_action,
    sl2ProjectiveKernelPair_familyMap_eq]

private theorem actionOnCover_descends :
    ∃ u : PGL2P1Scheme (k := k) ⟶ P1Scheme (k := k),
      actionProjectionBaseChange (k := k) ≫ u =
        actionOnCover (k := k) := by
  let _ : EffectiveEpi
      (actionProjectionBaseChange (k := k)) :=
    actionProjectionBaseChange_effectiveEpi (k := k)
  exact IsRegularEpi.exists_of_isKernelPair
    (actionProjectionBaseChange (k := k))
    (IsPullback.of_hasPullback _ _)
    (actionOnCover (k := k))
    (actionOnCover_kernelPair (k := k))

/-- The scheme morphism obtained by fpqc descent of the standard `SL2`
action along the affine `PGL2` quotient. -/
noncomputable def descendedActionHom :
    PGL2P1Scheme (k := k) ⟶ P1Scheme (k := k) :=
  (actionOnCover_descends (k := k)).choose

private theorem projectionBaseChange_descendedActionHom :
    actionProjectionBaseChange (k := k) ≫
        descendedActionHom (k := k) =
      actionOnCover (k := k) :=
  (actionOnCover_descends (k := k)).choose_spec

private theorem descendedActionHom_commutes :
    descendedActionHom (k := k) ≫ (projectiveRankTwo (k := k)).structureMap =
      (prod (ofAffine (pgl2Variety (k := k)))
        (projectiveRankTwo (k := k))).structureMap := by
  rw [← cancel_epi
    (actionProjectionBaseChange (k := k))]
  rw [← Category.assoc, projectionBaseChange_descendedActionHom]
  unfold actionOnCover
  rw [Category.assoc,
    (sl2ProjectiveRankTwoMorphicAction (k := k)).actionMorphism.commutes]
  rw [← (fst
    (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k))))
    (projectiveRankTwo (k := k))).commutes]
  rw [← Category.assoc, actionCoverToSL2P1_fst]
  rw [← (pgl2ProjectionGeometric (k := k)).commutes]
  rw [← Category.assoc, ← pullback.condition]
  exact congrArg (fun q ↦ actionProjectionBaseChange (k := k) ≫ q)
    (fst (ofAffine (pgl2Variety (k := k)))
      (projectiveRankTwo (k := k))).commutes

/-- The descended action on the rank-indexed projective carrier used by the
scheme-theoretic kernel-pair calculation. -/
private noncomputable def pgl2ProjectiveRankTwoActionMorphism :
    Morphism
      (prod (ofAffine (pgl2Variety (k := k)))
        (projectiveRankTwo (k := k)))
      (projectiveRankTwo (k := k)) where
  hom := descendedActionHom (k := k)
  commutes := descendedActionHom_commutes (k := k)

/-- The descended action as a morphism of geometric varieties. -/
public noncomputable def pgl2ProjectiveLineActionMorphism :
    Morphism
      (prod (ofAffine (pgl2Variety (k := k))) (projectiveLine k))
      (projectiveLine k) :=
  projectiveRankTwo_eq_projectiveLine (k := k) ▸
    pgl2ProjectiveRankTwoActionMorphism (k := k)

private theorem pgl2ProjectionGeometric_affinePoint
    (s : Variety.Point
      (slVariety k (Module.finrank k (Fin 2 -> k)))) :
    pgl2ProjectionGeometric (k := k)
        ((affinePointEquiv
          (slVariety k (Module.finrank k (Fin 2 -> k)))).symm s) =
      (affinePointEquiv (pgl2Variety (k := k))).symm
        ((pgl2Projection (k := k)).onPoints s) := by
  apply (affinePointEquiv (pgl2Variety (k := k))).injective
  rw [affinePointEquiv_ofAffine_morphism]
  simp only [Equiv.apply_symm_apply]
  rfl

private noncomputable def actionCoverPointHom
    (s : Variety.Point
      (slVariety k (Module.finrank k (Fin 2 -> k))))
    (x : Point (projectiveRankTwo (k := k))) :
    Spec (CommRingCat.of k) ⟶ actionCoverScheme (k := k) :=
  pullback.lift
    (prodPoint
      ((affinePointEquiv (pgl2Variety (k := k))).symm
        ((pgl2Projection (k := k)).onPoints s)) x).1
    ((affinePointEquiv
      (slVariety k (Module.finrank k (Fin 2 -> k)))).symm s).1
    (by
      change ((fst (ofAffine (pgl2Variety (k := k)))
          (projectiveRankTwo (k := k)))
          (prodPoint
            ((affinePointEquiv (pgl2Variety (k := k))).symm
              ((pgl2Projection (k := k)).onPoints s)) x)).1 =
        (pgl2ProjectionGeometric (k := k)
          ((affinePointEquiv
            (slVariety k (Module.finrank k (Fin 2 -> k)))).symm s)).1
      rw [fst_prodPoint, pgl2ProjectionGeometric_affinePoint])

private theorem actionCoverPointHom_fst
    (s : Variety.Point
      (slVariety k (Module.finrank k (Fin 2 -> k))))
    (x : Point (projectiveRankTwo (k := k))) :
    actionCoverPointHom (k := k) s x ≫
        actionProjectionBaseChange (k := k) =
      (prodPoint
        ((affinePointEquiv (pgl2Variety (k := k))).symm
          ((pgl2Projection (k := k)).onPoints s)) x).1 := by
  unfold actionCoverPointHom actionProjectionBaseChange
  exact pullback.lift_fst _ _ _

private theorem actionCoverPointHom_snd
    (s : Variety.Point
      (slVariety k (Module.finrank k (Fin 2 -> k))))
    (x : Point (projectiveRankTwo (k := k))) :
    actionCoverPointHom (k := k) s x ≫
        pullback.snd
          (fst (ofAffine (pgl2Variety (k := k)))
            (projectiveRankTwo (k := k))).hom
          (pgl2ProjectionGeometric (k := k)).hom =
      ((affinePointEquiv
        (slVariety k (Module.finrank k (Fin 2 -> k)))).symm s).1 := by
  unfold actionCoverPointHom
  exact pullback.lift_snd _ _ _

private theorem actionCoverPointHom_toSL2P1
    (s : Variety.Point
      (slVariety k (Module.finrank k (Fin 2 -> k))))
    (x : Point (projectiveRankTwo (k := k))) :
    actionCoverPointHom (k := k) s x ≫
        actionCoverToSL2P1 (k := k) =
      (prodPoint
        ((affinePointEquiv
          (slVariety k (Module.finrank k (Fin 2 -> k)))).symm s) x).1 := by
  apply prodScheme_hom_ext
  · rw [Category.assoc, actionCoverToSL2P1_fst,
      actionCoverPointHom_snd]
    exact congrArg Subtype.val (fst_prodPoint
      ((affinePointEquiv
        (slVariety k (Module.finrank k (Fin 2 -> k)))).symm s) x).symm
  · rw [Category.assoc, actionCoverToSL2P1_snd]
    rw [← Category.assoc, actionCoverPointHom_fst]
    exact (congrArg Subtype.val (snd_prodPoint
      ((affinePointEquiv (pgl2Variety (k := k))).symm
        ((pgl2Projection (k := k)).onPoints s)) x)).trans
      (congrArg Subtype.val (snd_prodPoint
        ((affinePointEquiv
          (slVariety k (Module.finrank k (Fin 2 -> k)))).symm s) x)).symm

private theorem pgl2ProjectiveRankTwoActionMorphism_projection_apply
    (s : Variety.Point
      (slVariety k (Module.finrank k (Fin 2 -> k))))
    (x : Point (projectiveRankTwo (k := k))) :
    pgl2ProjectiveRankTwoActionMorphism (k := k)
        (prodPoint
          ((affinePointEquiv (pgl2Variety (k := k))).symm
            ((pgl2Projection (k := k)).onPoints s)) x) =
      (sl2ProjectiveRankTwoMorphicAction (k := k)).toMulAction.smul s x := by
  apply Subtype.ext
  change (prodPoint
      ((affinePointEquiv (pgl2Variety (k := k))).symm
      ((pgl2Projection (k := k)).onPoints s)) x).1 ≫
        descendedActionHom (k := k) = _
  have hcover : actionCoverPointHom (k := k) s x ≫
        actionProjectionBaseChange (k := k) =
      (prodPoint
        ((affinePointEquiv (pgl2Variety (k := k))).symm
          ((pgl2Projection (k := k)).onPoints s)) x).1 := by
    exact actionCoverPointHom_fst (k := k) s x
  rw [← hcover]
  rw [Category.assoc, projectionBaseChange_descendedActionHom]
  unfold actionOnCover
  rw [← Category.assoc, actionCoverPointHom_toSL2P1]
  have h := congrArg Subtype.val
    ((sl2ProjectiveRankTwoMorphicAction (k := k)).actionMorphism_apply s x)
  exact h

/-- Evaluation of the descended action on a point lifted from `SL2` agrees
with the original projective-linear action. -/
public theorem pgl2ProjectiveLineActionMorphism_projection_apply
    (s : Variety.Point
      (slVariety k (Module.finrank k (Fin 2 -> k))))
    (x : Point (projectiveLine k)) :
    pgl2ProjectiveLineActionMorphism (k := k)
        (prodPoint
          ((affinePointEquiv (pgl2Variety (k := k))).symm
            ((pgl2Projection (k := k)).onPoints s)) x) =
      (sl2ProjectiveLineMorphicAction (k := k)).toMulAction.smul s x := by
  let hV := projectiveRankTwo_eq_projectiveLine (k := k)
  let x' : Point (projectiveRankTwo (k := k)) := hV.symm ▸ x
  have hx := pgl2ProjectiveRankTwoActionMorphism_projection_apply
    (k := k) s x'
  exact transportedAction_apply hV
    (pgl2ProjectiveRankTwoActionMorphism (k := k))
    (sl2ProjectiveRankTwoMorphicAction (k := k))
    ((affinePointEquiv (pgl2Variety (k := k))).symm
      ((pgl2Projection (k := k)).onPoints s)) s x hx

end Theory.AlgebraicGroup.Variety.Geometric
