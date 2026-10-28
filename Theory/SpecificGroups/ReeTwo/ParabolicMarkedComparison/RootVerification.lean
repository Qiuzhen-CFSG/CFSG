module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.Words
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.BinaryRelations
public import Theory.SpecificGroups.ReeTwo.CorePresentation
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.SimpleComparison
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.TransportComparison

/-!
# Source root identities in the actual binary Ree group

The existing comparison of the eight signed simple curves gives an injective
matrix realization after reindexing the Chevalley basis. Root 1 is its first
quartet word. Each of the ten core roots is recovered from the marked Parrott
generators and root 1, so the packed binary checks transfer to the literal
ambient roots. This proves all premises of the universal local map without
assuming a parabolic isomorphism or a structural conclusion.

The private scalar-extension and Weyl-route arguments follow the existing
`Realization.TransportComparison` proofs, retaining their multiplication
and commutator conventions.

Sources: Shinoda (1975), pp.81–82; Parrott (1972), p.683;
Aschbacher (1982), Section 3; Aschbacher–Smith 14.2.21, printed p.989.
-/

public section
noncomputable section
namespace ReeTwo.ParabolicMarkedComparison
namespace RootVerification
open ReeF4 ReeF4.DerivedTits.Realization
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open ReeF4.DerivedTits.Realization.TransportComparison
open ReeF4.Parabolics.Binary.FixedGeometry
open Tits.ExceptionalParabolics

private def renumber (e : F4Chevalley.BasisIndex ≃ Fin 52) :
    MatrixUnits 0 →* (Matrix (Fin 52) (Fin 52) (CoefficientField 0))ˣ :=
  Units.map (Matrix.reindexRingEquiv (CoefficientField 0) e).toMonoidHom

private def extendScalars : Products.BinaryUnit →*
    (Matrix (Fin 52) (Fin 52) (CoefficientField 0))ˣ :=
  Units.map binaryScalar.mapMatrix.toMonoidHom

private theorem compare_simple (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (b : Bool) (i : Fin 4) :
    renumber e (F4Chevalley.rootCurve (signedSimpleRoot b i) 1) =
      extendScalars (ReeF4.DerivedTits.Realization.Binary.simpleAssignment b i) :=
  Units.ext (h b i)

private theorem compare_tits (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (w : List (Fin 4)) :
    renumber e (WordRelations.titsUnit (w.map typeF4RootPairing_baseEquiv)) =
      extendScalars (Products.weylWord w) := by
  let := typeF4RootPairing.indexNeg
  induction w with
  | nil => simp [Products.weylWord]
  | cons i w ih =>
    have hp := compare_simple e h false i
    have hn := compare_simple e h true i
    change renumber e (F4Chevalley.rootCurve (typeF4SimpleRootIndex i) 1) = _ at hp
    change renumber e (F4Chevalley.rootCurve (-typeF4SimpleRootIndex i) 1) = _ at hn
    simp only [List.map_cons, WordRelations.titsUnit_cons,
      typeF4RootPairing_baseEquiv_val, CharTwo.neg_eq, map_mul, hp, hn, ih]
    simp [Products.weylWord, Products.weyl, map_mul]

private theorem compare_root (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (i : Fin 24) :
    renumber e (F4Chevalley.rootCurve (positiveRoot i) 1) =
      extendScalars (Products.root i) := by
  have hp := compare_simple e h false (routeSimple i)
  change renumber e (F4Chevalley.rootCurve (typeF4SimpleRootIndex (routeSimple i)) 1) = _ at hp
  rw [rootCurve_route]
  simp only [map_mul, map_inv, compare_tits e h, hp]
  simp only [Products.root, Products.transported, map_mul, map_inv]

private theorem compare_quartet (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (i : Fin 4) :
    renumber e (quartetElement i).val = extendScalars (Products.quartet i) := by
  rw [quartetElement_eq]
  change renumber e (F4Chevalley.rootCurve (quartetRoots i 0) 1 *
    F4Chevalley.rootCurve (quartetRoots i 1) 1 *
    F4Chevalley.rootCurve (quartetRoots i 3) 1) = _
  simp only [TransportComparison.quartetRoots_eq, map_mul, compare_root e h,
    Products.quartet]

private def numbered (e : F4Chevalley.BasisIndex ≃ Fin 52) :
    Model 0 →* (Matrix (Fin 52) (Fin 52) (CoefficientField 0))ˣ :=
  (renumber e).comp ((SplitGroup 0).subtype.comp (toSplitGroup 0))

private theorem numbered_injective (e : F4Chevalley.BasisIndex ≃ Fin 52) :
    Function.Injective (numbered e) := by
  intro x y he
  apply toSplitGroup_injective 0
  apply Subtype.ext
  apply Units.ext
  apply (Matrix.reindexRingEquiv (CoefficientField 0) e).injective
  exact congrArg Units.val he

private theorem compare_generator (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (i : Tits.ParrottGenerator) :
    numbered e (FullRee.atlasEmbedding (Tits.atlas1600ParrottAssignment i)) =
      extendScalars (ReeF4.DerivedTits.Realization.Binary.assignment i) := by
  change renumber e ((toSplitGroup 0 (FullRee.atlasEmbedding _)).val) = _
  rw [FullRee.atlasEmbedding_generator_matrix]
  exact Units.ext (matrixComparison_of_simpleMatrixComparison e h i)

private theorem compare_one (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) :
    numbered e Ambient.rootOne = extendScalars Binary.rootOne := by
  change renumber e ((toSplitGroup 0 Ambient.rootOne).val) = _
  rw [toSplitGroup_apply]
  exact compare_quartet e h 0

private theorem compare_weyl (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) :
    numbered e Ambient.weyl = extendScalars Binary.weyl := by
  rw [← show FullRee.atlasEmbedding (Tits.atlas1600ParrottAssignment .r1) = Ambient.weyl from
    Ambient.atlas_generator .r1]
  exact compare_generator e h .r1

private def recoveredRoot (i : CoreRoot) : Model 0 :=
  let s := Ambient.rootOne
  let g := fun j => FullRee.atlasEmbedding (Tits.atlas1600ParrottAssignment j)
  ![g .s8, g .s7 * s, s⁻¹ * g .s5, s⁻¹ * g .s3, g .s2,
    (g .s7 * s) ^ 2, g .s6, g .s4, (s⁻¹ * g .s3) ^ 2, (s⁻¹ * g .s5) ^ 2] i

private theorem root_recovered (i : CoreRoot) : Ambient.root i = recoveredRoot i := by
  fin_cases i <;> simp [recoveredRoot, Ambient.atlas_generator, Ambient.parrottWord,
    Ambient.rootOne, Ambient.root, mul_assoc]

private theorem compare_core (e : F4Chevalley.BasisIndex ≃ Fin 52)
    (h : SimpleMatrixComparison e) (i : CoreRoot) :
    numbered e (Ambient.root i) = extendScalars (Binary.root i) := by
  rw [root_recovered]
  fin_cases i <;> simp [recoveredRoot, Binary.root, compare_generator e h, compare_one e h]

private theorem transport_relations {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* K) (g : H →* K) (hf : Function.Injective f)
    (x : CoreRoot → G) (y : CoreRoot → H) (s w : G) (t v : H)
    (hx : ∀ i, f (x i) = g (y i)) (hs : f s = g t) (hw : f w = g v)
    (hc : CoreRelations y) (hr : RootOneRelations t y)
    (hv : ∀ i, v * y i * v⁻¹ = y (weylRoot i))
    (h5 : ((t⁻¹) ^ 2 * v) ^ 5 = 1) (h4 : (t⁻¹) ^ 4 = 1)
    (ha : t⁻¹ * ((t⁻¹) ^ 2 * v) * (t⁻¹)⁻¹ = ((t⁻¹) ^ 2 * v) ^ 2) :
    CoreRelations x ∧ RootOneRelations s x ∧
      (∀ i, w * x i * w⁻¹ = x (weylRoot i)) ∧
      ((s⁻¹) ^ 2 * w) ^ 5 = 1 ∧ (s⁻¹) ^ 4 = 1 ∧
      s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2 := by
  have hword (l : List CoreRoot) : f (rootWord x l) = g (rootWord y l) := by
    simp only [map_rootWord, hx]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply hf
    simpa only [map_mul, hx, hword] using congrArg g (hc.square i)
  · intro i j hij
    apply hf
    simpa only [map_rightComm, hx, hword] using congrArg g (hc.commutator i j hij)
  · intro i
    apply hf
    simpa only [map_rightComm, hs, hx, hword] using congrArg g (hr i)
  · intro i
    apply hf
    simpa only [map_mul, map_inv, hx, hw] using congrArg g (hv i)
  · apply hf
    simpa only [map_mul, map_inv, map_pow, map_one, hs, hw] using congrArg g h5
  · apply hf
    simpa only [map_inv, map_pow, map_one, hs] using congrArg g h4
  · apply hf
    simpa only [map_mul, map_inv, map_pow, hs, hw] using congrArg g ha

/-- The actual root identities follow from the existing canonical matrix comparison. -/
theorem relations : Ambient.Relations := by
  obtain ⟨e, he⟩ := exists_simpleMatrixComparison
  obtain ⟨hc, hr, hw, h5, h4, ha⟩ := transport_relations
    (numbered e) extendScalars (numbered_injective e)
    Ambient.root Binary.root Ambient.rootOne Ambient.weyl Binary.rootOne Binary.weyl
    (compare_core e he) (compare_one e he) (compare_weyl e he)
    Binary.core_relations Binary.root_one_relations Binary.weyl_root
    Binary.five Binary.four Binary.action
  exact ⟨hc, hr, hw, h5, h4, ha⟩

end RootVerification
end ReeTwo.ParabolicMarkedComparison
