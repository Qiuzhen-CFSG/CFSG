module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.FundamentalModules.OuterFunctions.NaturalModule.SpinComparisonExistence.LocalMaps
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.FrobeniusDifferential.TangentSpan.DenseParameters.Products

/-!
# Regular lifts of actual torus/root products to Spin

Multiply the supplied regular torus map and the scalar-reparametrized Clifford
root curves, in the same two lists used by `Geometry.rootProductMorphism`.
The resulting morphism is exactly the supplied point homomorphism after the
source product map. The proof uses `torus_lift` and `root_lift`; it makes no
assumption about uniqueness, density, or separability of these parameters.

This constructs the map upstairs for descent through the open root-product
chart in Steinberg (6.1)--(6.2), `refs/KGroup/GLS3/Chapter2St2.tex`, with target
the actual Clifford Spin carrier of GLS3 Theorem 1.10.7(d).
-/

public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
open Theory.AlgebraicGroup Triality.SimplyConnected
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
namespace SpinComparisonExistence

private def coordinateMorphism (S : Geometry K) (r : S.roots.Root) :
    Variety.Morphism S.rootProductParameterSpace (KPlus k) where
  toFun z := kPlusPoint (z.val (Sum.inr r))
  regular := by
    intro j
    refine ⟨MvPolynomial.X (Sum.inr r), ?_⟩
    intro z
    change z.val (Sum.inr r) = evalPolynomial z.val (MvPolynomial.X (Sum.inr r))
    exact (evalPolynomial_X _ _).symm

private def productMorphism {X Y : Variety k} [AlgebraicGroup Y] :
    List (Variety.Morphism X Y) → Variety.Morphism X Y
  | [] => Variety.Morphism.const X Y 1
  | f :: fs => (mulMorphism Y).comp (f.pair (productMorphism fs))

omit [IsAlgClosed k] [CharP k 2] in
private theorem productMorphism_apply {X Y : Variety k} [AlgebraicGroup Y]
    (fs : List (Variety.Morphism X Y)) (z : Variety.Point X) :
    (productMorphism fs).toFun z = (fs.map fun f => f.toFun z).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change f.toFun z * (productMorphism fs).toFun z = _
    rw [ih]
    rfl

private def RootwiseSpinHom.rootListMorphism {S : Geometry K}
    (C : RootwiseSpinHom k S) (rs : List S.roots.Root) :
    Variety.Morphism S.rootProductParameterSpace (groupVariety k) :=
  productMorphism (List.ofFn fun i : Fin rs.length =>
    (rootMorphism k S (rs.get i) (C.rootScale (rs.get i))).toVariety.comp
      (coordinateMorphism S (rs.get i)))

private theorem RootwiseSpinHom.rootListMorphism_apply {S : Geometry K}
    (C : RootwiseSpinHom k S) (rs : List S.roots.Root)
    (t : Variety.Point S.torus.carrierVariety) (c : S.roots.Root → k) :
    (C.rootListMorphism rs).toFun (S.rootProductParameterPoint t c) =
      C.pointHom (toralOrderedRootProduct S.roots S.rootParameter rs
        (fun i => c (rs.get i))) := by
  rw [RootwiseSpinHom.rootListMorphism, productMorphism_apply,
    toralOrderedRootProduct, map_list_prod, List.map_ofFn, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  have h := DFunLike.congr_fun (C.root_lift (rs.get i))
    (kPlusPoint (c (rs.get i)))
  exact h

/-- The regular Spin-valued product of the prescribed torus and root maps. -/
def RootwiseSpinHom.parameterMorphism {S : Geometry K}
    (C : RootwiseSpinHom k S) (positive negative : List S.roots.Root) :
    Variety.Morphism S.rootProductParameterSpace (groupVariety k) := by
  let : Finite S.roots.Root := Finite.of_equiv _ S.rootIndex.symm
  let t := (torusMorphism k S).toVariety.comp
    (Variety.Morphism.fst S.torus.carrierVariety (affineSpaceVariety k S.roots.Root))
  exact (mulMorphism (groupVariety k)).comp
    (((mulMorphism (groupVariety k)).comp
      (t.pair (C.rootListMorphism positive))).pair (C.rootListMorphism negative))

/-- The target product is the given point homomorphism on the source product. -/
theorem RootwiseSpinHom.parameterMorphism_apply {S : Geometry K}
    (C : RootwiseSpinHom k S) (positive negative : List S.roots.Root)
    (z : Variety.Point S.rootProductParameterSpace) :
    (C.parameterMorphism positive negative).toFun z =
      C.pointHom ((S.rootProductMorphism positive negative).toFun z) := by
  let : Finite S.roots.Root := Finite.of_equiv _ S.rootIndex.symm
  let t := (Variety.prodPointEquiv S.torus.carrierVariety
    (affineSpaceVariety k S.roots.Root) z).1
  let c : S.roots.Root → k := fun r => z.val (Sum.inr r)
  have hz : S.rootProductParameterPoint t c = z := by
    apply Variety.Point.ext
    funext i
    cases i <;> rfl
  rw [← hz, S.rootProductMorphism_apply, map_mul, map_mul]
  change (torusMorphism k S).onPoints t *
      (C.rootListMorphism positive).toFun (S.rootProductParameterPoint t c) *
      (C.rootListMorphism negative).toFun (S.rootProductParameterPoint t c) = _
  rw [C.rootListMorphism_apply, C.rootListMorphism_apply]
  have ht := DFunLike.congr_fun C.torus_lift t
  rw [ht]
  rfl

end SpinComparisonExistence
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.OuterFunctions
