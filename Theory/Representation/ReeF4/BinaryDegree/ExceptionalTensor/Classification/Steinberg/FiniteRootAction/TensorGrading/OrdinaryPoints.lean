module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.FilteredOperators
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.TensorStep

/-!
# The actual ordinary Frobenius action and coordinate root expansions

The canonical tensor action extends to the literal algebraic point group by
ordinary Frobenius pullback in each factor. Factorwise insertion identifies
its root action with a product of genuine rational root polynomials. These
are the operators used on restriction to the original finite Ree model.

Source: Steinberg (1963), Section 12.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open Theory.AlgebraicGroup
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- The canonical tensor of endomorphisms preserves identity and composition. -/
@[expose] def tensorMapHom (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n : ℕ) :
    (∀ i : ℕ, Module.End F (basicFactor m B i).Space) →* Module.End F (basicTensorSpace m B n) where
  toFun := fun T => tensorMap m B T n
  map_one' := tensorMap_one m B n
  map_mul' S T := tensorMap_mul m B S T n

/-- Tensoring all coordinates equals their ordered product of insertions. -/
theorem tensorMap_eq_coordinateProduct (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (T : ∀ i : ℕ, Module.End F (basicFactor m B i).Space) (n : ℕ) :
    tensorMap m B T n = ((List.range n).map (fun i => coordinateMap m B n i (T i))).prod := by
  let h := tensorMapHom m B n
  change h T = _
  rw [show (fun i => coordinateMap m B n i (T i)) =
    h ∘ (fun i => Pi.mulSingle i (T i)) from rfl, ← List.map_map, ← map_list_prod]
  apply tensorMap_congr
  intro j hj
  have he := map_list_prod (Pi.evalMonoidHom (fun i => Module.End F (basicFactor m B i).Space) j)
    ((List.range n).map (fun i => Pi.mulSingle i (T i)))
  rw [List.map_map] at he
  change (((List.range n).map fun i => Pi.mulSingle i (T i)).prod j) = _ at he
  rw [he, List.prod_map_eq_pow_single j]
  · simp only [Function.comp_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same,
      List.count_range, hj, if_pos, pow_one]
  · intro i hij _
    exact Pi.mulSingle_eq_of_ne (M := fun i => Module.End F (basicFactor m B i).Space) hij.symm (T i)

variable [CharP F 2]

/-- The ordinary Frobenius action on algebraic points, on the canonical carrier. -/
@[expose] def ordinaryPointAction (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (n : ℕ) : Representation F (PointGroup F) (basicTensorSpace m B n) :=
  (tensorMapHom m B n).comp
    (MonoidHom.pi fun i => ((basicFactor m B i).restrict (Geometry.frobeniusEnd ^ i)).ρ)

/-- Restriction is the previously fixed finite Ree action. -/
theorem ordinaryPointAction_restrict (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (f : CoefficientField m →+* F) (n : ℕ) :
    (ordinaryPointAction m B n).comp (modelEmbedding f) = ordinaryAction m B f n := by
  induction n with
  | zero => apply MonoidHom.ext; intro g; rfl
  | succ n ih =>
    apply MonoidHom.ext
    intro g
    change TensorProduct.map (((ordinaryPointAction m B n).comp (modelEmbedding f)) g)
      (((basicFactor m B n).restrict ((Geometry.frobeniusEnd ^ n).comp (modelEmbedding f))).ρ g) = _
    rw [ih]
    rfl

private theorem frobenius_pow_root (i : ℕ) (r : F4Chevalley.Root) (t : F) :
    (Geometry.frobeniusEnd ^ i) (algebraicRootElement r t) =
      algebraicRootElement r (t ^ (2 ^ i)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ']
    change Geometry.frobeniusEnd ((Geometry.frobeniusEnd ^ i) (algebraicRootElement r t)) = _
    rw [ih, Geometry.frobeniusEnd_root, ← pow_mul, pow_succ]

/-- The literal ordinary point action of a root is the ordered coordinate product. -/
theorem ordinaryPointAction_root (m : ℕ) (B : ZMod (2 * m + 1) → AlgebraicFactor F)
    (n : ℕ) (r : F4Chevalley.Root) (t : F) :
    ordinaryPointAction m B n (algebraicRootElement r t) =
      ((List.range n).map fun i => coordinateMap m B n i
        ((basicFactor m B i).action.action (algebraicRootElement r (t ^ (2 ^ i))))).prod := by
  change tensorMap m B (fun i =>
    ((basicFactor m B i).action.action ((Geometry.frobeniusEnd ^ i) (algebraicRootElement r t))).val) n = _
  simp only [frobenius_pow_root]
  exact tensorMap_eq_coordinateProduct m B _ n

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
