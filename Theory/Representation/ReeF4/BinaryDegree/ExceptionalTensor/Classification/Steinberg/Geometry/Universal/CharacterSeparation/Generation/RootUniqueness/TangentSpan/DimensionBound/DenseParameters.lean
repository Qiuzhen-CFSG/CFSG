module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.Parameters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.Words
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.NormalizerCosets
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.NormalForms
public import Theory.AlgebraicGroup.Irreducible.Product

/-!
# Dense torus-and-root parameters for the literal F4 carrier

Two ordered lists of 24 root curves, a constant carrier point, and the literal
split torus define a regular map from the prescribed torus-and-48-root parameter
space. The root enumeration assigns disjoint coordinates to the two lists,
which may contain the same roots. The evaluation theorem identifies this map
with its actual group product.

Connectedness of the literal carrier makes it irreducible. Thus any finite
family of these cells covering its points has a member with dense image.
In characteristic two, the proved root transport and ordered root collection
give root-normalizer-root coverage. The finite normalizer representatives
modulo the literal split torus then give a covering family of these cells.
The final theorem discharges both algebraic inputs and constructs a dominant
parametrization over every algebraically closed field of characteristic two.
In particular it applies over the algebraic closure of a finite field, without
needing semisimplicity or maximality hypotheses for this concrete carrier.

This is the geometric part of the Bruhat argument in GLS3 §§1.11–1.12,
used toward Theorem 1.9.5(b). Source: `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section

namespace Theory.AlgebraicGroup.F4Chevalley.DenseParameters

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable section

local instance : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
  (splitTorus (k := k)).carrierAlgebraicGroup

private def parameterSlots : (Fin 24 ⊕ Fin 24) ≃ Root :=
  finSumFinEquiv.trans ReeF4.Cartan.FieldSeparation.TraceValues.rootEquiv

/-- Pack two independent 24-coordinate tuples and an actual torus point into
the literal 48-root parameter space. -/
def parameters (s : Variety.Point (splitTorus (k := k)).carrierVariety)
    (a b : Fin 24 → k) : Variety.Point (concreteRootParameterSpace (k := k)) :=
  (Variety.prodPointEquiv _ _).symm
    (s, affineSpacePoint fun r => Sum.elim a b (parameterSlots.symm r.down))

private def affineRootCoordinate (r : Root) :
    Variety.Morphism (affineSpaceVariety k (ULift.{u} Root)) (KPlus k) where
  toFun x := kPlusPoint (x.val (ULift.up r))
  regular := by
    intro c
    refine ⟨MvPolynomial.X (ULift.up r), ?_⟩
    intro x
    rw [show c = PUnit.unit by rfl]
    change x.val (ULift.up r) = evalPolynomial x.val (MvPolynomial.X (ULift.up r))
    rw [evalPolynomial_X]

private def productMorphism {X : Variety k}
    (fs : List (Variety.Morphism X (Carrier (k := k)))) :
    Variety.Morphism X (Carrier (k := k)) :=
  match fs with
  | [] => Variety.Morphism.const _ _ 1
  | f :: fs => (mulMorphism _).comp (f.pair (productMorphism fs))

private theorem productMorphism_apply {X : Variety k}
    (fs : List (Variety.Morphism X (Carrier (k := k)))) (x : Variety.Point X) :
    (productMorphism fs).toFun x = (fs.map fun f => f.toFun x).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp [productMorphism, Variety.Morphism.comp, Variety.Morphism.pair,
      Variety.prodPointEquiv, mulMorphism, ih]

private def rootCoordinate (r slot : Root) :
    Variety.Morphism (concreteRootParameterSpace (k := k)) (Carrier (k := k)) :=
  (rootMorphism r).toVariety.comp
    ((affineRootCoordinate slot).comp (Variety.Morphism.snd _ _))

private def rootProductMorphism (p : Fin 24 → Root) (side : Bool) :
    Variety.Morphism (concreteRootParameterSpace (k := k)) (Carrier (k := k)) :=
  productMorphism (List.ofFn fun i =>
    rootCoordinate (p i) (parameterSlots (if side then Sum.inr i else Sum.inl i)))

private theorem rootCoordinate_parameters (r slot : Root)
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) (a b : Fin 24 → k) :
    (rootCoordinate r slot).toFun (parameters s a b) =
      rootElement r (Sum.elim a b (parameterSlots.symm slot)) := rfl

private theorem rootProductMorphism_parameters (p : Fin 24 → Root) (side : Bool)
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) (a b : Fin 24 → k) :
    (rootProductMorphism p side).toFun (parameters s a b) =
      rootProduct p (if side then b else a) := by
  rw [rootProductMorphism, productMorphism_apply, List.map_ofFn]
  unfold rootProduct
  apply congrArg (fun f : Fin 24 → Variety.Point (Carrier (k := k)) => (List.ofFn f).prod)
  funext i
  dsimp only [Function.comp_def]
  rw [rootCoordinate_parameters]
  cases side <;> simp

private def torusMorphism :
    Variety.Morphism (concreteRootParameterSpace (k := k)) (Carrier (k := k)) :=
  (splitTorus (k := k)).inclusion.toVariety.comp (Variety.Morphism.fst _ _)

/-- A regular cell map: an ordered root product, a constant middle factor,
the actual split torus, and another ordered root product. -/
def cellMorphism (p q : Fin 24 → Root) (w : Variety.Point (Carrier (k := k))) :
    Variety.Morphism (concreteRootParameterSpace (k := k)) (Carrier (k := k)) :=
  productMorphism [rootProductMorphism p false, Variety.Morphism.const _ _ w,
    torusMorphism, rootProductMorphism q true]

/-- The cell morphism evaluates to its literal four-factor group product. -/
theorem cellMorphism_parameters (p q : Fin 24 → Root)
    (w : Variety.Point (Carrier (k := k)))
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) (a b : Fin 24 → k) :
    (cellMorphism p q w).toFun (parameters s a b) =
      rootProduct p a * w * (splitTorus (k := k)).inclusion.onPoints s *
        rootProduct q b := by
  rw [cellMorphism, productMorphism_apply]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [rootProductMorphism_parameters, rootProductMorphism_parameters]
  change rootProduct p a *
    (w * ((splitTorus (k := k)).inclusion.onPoints s * (rootProduct q b * 1))) = _
  simp only [mul_one, mul_assoc]

/-- One member of a finite covering family of morphisms has dense image in
the connected literal F4 carrier. -/
theorem exists_dense_of_finite_cover {ι : Type*} [Finite ι]
    (f : ι → Variety.Morphism (concreteRootParameterSpace (k := k)) (Carrier (k := k)))
    (hcover : ∀ g, ∃ i x, (f i).toFun x = g) :
    ∃ i, Dense (Set.range (f i).toFun) := by
  classical
  let := Fintype.ofFinite ι
  let t : Finset (Set (Variety.Point (Carrier (k := k)))) :=
    Finset.univ.image fun i => closure (Set.range (f i).toFun)
  have hclosed : ∀ Z ∈ t, IsClosed Z := by
    intro Z hZ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hZ
    exact isClosed_closure
  have hcovered : Set.univ ⊆ ⋃₀ (t : Set (Set (Variety.Point (Carrier (k := k))))) := by
    intro g _
    obtain ⟨i, x, rfl⟩ := hcover g
    exact Set.mem_sUnion_of_mem
      (subset_closure (show (f i).toFun x ∈ Set.range (f i).toFun from ⟨x, rfl⟩))
      (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hirr := connectedAlgebraicGroup_irreducible (Carrier (k := k)) carrier_isConnected
  obtain ⟨Z, hZ, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hirr t hclosed hcovered
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hZ
  exact ⟨i, dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset hsub)⟩

/-- Ordered root-word coverage and finitely many normalizer representatives
modulo the actual torus give a dominant morphism from the required parameter
space. Both algebraic normal-form statements remain explicit inputs. -/
theorem exists_dense_of_normal_forms
    (p q : Fin 24 → Root)
    (hwords : ∀ g : Variety.Point (Carrier (k := k)),
      ∃ (a b : Fin 24 → k) (n : Variety.Point (Carrier (k := k))),
        n ∈ normalizerWords (k := k) ∧ g = rootProduct p a * n * rootProduct q b)
    (hnormalizer : ∃ W : Finset (Variety.Point (Carrier (k := k))),
      ∀ n ∈ normalizerWords (k := k), ∃ w ∈ W,
        ∃ s : Variety.Point (splitTorus (k := k)).carrierVariety,
          n = w * (splitTorus (k := k)).inclusion.onPoints s) :
    ∃ f : Variety.Morphism (concreteRootParameterSpace (k := k)) (Carrier (k := k)),
      Dense (Set.range f.toFun) := by
  obtain ⟨W, hW⟩ := hnormalizer
  obtain ⟨w, hw⟩ := exists_dense_of_finite_cover
    (fun w : W => cellMorphism p q w.val) (by
      intro g
      obtain ⟨a, b, n, hn, hg⟩ := hwords g
      obtain ⟨w, hw, s, hnw⟩ := hW n hn
      refine ⟨⟨w, hw⟩, parameters s a b, ?_⟩
      rw [cellMorphism_parameters, hg, hnw, mul_assoc (rootProduct p a) w])
  exact ⟨cellMorphism p q w.val, hw⟩

end
end Theory.AlgebraicGroup.F4Chevalley.DenseParameters

namespace Theory.AlgebraicGroup.F4Chevalley

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

/-- The literal split torus and 48 affine root coordinates dominantly
parametrize the closed F4 carrier in characteristic two. This applies in
particular over the algebraic closure of every finite characteristic-two field;
no additional geometric hypotheses are needed. -/
theorem exists_concrete_dense_root_parameters :
    ∃ f : Variety.Morphism (concreteRootParameterSpace (k := k)) (Carrier (k := k)),
      Dense (Set.range f.toFun) := by
  obtain ⟨p, q, hwords⟩ := DenseParameters.exists_ordered_normal_forms_of_transport
    (k := k) (fun _ hn => DenseParameters.normalizerWords_rootTransport hn)
  exact DenseParameters.exists_dense_of_normal_forms p q hwords
    DenseParameters.normalizerWords_finite_torus_cosets

end Theory.AlgebraicGroup.F4Chevalley
