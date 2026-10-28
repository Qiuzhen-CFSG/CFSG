module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.DeterminantalLocus.Equations
public import Theory.AlgebraicGroup.Variety.ClosedLocus

/-!
# Reduction to bihomogeneous zero loci on two projective factors

Scheme morphisms project the recursive finite product to each of its factors.
Pulling a bihomogeneous equation back along two such morphisms and intersecting
all minors gives exactly the simultaneous wedge rank conditions. The point
comparison uses the published rational-point equivalence in arbitrary bases.

The geometric premise `BihomogeneousZeroLoci` is explicit here and is not proved
by this module. Thus the last theorem is a conditional assembly lemma, not a
closedness theorem for flags. Its remaining premise asks for genuine closed
subsets of the scheme fiber product of two projective spaces. No product
topology on their underlying spaces is substituted. Diagonal pairs use the
same projection twice; empty flag indices give the top closed subset of `Spec k`.

Source: the projective flag variety used in Borel, *Linear Algebraic Groups*,
§11.1, and the standard affine-chart description of biprojective equations.
-/

@[expose] public noncomputable section
open scoped ExteriorAlgebra LinearAlgebra.Projectivization
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry.DeterminantalLocus
open Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The projection to any factor of the actual recursive scheme product. -/
def finProductProjection : (n : ℕ) → (X : Fin n → Variety.Geometric k) →
    (i : Fin n) → Variety.Geometric.Morphism (finProduct n X) (X i)
  | 0, _, i => Fin.elim0 i
  | n+1, X, i => Fin.cases (fst (X 0) (finProduct n (fun j => X j.succ)))
      (fun j => Variety.Geometric.Morphism.comp (snd (X 0) (finProduct n (fun l => X l.succ)))
        (finProductProjection n (fun l => X l.succ) j)) i

/-- On rational points the scheme projection is the corresponding tuple projection. -/
theorem finProductProjection_apply (n : ℕ) (X : Fin n → Variety.Geometric k)
    (i : Fin n) (x : Point (finProduct n X)) :
    finProductProjection n X i x = finProductPointEquiv n X x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (Variety.Geometric.Morphism.comp (snd _ _) (finProductProjection n _ j)) x = _
      erw [Variety.Geometric.Morphism.comp_apply_point]
      exact ih _ _ _

/-- A projective rational point is represented by the coordinates of its exterior-line representative. -/
theorem projectivePoint_eq_coordinates
    {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (x : Point (projectiveSpace k E)) :
    x = projectivePointOfVector (b.equivFun (projectiveSpacePointEquivOf b x).rep)
      (b.equivFun.map_ne_zero_iff.mpr (projectiveSpacePointEquivOf b x).rep_nonzero) := by
  apply (projectiveSpacePointEquivOf b).injective
  exact ((projectiveSpacePointEquivOf_projectivePointOfVector b _
    (projectiveSpacePointEquivOf b x).rep_nonzero).trans
      (projectiveSpacePointEquivOf b x).mk_rep).symm

/-- The geometric prerequisite: a bihomogeneous polynomial has its prescribed zero locus on the scheme product. This is a proposition to be proved, not an instance or an assumed source theorem. -/
def BihomogeneousZeroLoci (k : Type u) [Field k] [IsAlgClosed k] : Prop :=
  ∀ (m n : ℕ) (P : MvPolynomial (Fin m ⊕ Fin n) k) (degree : ℕ × ℕ),
    P.IsWeightedHomogeneous blockWeight degree →
    ∃ Z : Closeds (prod (projectiveSpaceByCoordinates k (Fin m))
      (projectiveSpaceByCoordinates k (Fin n))).toScheme,
      ∀ (a : Fin m → k) (ha : a ≠ 0) (b : Fin n → k) (hb : b ≠ 0),
        (prodPoint (projectivePointOfVector a ha)
          (projectivePointOfVector b hb)).val (IsLocalRing.closedPoint k) ∈ Z ↔
          MvPolynomial.eval (Sum.elim a b) P = 0

/-- Conditional pullback of a bihomogeneous zero locus along two actual scheme morphisms. -/
theorem exists_polynomial_pullback_locus
    (H : BihomogeneousZeroLoci k)
    {X : Variety.Geometric k}
    {E F : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    [AddCommGroup F] [Module k F] [FiniteDimensional k F]
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (c : Module.Basis (Fin (Module.finrank k F)) k F)
    (f : Variety.Geometric.Morphism X (projectiveSpace k E)) (g : Variety.Geometric.Morphism X (projectiveSpace k F))
    (P : MvPolynomial (Fin (Module.finrank k E) ⊕ Fin (Module.finrank k F)) k)
    (degree : ℕ × ℕ) (hP : P.IsWeightedHomogeneous blockWeight degree) :
    ∃ Z : Closeds X.toScheme, ∀ x : Point X,
      x.val (IsLocalRing.closedPoint k) ∈ Z ↔
        MvPolynomial.eval (Sum.elim (b.equivFun (projectiveSpacePointEquivOf b (f x)).rep)
          (c.equivFun (projectiveSpacePointEquivOf c (g x)).rep)) P = 0 := by
  obtain ⟨Z, hZ⟩ := H (Module.finrank k E) (Module.finrank k F) P degree hP
  let h := Variety.Geometric.Morphism.prodLift f g
  let W : Closeds (prod (projectiveSpace k E) (projectiveSpace k F)).toScheme := Z
  refine ⟨⟨h.hom ⁻¹' (W : Set _), W.isClosed.preimage h.hom.continuous⟩, ?_⟩
  intro x
  change h.hom (x.val (IsLocalRing.closedPoint k)) ∈ Z ↔ _
  have hx : h x = prodPoint (f x) (g x) := by
    apply (prodPointEquiv _ _).injective
    rw [Variety.Geometric.Morphism.prodPointEquiv_prodLift_apply]
    exact ((prodPointEquiv _ _).apply_symm_apply (f x, g x)).symm
  change (h x).val (IsLocalRing.closedPoint k) ∈ Z ↔ _
  rw [hx]
  have hz := hZ (b.equivFun (projectiveSpacePointEquivOf b (f x)).rep)
      (b.equivFun.map_ne_zero_iff.mpr (projectiveSpacePointEquivOf b (f x)).rep_nonzero)
      (c.equivFun (projectiveSpacePointEquivOf c (g x)).rep)
      (c.equivFun.map_ne_zero_iff.mpr (projectiveSpacePointEquivOf c (g x)).rep_nonzero)
  rw [← projectivePoint_eq_coordinates b (f x),
    ← projectivePoint_eq_coordinates c (g x)] at hz
  convert! hz using 1


variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Given bihomogeneous zero loci, the minors cut out a stacked wedge rank bound. -/
theorem exists_stacked_rank_locus
    (H : BihomogeneousZeroLoci k) {X : Variety.Geometric k}
    {d e : ℕ}
    (bd : Module.Basis (Fin (Module.finrank k (⋀[k]^d V))) k (⋀[k]^d V))
    (be : Module.Basis (Fin (Module.finrank k (⋀[k]^e V))) k (⋀[k]^e V))
    (f : Variety.Geometric.Morphism X (projectiveSpace k (⋀[k]^d V)))
    (g : Variety.Geometric.Morphism X (projectiveSpace k (⋀[k]^e V))) (t : ℕ) :
    ∃ Z : Closeds X.toScheme, ∀ x : Point X,
      x.val (IsLocalRing.closedPoint k) ∈ Z ↔
        Module.finrank k (LinearMap.range
          ((wedgeVectorMap (projectiveSpacePointEquivOf bd (f x)).rep).prod
            (wedgeVectorMap (projectiveSpacePointEquivOf be (g x)).rep))) ≤ t := by
  classical
  let bv := Module.finBasis k V
  let cd := Module.finBasis k (⋀[k]^(d+1) V)
  let ce := Module.finBasis k (⋀[k]^(e+1) V)
  have hloc := fun
      (r : Fin (t+1) → Fin (Module.finrank k (⋀[k]^(d+1) V)) ⊕
        Fin (Module.finrank k (⋀[k]^(e+1) V)))
      (c : Fin (t+1) → Fin (Module.finrank k V)) =>
    exists_polynomial_pullback_locus H bd be f g
      (wedgeMinorPolynomial bv bd be cd ce r c) (∑ i, blockWeight (r i))
      (wedgeMinorPolynomial_homogeneous bv bd be cd ce r c)
  choose Z hZ using hloc
  refine ⟨⨅ r, ⨅ c, Z r c, ?_⟩
  intro x
  rw [stacked_rank_iff_minorEquations bv bd be cd ce]
  simp only [Closeds.mem_iInf, hZ]

/-- Conditional assembly of all flag rank equations. The geometric premise must be discharged before claiming the flag determinantal locus exists. -/
theorem exists_flagRankConditions_locus_of_bihomogeneous
    (H : BihomogeneousZeroLoci k) (b : CoordinateBases (k := k) V) :
    ∃ Z : Closeds (flagAmbient (k := k) V).toScheme,
      ∀ x : Point (flagAmbient (k := k) V),
        x.val (IsLocalRing.closedPoint k) ∈ Z ↔ FlagRankConditions (ambientPointEquiv b x) := by
  classical
  let X := fun i : Fin (Module.finrank k V) => projectiveSpace k (⋀[k]^(i : ℕ) V)
  let f : (i : Fin (Module.finrank k V)) →
      Variety.Geometric.Morphism (flagAmbient (k := k) V) (projectiveSpace k (⋀[k]^(i : ℕ) V)) :=
    finProductProjection (Module.finrank k V) X
  have hf (i : Fin (Module.finrank k V)) (x : Point (flagAmbient (k := k) V)) :
      projectiveSpacePointEquivOf (b i) (f i x) = ambientPointEquiv b x i := by
    exact congrArg (projectiveSpacePointEquivOf (b i))
      (finProductProjection_apply (Module.finrank k V) X i x)
  have hloc := fun i j : Fin (Module.finrank k V) =>
    exists_stacked_rank_locus H (b i) (b j) (f i) (f j) (Module.finrank k V - i)
  choose Z hZ using hloc
  refine ⟨⨅ i, ⨅ j, ⨅ (_ : i ≤ j), Z i j, ?_⟩
  intro x
  rw [flagRankConditions_iff_stacked_rank]
  simp only [Closeds.mem_iInf]
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun _ => ?_
  convert! hZ i j x using 1
  rw [hf i x, hf j x]

end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry.DeterminantalLocus
