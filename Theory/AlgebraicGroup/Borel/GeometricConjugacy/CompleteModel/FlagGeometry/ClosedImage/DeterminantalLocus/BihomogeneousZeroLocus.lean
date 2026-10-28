module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.DeterminantalLocus.Assembly
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.DeterminantalLocus.BihomogeneousZeroLocus.ChartEvaluation
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.DeterminantalLocus.BihomogeneousZeroLocus.Scaling
/-!
# Closed zero loci of bihomogeneous equations

On the scheme fiber product of two projective spaces, intersect the inverse
images of two standard coordinate charts. Pulling back their normalized
coordinates gives sections on this open subscheme, in which any polynomial can
be evaluated. The complement of the union of the resulting nonvanishing opens
is a closed subset of the actual scheme product.

At a rational point, the chart sections evaluate to the original coordinates
divided by the selected nonzero coordinates. Separate homogeneity in the two
blocks makes vanishing invariant under this normalization. This proves the
exact `BihomogeneousZeroLoci` contract consumed by `DeterminantalLocus.Assembly`,
including zero coordinate counts, zero bidegrees, constants, and the zero
polynomial. No product topology on the underlying projective spaces is used.

Source: the projective flag variety in Borel, *Linear Algebraic Groups*, §11.1,
and its standard construction by bihomogeneous equations in projective factors.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Theory.AlgebraicGroup.Variety.Geometric
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry.DeterminantalLocus
open BihomogeneousCharts
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {m n : ℕ}

private abbrev biprojective (k : Type u) [Field k] [IsAlgClosed k] (m n : ℕ) :=
  prod (projectiveSpaceByCoordinates k (Fin m)) (projectiveSpaceByCoordinates k (Fin n))

private abbrev leftProjection :=
  (fst (projectiveSpaceByCoordinates k (Fin m)) (projectiveSpaceByCoordinates k (Fin n))).hom
private abbrev rightProjection :=
  (snd (projectiveSpaceByCoordinates k (Fin m)) (projectiveSpaceByCoordinates k (Fin n))).hom

private def pairChart (i : Fin m) (j : Fin n) : (biprojective k m n).toScheme.Opens :=
  leftProjection ⁻¹ᵁ Proj.basicOpen (projectiveGrading k (Fin m)) (MvPolynomial.X i) ⊓
    rightProjection ⁻¹ᵁ Proj.basicOpen (projectiveGrading k (Fin n)) (MvPolynomial.X j)

private def leftChartMap (i : Fin m) (j : Fin n) :
    (pairChart (k := k) i j).toScheme ⟶ Spec (.of (ChartRing (k := k) i)) :=
  leftProjection.resLE _ _ inf_le_left ≫
    (Proj.basicOpenIsoSpec (projectiveGrading k (Fin m)) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).hom

private def rightChartMap (i : Fin m) (j : Fin n) :
    (pairChart (k := k) i j).toScheme ⟶ Spec (.of (ChartRing (k := k) j)) :=
  rightProjection.resLE _ _ inf_le_right ≫
    (Proj.basicOpenIsoSpec (projectiveGrading k (Fin n)) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X k j) Nat.zero_lt_one).hom

private theorem leftChartMap_fac (i : Fin m) (j : Fin n) :
    leftChartMap (k := k) i j ≫ inclusion i = (pairChart i j).ι ≫ leftProjection := by
  simp only [leftChartMap, inclusion, Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc]
  exact Scheme.Hom.resLE_comp_ι _ _

private theorem rightChartMap_fac (i : Fin m) (j : Fin n) :
    rightChartMap (k := k) i j ≫ inclusion j = (pairChart i j).ι ≫ rightProjection := by
  simp only [rightChartMap, inclusion, Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc]
  exact Scheme.Hom.resLE_comp_ι _ _

private def chartCoefficients (i : Fin m) (j : Fin n) :
    k →+* Γ((pairChart (k := k) i j).toScheme, ⊤) :=
  ((pairChart i j).ι ≫ (biprojective k m n).structureMap).appTop.hom.comp
    (Scheme.ΓSpecIso (.of k)).inv.hom

private def chartVariables (i : Fin m) (j : Fin n) :
    Fin m ⊕ Fin n → Γ((pairChart (k := k) i j).toScheme, ⊤) :=
  Sum.elim
    (fun l => (leftChartMap i j).appTop ((Scheme.ΓSpecIso (.of (ChartRing (k := k) i))).inv
      (coordinate i l)))
    (fun l => (rightChartMap i j).appTop ((Scheme.ΓSpecIso (.of (ChartRing (k := k) j))).inv
      (coordinate j l)))

private def chartPolynomial (i : Fin m) (j : Fin n)
    (P : MvPolynomial (Fin m ⊕ Fin n) k) : Γ((pairChart (k := k) i j).toScheme, ⊤) :=
  MvPolynomial.eval₂Hom (chartCoefficients i j) (chartVariables i j) P

omit [IsAlgClosed k] in
private theorem point_mem_projectiveChart (i : Fin m) (a : Fin m → k) (ha : a ≠ 0) :
    (projectivePointOfVector a ha).val (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k (Fin m)) (MvPolynomial.X i) ↔ a i ≠ 0 := by
  rw [Proj.mem_basicOpen]
  exact not_congr (by
    simpa using (projectivePointOfVector_mem_iff a ha (MvPolynomial.isHomogeneous_X k i)))

private theorem point_mem_pairChart (i : Fin m) (j : Fin n)
    (a : Fin m → k) (ha : a ≠ 0) (b : Fin n → k) (hb : b ≠ 0) :
    (prodPoint (projectivePointOfVector a ha) (projectivePointOfVector b hb)).val
      (IsLocalRing.closedPoint k) ∈ pairChart i j ↔ a i ≠ 0 ∧ b j ≠ 0 := by
  change (leftProjection (k := k) (m := m) (n := n)
    ((prodPoint (projectivePointOfVector a ha) (projectivePointOfVector b hb)).val
      (IsLocalRing.closedPoint k)) ∈
      Proj.basicOpen (projectiveGrading k (Fin m)) (MvPolynomial.X i) ∧
    rightProjection (k := k) (m := m) (n := n)
    ((prodPoint (projectivePointOfVector a ha) (projectivePointOfVector b hb)).val
      (IsLocalRing.closedPoint k)) ∈
      Proj.basicOpen (projectiveGrading k (Fin n)) (MvPolynomial.X j)) ↔ _
  have h1 := congrArg (fun x => x.val (IsLocalRing.closedPoint k))
    (fst_prodPoint (projectivePointOfVector a ha) (projectivePointOfVector b hb))
  have h2 := congrArg (fun x => x.val (IsLocalRing.closedPoint k))
    (snd_prodPoint (projectivePointOfVector a ha) (projectivePointOfVector b hb))
  change leftProjection ((prodPoint _ _).val _) = _ at h1
  change rightProjection ((prodPoint _ _).val _) = _ at h2
  rw [h1, h2, point_mem_projectiveChart, point_mem_projectiveChart]

private theorem chartPolynomial_eval (i : Fin m) (j : Fin n)
    (P : MvPolynomial (Fin m ⊕ Fin n) k)
    (a : Fin m → k) (ha : a ≠ 0) (b : Fin n → k) (hb : b ≠ 0)
    (hi : a i ≠ 0) (hj : b j ≠ 0)
    (q : Spec (.of k) ⟶ (pairChart (k := k) i j).toScheme)
    (hq : q ≫ (pairChart i j).ι =
      (prodPoint (projectivePointOfVector a ha) (projectivePointOfVector b hb)).val) :
    pointEval q (chartPolynomial i j P) =
      MvPolynomial.eval (Sum.elim (fun l => (a i)⁻¹ * a l)
        (fun l => (b j)⁻¹ * b l)) P := by
  have hc : (pointEval q).comp (chartCoefficients i j) = RingHom.id k := by
    ext r
    change pointEval q (((pairChart i j).ι ≫ (biprojective k m n).structureMap).appTop
      ((Scheme.ΓSpecIso (.of k)).inv r)) = r
    apply pointEval_coeff
    rw [← Category.assoc, hq]
    exact (prodPoint (projectivePointOfVector a ha) (projectivePointOfVector b hb)).property
  have hleft : q ≫ leftChartMap i j ≫ inclusion i = (projectivePointOfVector a ha).val := by
    rw [leftChartMap_fac, ← Category.assoc, hq]
    exact congrArg Subtype.val (fst_prodPoint (projectivePointOfVector a ha) (projectivePointOfVector b hb))
  have hright : q ≫ rightChartMap i j ≫ inclusion j = (projectivePointOfVector b hb).val := by
    rw [rightChartMap_fac, ← Category.assoc, hq]
    exact congrArg Subtype.val (snd_prodPoint (projectivePointOfVector a ha) (projectivePointOfVector b hb))
  have hv : (fun l => pointEval q (chartVariables i j l)) =
      Sum.elim (fun l => (a i)⁻¹ * a l) (fun l => (b j)⁻¹ * b l) := by
    funext l
    cases l with
    | inl l =>
      change pointEval q ((leftChartMap i j).appTop _) = _
      rw [pointEval_spec]
      exact point_coordinate i l a ha hi _ (by simpa only [Category.assoc] using hleft)
    | inr l =>
      change pointEval q ((rightChartMap i j).appTop _) = _
      rw [pointEval_spec]
      exact point_coordinate j l b hb hj _ (by simpa only [Category.assoc] using hright)
  rw [chartPolynomial, MvPolynomial.map_eval₂Hom, hc, hv]
  rfl


private def chartNonzero (i : Fin m) (j : Fin n)
    (P : MvPolynomial (Fin m ⊕ Fin n) k) : (biprojective k m n).toScheme.Opens :=
  (pairChart i j).ι ''ᵁ (pairChart i j).toScheme.basicOpen (chartPolynomial i j P)

private theorem point_mem_chartNonzero (i : Fin m) (j : Fin n)
    (P : MvPolynomial (Fin m ⊕ Fin n) k) (degree : ℕ × ℕ)
    (hP : P.IsWeightedHomogeneous blockWeight degree)
    (a : Fin m → k) (ha : a ≠ 0) (b : Fin n → k) (hb : b ≠ 0) :
    (prodPoint (projectivePointOfVector a ha) (projectivePointOfVector b hb)).val
      (IsLocalRing.closedPoint k) ∈ chartNonzero i j P ↔
      a i ≠ 0 ∧ b j ≠ 0 ∧ MvPolynomial.eval (Sum.elim a b) P ≠ 0 := by
  let p := prodPoint (projectivePointOfVector a ha) (projectivePointOfVector b hb)
  by_cases hmem : p.val (IsLocalRing.closedPoint k) ∈ pairChart i j
  · obtain ⟨hi, hj⟩ := (point_mem_pairChart i j a ha b hb).mp hmem
    have hr : Set.range p.val ⊆ Set.range (pairChart (k := k) i j).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      obtain rfl := Subsingleton.elim z (IsLocalRing.closedPoint k)
      exact hmem
    let q := IsOpenImmersion.lift (pairChart (k := k) i j).ι p.val hr
    have hq : q ≫ (pairChart i j).ι = p.val := IsOpenImmersion.lift_fac _ _ _
    have hcp : (pairChart i j).ι (q (IsLocalRing.closedPoint k)) =
        p.val (IsLocalRing.closedPoint k) :=
      congrArg (fun f => f (IsLocalRing.closedPoint k)) hq
    have himage : p.val (IsLocalRing.closedPoint k) ∈ chartNonzero i j P ↔
        q (IsLocalRing.closedPoint k) ∈ (pairChart i j).toScheme.basicOpen
          (chartPolynomial i j P) := by
      change p.val (IsLocalRing.closedPoint k) ∈
        (pairChart i j).ι '' ((pairChart i j).toScheme.basicOpen (chartPolynomial i j P) : Set _) ↔ _
      rw [← hcp]
      constructor
      · rintro ⟨x, hx, he⟩
        have he' : x = q (IsLocalRing.closedPoint k) := Subtype.ext he
        rw [← he']
        exact hx
      · intro hx
        exact ⟨_, hx, rfl⟩
    rw [himage, pointEval_nonzero, chartPolynomial_eval i j P a ha b hb hi hj q hq]
    constructor
    · intro h
      exact ⟨hi, hj, (not_congr (eval_bihomogeneous_normalize_iff P degree hP a b i j hi hj)).mp h⟩
    · intro h
      exact (not_congr (eval_bihomogeneous_normalize_iff P degree hP a b i j hi hj)).mpr h.2.2
  · have hn : ¬ (a i ≠ 0 ∧ b j ≠ 0) :=
      fun h => hmem ((point_mem_pairChart i j a ha b hb).mpr h)
    have hn' : p.val (IsLocalRing.closedPoint k) ∉ chartNonzero i j P := by
      rintro ⟨x, hx, he⟩
      apply hmem
      rw [← he]
      exact x.property
    exact iff_of_false hn' (fun h => hn ⟨h.1, h.2.1⟩)

/-- Bihomogeneous equations cut out closed subsets of the actual projective scheme product. -/
theorem bihomogeneousZeroLoci : BihomogeneousZeroLoci k := by
  intro m n P degree hP
  refine ⟨(⨆ i, ⨆ j, chartNonzero i j P).compl, ?_⟩
  intro a ha b hb
  change (prodPoint (projectivePointOfVector a ha) (projectivePointOfVector b hb)).val
    (IsLocalRing.closedPoint k) ∉ (⨆ i, ⨆ j, chartNonzero i j P) ↔ _
  simp only [Opens.mem_iSup, point_mem_chartNonzero _ _ P degree hP a ha b hb]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by simpa [Function.ne_iff] using ha
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by simpa [Function.ne_iff] using hb
  constructor
  · intro h
    by_contra hp
    exact h ⟨i, j, hi, hj, hp⟩
  · intro hp
    rintro ⟨i, j, _, _, h⟩
    exact h hp
end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry.DeterminantalLocus
