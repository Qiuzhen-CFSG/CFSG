module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.RootSupport.NaturalCoefficients.Coefficients
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Coordinates
public import Theory.AlgebraicGroup.Tori.Character.Duality

/-!
# Natural matrix characters in simple-coroot coordinates

The eight diagonal characters are computed in the source coroot coordinates.
For entries between distinct hyperbolic planes, the column-minus-row exponent
is an explicit signed type-D root. Pairing with each simple coroot identifies
the quotient of algebraic entry characters with `coordinateRootWeight`.
The natural action of the coroot product then proves the scaling identity for
each polynomial matrix coefficient of an equivariant additive curve.

Source: GLS3 1.9.2, 1.12.1(g), and 1.14.1–5
(`refs/KGroup/GLS3/Chapter1.tex`). Vertex 1 is central, with arms 0, 2, 3.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Pinning.NaturalCoefficients
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators
universe u
variable (k : Type u) [Field k] [IsAlgClosed k]

local instance (T : ClosedSubgroup (groupVariety k)) : AlgebraicGroup T.carrierVariety :=
  T.carrierAlgebraicGroup

/-- The ordinary diagonal exponent of a hyperbolic basis vector. -/
@[expose] def entryExponent : Index → Fin 4 → ℤ
  | .inl i => Pi.single i 1
  | .inr i => Pi.single i (-1)

/-- Pair the ordinary diagonal exponent with each numbered simple coroot. -/
@[expose] def entryCorootExponent (p : Index) (i : Fin 4) : ℤ :=
  ∑ j, entryExponent p j * evenOrthogonalRootExponent 4 (simpleRoot i) j

/-- The genuine algebraic character acting on a natural basis vector. -/
def entryWeight (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (p : Index) : TorusWeight T :=
  TorusCharacter.pullback e.inv (dLaurentCharacter 4 (entryCorootExponent p))

/-- The diagonal scalar on either member of a hyperbolic pair. -/
@[expose] def diagonalEntry (d : Fin 4 → kˣ) : Index → kˣ
  | .inl i => d i
  | .inr i => (d i)⁻¹

omit [IsAlgClosed k] in
lemma diagonal_basis (d : Fin 4 → kˣ) (q : Index) :
    (hyperbolicDiagonalPoint 4 d).1 (basis k q) =
      (diagonalEntry k d q : k) • basis k q := by
  cases q with
  | inl i =>
    ext p <;> by_cases hp : p = i <;>
      simp [basis_apply, diagonalEntry, hyperbolicDiagonalPoint,
        hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv, Pi.single_apply, hp]
  | inr i =>
    ext p <;> by_cases hp : p = i <;>
      simp [basis_apply, diagonalEntry, hyperbolicDiagonalPoint,
        hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv, Pi.single_apply, hp]

omit [IsAlgClosed k] in
lemma coord_diagonal_inv (d : Fin 4 → kˣ) (p : Index) (v : QuadraticSpace k) :
    (basis k).coord p ((hyperbolicDiagonalPoint 4 d).1⁻¹ v) =
      (diagonalEntry k d p : k)⁻¹ * (basis k).coord p v := by
  cases p <;> simp [diagonalEntry, basis,
    hyperbolicDiagonalPoint, hyperbolicDiagonalIsometry, hyperbolicDiagonalLinearEquiv]

lemma pointMatrix_conjugation (g x : Points k) (d : Fin 4 → kˣ)
    (hg : naturalAction k g = hyperbolicDiagonalPoint 4 d) (p q : Index) :
    pointMatrix k (g⁻¹ * x * g) p q =
      ((diagonalEntry k d q : k) * (diagonalEntry k d p : k)⁻¹) *
        pointMatrix k x p q := by
  rw [pointMatrix_apply, pointMatrix_apply]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply]
  rw [hg, diagonal_basis]
  simp only [map_smul, coord_diagonal_inv, smul_eq_mul]
  ring

lemma entryCorootExponent_inl (i j : Fin 4) :
    entryCorootExponent (.inl i) j = evenOrthogonalRootExponent 4 (simpleRoot j) i := by
  classical
  simp [entryCorootExponent, entryExponent, Pi.single_apply]

lemma entryCorootExponent_inr (i j : Fin 4) :
    entryCorootExponent (.inr i) j = -evenOrthogonalRootExponent 4 (simpleRoot j) i := by
  classical
  simp [entryCorootExponent, entryExponent, Pi.single_apply]

lemma entryCorootExponent_inl_values (i : Fin 4) :
    entryCorootExponent (.inl i) =
      (![![-1, 0, 0, 0], ![1, -1, 0, 0], ![0, 1, -1, -1], ![0, 0, 1, -1]] :
        Fin 4 → Fin 4 → ℤ) i := by
  funext j
  rw [entryCorootExponent_inl]
  fin_cases i <;> fin_cases j <;>
    norm_num [evenOrthogonalRootExponent, simpleRoot, typeDSimpleRootIndex,
      Pi.single_apply, Fin.ext_iff, Fin.val_last]

omit [IsAlgClosed k] in
lemma entryCorootExponent_laurent (d : Fin 4 → kˣ) (p : Index) :
    (∏ i, d i ^ entryCorootExponent p i) =
      diagonalEntry k (CorootTorus.diagonal k d) p := by
  have hinl (i : Fin 4) : (∏ j, d j ^ entryCorootExponent (.inl i) j) =
      CorootTorus.diagonal k d i := by
    rw [entryCorootExponent_inl_values]
    fin_cases i <;> simp [CorootTorus.diagonal, Fin.prod_univ_succ, mul_assoc]
  cases p with
  | inl i => exact hinl i
  | inr i =>
    change (∏ j, d j ^ entryCorootExponent (.inr i) j) = (CorootTorus.diagonal k d i)⁻¹
    simp only [entryCorootExponent_inr, zpow_neg, Finset.prod_inv_distrib]
    simpa only [entryCorootExponent_inl] using congrArg Inv.inv (hinl i)

lemma entryWeight_apply (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (p : Index) (t : Variety.Point (dVariety k 4)) :
    (entryWeight k T e p).pointCharacter (e.hom.onPoints t) =
      (diagonalEntry k (CorootTorus.diagonal k (dPointEquiv 4 t)) p : k) := by
  change (dPointEquiv 1 ((dLaurentCharacter 4 (entryCorootExponent p)).onPoints
    (e.inv.onPoints (e.hom.onPoints t))) 0 : k) = _
  rw [e.hom_inv_id, dLaurentCharacter_apply, entryCorootExponent_laurent]

/-- Every entry between distinct pairs has an explicit signed type-D root exponent. -/
lemma exists_rootExponent_eq_entry_sub (p q : Index)
    (hpq : pairIndex p ≠ pairIndex q) :
    ∃ r : RootIndex, evenOrthogonalRootExponent 4 r = entryExponent q - entryExponent p := by
  let pos : ({-1, 1} : Set ℝ) := ⟨1, by simp⟩
  let neg : ({-1, 1} : Set ℝ) := ⟨-1, by simp⟩
  cases p with
  | inl i =>
    cases q with
    | inl j =>
      change i ≠ j at hpq
      rcases lt_or_gt_of_ne hpq with hij | hji
      · refine ⟨⟨⟨⟨i,j⟩, hij⟩, pos, neg⟩, ?_⟩
        funext l
        by_cases hli : l = i <;> by_cases hlj : l = j <;>
          norm_num [evenOrthogonalRootExponent, entryExponent, pos, neg, Pi.single_apply,
            hli, hlj, hpq, hpq.symm]
      · refine ⟨⟨⟨⟨j,i⟩, hji⟩, neg, pos⟩, ?_⟩
        funext l
        by_cases hli : l = i <;> by_cases hlj : l = j <;>
          norm_num [evenOrthogonalRootExponent, entryExponent, pos, neg, Pi.single_apply,
            hli, hlj, hpq, hpq.symm]
    | inr j =>
      change i ≠ j at hpq
      rcases lt_or_gt_of_ne hpq with hij | hji
      · refine ⟨⟨⟨⟨i,j⟩, hij⟩, pos, pos⟩, ?_⟩
        funext l
        by_cases hli : l = i <;> by_cases hlj : l = j <;>
          norm_num [evenOrthogonalRootExponent, entryExponent, pos, Pi.single_apply, hli, hlj, hpq, hpq.symm]
      · refine ⟨⟨⟨⟨j,i⟩, hji⟩, pos, pos⟩, ?_⟩
        funext l
        by_cases hli : l = i <;> by_cases hlj : l = j <;>
          norm_num [evenOrthogonalRootExponent, entryExponent, pos, Pi.single_apply, hli, hlj, hpq, hpq.symm]
  | inr i =>
    cases q with
    | inl j =>
      change i ≠ j at hpq
      rcases lt_or_gt_of_ne hpq with hij | hji
      · refine ⟨⟨⟨⟨i,j⟩, hij⟩, neg, neg⟩, ?_⟩
        funext l
        by_cases hli : l = i <;> by_cases hlj : l = j <;>
          norm_num [evenOrthogonalRootExponent, entryExponent, neg, Pi.single_apply, hli, hlj, hpq, hpq.symm]
      · refine ⟨⟨⟨⟨j,i⟩, hji⟩, neg, neg⟩, ?_⟩
        funext l
        by_cases hli : l = i <;> by_cases hlj : l = j <;>
          norm_num [evenOrthogonalRootExponent, entryExponent, neg, Pi.single_apply, hli, hlj, hpq, hpq.symm]
    | inr j =>
      change i ≠ j at hpq
      rcases lt_or_gt_of_ne hpq with hij | hji
      · refine ⟨⟨⟨⟨i,j⟩, hij⟩, neg, pos⟩, ?_⟩
        funext l
        by_cases hli : l = i <;> by_cases hlj : l = j <;>
          norm_num [evenOrthogonalRootExponent, entryExponent, pos, neg, Pi.single_apply, hli, hlj, hpq, hpq.symm]
      · refine ⟨⟨⟨⟨j,i⟩, hji⟩, pos, neg⟩, ?_⟩
        funext l
        by_cases hli : l = i <;> by_cases hlj : l = j <;>
          norm_num [evenOrthogonalRootExponent, entryExponent, pos, neg, Pi.single_apply, hli, hlj, hpq, hpq.symm]

/-- The column character divided by the row character is the coordinate-root character. -/
lemma coordinateRootWeight_eq_entry_quotient
    (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (p q : Index) (r : RootIndex)
    (hr : evenOrthogonalRootExponent 4 r = entryExponent q - entryExponent p) :
    coordinateRootWeight k T e r = entryWeight k T e q * (entryWeight k T e p)⁻¹ := by
  have hexp : rootCorootExponent r = entryCorootExponent q - entryCorootExponent p := by
    funext i
    simp [rootCorootExponent, hr, entryCorootExponent, sub_mul, Finset.sum_sub_distrib]
  have hchar : dLaurentCharacter (k := k) 4 (rootCorootExponent r) =
      dLaurentCharacter 4 (entryCorootExponent q) *
        (dLaurentCharacter 4 (entryCorootExponent p))⁻¹ := by
    apply Additive.ofMul.injective
    change dLaurentCharacterAddEquiv 4 (rootCorootExponent r) =
      dLaurentCharacterAddEquiv 4 (entryCorootExponent q) -
        dLaurentCharacterAddEquiv 4 (entryCorootExponent p)
    rw [hexp, map_sub]
  unfold coordinateRootWeight entryWeight
  rw [hchar, map_mul, map_inv]

omit [IsAlgClosed k] in
private lemma pointCharacter_inv {T : Variety k} [AlgebraicGroup T]
    (χ : TorusCharacter T) (s : Variety.Point T) :
    (χ⁻¹).pointCharacter s = (χ.pointCharacter s)⁻¹ := by
  change ((dPointEquiv 1 ((χ.onPoints s)⁻¹) 0 : k)) =
    ((dPointEquiv 1 (χ.onPoints s) 0 : k))⁻¹
  have hmul := congrFun (dPointEquiv_mul 1 (χ.onPoints s)⁻¹ (χ.onPoints s)) 0
  rw [inv_mul_cancel, dPointEquiv_one] at hmul
  simp only [Pi.one_apply, Pi.mul_apply] at hmul
  have hu : dPointEquiv 1 ((χ.onPoints s)⁻¹) 0 = (dPointEquiv 1 (χ.onPoints s) 0)⁻¹ :=
    eq_inv_of_mul_eq_one_left hmul.symm
  simpa using congrArg Units.val hu

omit [IsAlgClosed k] in
private lemma pointCharacter_mul {T : Variety k} [AlgebraicGroup T]
    (χ ψ : TorusCharacter T) (s : Variety.Point T) :
    (χ * ψ).pointCharacter s = χ.pointCharacter s * ψ.pointCharacter s := by
  change (dPointEquiv 1 (χ.onPoints s * ψ.onPoints s) 0 : k) = _
  rw [dPointEquiv_mul]
  rfl

lemma coordinateRootWeight_pointCharacter_eq_entry_quotient
    (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (p q : Index) (r : RootIndex)
    (hr : evenOrthogonalRootExponent 4 r = entryExponent q - entryExponent p)
    (s : Variety.Point T.carrierVariety) :
    (coordinateRootWeight k T e r).pointCharacter s =
      (entryWeight k T e q).pointCharacter s * ((entryWeight k T e p).pointCharacter s)⁻¹ := by
  rw [coordinateRootWeight_eq_entry_quotient k T e p q r hr,
    pointCharacter_mul, pointCharacter_inv]

variable [CharP k 2]

lemma naturalAction_torusPoint (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (he : HasCorootCoordinates k T e) (t : Variety.Point (dVariety k 4)) :
    naturalAction k (T.includePoint (e.hom.onPoints t)) =
      hyperbolicDiagonalPoint 4 (CorootTorus.diagonal k (dPointEquiv 4 t)) := by
  change naturalAction k (T.inclusion.onPoints (e.hom.onPoints t)) = _
  rw [he]
  exact CorootTorus.naturalAction_parameter k (dPointEquiv 4 t)

lemma pointMatrix_torus_conjugation (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (he : HasCorootCoordinates k T e) (s : Variety.Point T.carrierVariety)
    (x : Points k) (p q : Index) :
    pointMatrix k ((T.includePoint s)⁻¹ * x * T.includePoint s) p q =
      ((entryWeight k T e q).pointCharacter s * ((entryWeight k T e p).pointCharacter s)⁻¹) *
        pointMatrix k x p q := by
  obtain ⟨t, rfl⟩ := e.toMulEquiv.surjective s
  change pointMatrix k ((T.includePoint (e.hom.onPoints t))⁻¹ * x *
    T.includePoint (e.hom.onPoints t)) p q =
      ((entryWeight k T e q).pointCharacter (e.hom.onPoints t) *
        ((entryWeight k T e p).pointCharacter (e.hom.onPoints t))⁻¹) * pointMatrix k x p q
  rw [entryWeight_apply, entryWeight_apply]
  exact pointMatrix_conjugation k _ x _ (naturalAction_torusPoint k T e he t) p q

/-- Torus conjugation scales the actual polynomial coefficient by its coordinate root. -/
lemma polynomial_scaling (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (he : HasCorootCoordinates k T e)
    (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k)) (χ : TorusWeight T)
    (hχ : ∀ s a, (T.includePoint s)⁻¹ * f.onPoints (kPlusPoint a) * T.includePoint s =
      f.onPoints (kPlusPoint (χ.pointCharacter s * a)))
    (p q : Index) (r : RootIndex)
    (hr : evenOrthogonalRootExponent 4 r = entryExponent q - entryExponent p)
    (s : Variety.Point T.carrierVariety) (a : k) :
    (polynomial k f p q).eval (χ.pointCharacter s * a) =
      (coordinateRootWeight k T e r).pointCharacter s * (polynomial k f p q).eval a := by
  rw [polynomial_eval_matrix, ← hχ s a, pointMatrix_torus_conjugation k T e he,
    ← polynomial_eval_matrix, coordinateRootWeight_pointCharacter_eq_entry_quotient k T e p q r hr]

end Triality.SimplyConnected.Pinning.NaturalCoefficients
