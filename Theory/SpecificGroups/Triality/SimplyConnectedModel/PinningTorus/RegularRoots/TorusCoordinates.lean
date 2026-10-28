module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootPoints
public import Theory.AlgebraicGroup.RootSystems.EvenOrthogonalDiagonalTorus

/-!
# Root characters in geometric simple-coroot coordinates

For any actual algebraic isomorphism from the four-dimensional split torus to
a closed Spin subgroup, `HasCorootCoordinates` specifies its inclusion by the
ordered product of the four source coroot words. It assumes no root datum.
The proposed root characters are genuine Laurent characters transported along
that algebraic isomorphism. Their exponents are the integral dot products of
the coordinate roots with the numbered simple coroots. In particular, the
simple-root exponents are the standard D4 Cartan entries, with vertex 1 central.

The proved coroot point formulas give the conjugation equation for every root
point. Regularity of the forward root curves and exhaustiveness of these
characters as actual torus roots remain separate obligations.

Source: GLS3, 1.9.3, 1.12.1(g), and 1.14.1
(`refs/KGroup/GLS3/Chapter1.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

local instance torusCoordinatesAlgebraicGroup (T : ClosedSubgroup (groupVariety k)) :
    AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup

/-- The ordered product of the four source simple coroots. -/
def corootTuplePoint (d : Fin 4 → kˣ) : Points k :=
  (List.ofFn fun i : Fin 4 => simpleCoroot k i (d i)).prod

/-- A geometric torus coordinate system has the source coroot point formula. -/
def HasCorootCoordinates (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup) : Prop :=
  ∀ t, T.inclusion.onPoints (e.hom.onPoints t) = corootTuplePoint k (dPointEquiv 4 t)

/-- The integral root pairing with each numbered simple coroot. -/
def rootCorootExponent (r : RootIndex) (i : Fin 4) : ℤ :=
  ∑ p, evenOrthogonalRootExponent 4 r p * evenOrthogonalRootExponent 4 (simpleRoot i) p

/-- The source numbering gives the standard D4 Cartan matrix. -/
theorem rootCorootExponent_simple (i j : Fin 4) :
    rootCorootExponent (simpleRoot i) j = typeDCartanMatrix 2 i j := by
  unfold rootCorootExponent
  simp only [Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;>
    norm_num [evenOrthogonalRootExponent, simpleRoot,
      typeDSimpleRootIndex, typeDCartanMatrix, Pi.single_apply,
      Fin.ext_iff, Fin.val_last]

omit [IsAlgClosed k] [CharP k 2] in
/-- The natural-action coroot diagonal has the coordinate exponent `-α`. -/
theorem corootDiagonal_eq_zpow (r : RootIndex) (t : kˣ) (p : Fin 4) :
    corootDiagonal k r t p = t ^ evenOrthogonalRootExponent 4 r p := by
  classical
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, s, v⟩
  by_cases hpi : p = i
  · subst p
    by_cases hs : s.val = 1 <;>
      simp [corootDiagonal, evenOrthogonalRootExponent, ite_apply, hij.ne, hs]
  · by_cases hpj : p = j
    · subst p
      by_cases hv : v.val = 1 <;>
        simp [corootDiagonal, evenOrthogonalRootExponent, ite_apply, hpi, hv]
    · simp [corootDiagonal, evenOrthogonalRootExponent, ite_apply, hpi, hpj]

omit [CharP k 2] in
/-- The matrix conjugation scalar is the corresponding Laurent monomial. -/
theorem rootScale_eq_prod (r : RootIndex) (d : Fin 4 → kˣ) :
    evenOrthogonalRootScale 4 r d =
      ((∏ p, d p ^ evenOrthogonalRootExponent 4 r p : kˣ) : k) := by
  have h := evenOrthogonalRootWeight_apply (k := k) 4 (show 4 ≤ 4 from le_rfl)
    r ((dPointEquiv 4).symm d)
  rw [evenOrthogonalRootWeight, evenOrthogonalDiagonalCharacter_apply] at h
  simpa only [Equiv.apply_symm_apply] using h.symm

omit [CharP k 2] in
/-- Each simple coroot acts with the integral root-pairing exponent. -/
theorem rootScale_simpleCoroot (r : RootIndex) (i : Fin 4) (t : kˣ) :
    evenOrthogonalRootScale 4 r (corootDiagonal k (simpleRoot i) t) =
      (t : k) ^ rootCorootExponent r i := by
  rw [rootScale_eq_prod]
  simp_rw [corootDiagonal_eq_zpow, ← zpow_mul]
  simp [rootCorootExponent, Fin.prod_univ_succ, Fin.sum_univ_succ,
    zpow_add₀ t.ne_zero, mul_comm]

/-- The genuine algebraic character in the given coroot coordinates. -/
def coordinateRootWeight (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (r : RootIndex) : @TorusCharacter k _ T.carrierVariety T.carrierAlgebraicGroup :=
  TorusCharacter.pullback e.inv (dLaurentCharacter 4 (rootCorootExponent r))

omit [CharP k 2] in
/-- Evaluation of the root character on the geometric torus coordinates. -/
theorem coordinateRootWeight_apply (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (r : RootIndex) (t : Variety.Point (dVariety k 4)) :
    (coordinateRootWeight k T e r).pointCharacter (e.hom.onPoints t) =
      ∏ i, (dPointEquiv 4 t i : k) ^ rootCorootExponent r i := by
  let : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  change (dPointEquiv 1 ((dLaurentCharacter 4 (rootCorootExponent r)).onPoints
    (e.inv.onPoints (e.hom.onPoints t))) 0 : k) = _
  rw [e.hom_inv_id, dLaurentCharacter_apply]
  simp

private theorem listCoroot_rootPoint_conjugation (r : RootIndex)
    (d : Fin 4 → kˣ) (l : List (Fin 4)) (a : k) :
    (l.map (fun i => simpleCoroot k i (d i))).prod⁻¹ * rootPoint k r a *
        (l.map (fun i => simpleCoroot k i (d i))).prod =
      rootPoint k r ((l.map (fun i => (d i : k) ^ rootCorootExponent r i)).prod * a) := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, mul_inv_rev]
    calc
      _ = (l.map (fun j => simpleCoroot k j (d j))).prod⁻¹ *
          ((simpleCoroot k i (d i))⁻¹ * rootPoint k r a * simpleCoroot k i (d i)) *
          (l.map (fun j => simpleCoroot k j (d j))).prod := by group
      _ = _ := by
        rw [corootWord_rootPoint_conjugation, rootScale_simpleCoroot, ih]
        congr 1
        ring

/-- The ordered coroot product scales every anchored root parameter. -/
theorem corootTuplePoint_rootPoint_conjugation (r : RootIndex)
    (d : Fin 4 → kˣ) (a : k) :
    (corootTuplePoint k d)⁻¹ * rootPoint k r a * corootTuplePoint k d =
      rootPoint k r ((∏ i, (d i : k) ^ rootCorootExponent r i) * a) := by
  simpa only [corootTuplePoint, List.map_ofFn, Function.comp_id, List.prod_ofFn] using
    listCoroot_rootPoint_conjugation k r d (List.ofFn id) a

/-- The proposed algebraic character gives the actual conjugation action. -/
theorem coordinateRootWeight_conjugation (T : ClosedSubgroup (groupVariety k))
    (e : @Iso k _ (dVariety k 4) T.carrierVariety _ T.carrierAlgebraicGroup)
    (he : HasCorootCoordinates k T e) (r : RootIndex)
    (s : Variety.Point T.carrierVariety) (a : k) :
    (T.includePoint s)⁻¹ * rootPoint k r a * T.includePoint s =
      rootPoint k r ((coordinateRootWeight k T e r).pointCharacter s * a) := by
  let : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
  obtain ⟨t, rfl⟩ := e.toMulEquiv.surjective s
  change (T.inclusion.onPoints (e.hom.onPoints t))⁻¹ * rootPoint k r a *
      T.inclusion.onPoints (e.hom.onPoints t) =
        rootPoint k r ((coordinateRootWeight k T e r).pointCharacter (e.hom.onPoints t) * a)
  rw [he, coordinateRootWeight_apply, corootTuplePoint_rootPoint_conjugation]

end Triality.SimplyConnected.Pinning
