module

public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.MarkingExistence.CalibratedCharts.CentralLifting.RootRigidity
public import Theory.AlgebraicGroup.Morphism.SL2PrincipalOpen
public import Theory.AlgebraicGroup.RootSubgroups.SL2RootCurves
public import Theory.AlgebraicGroup.Morphism.Operations
public import Theory.AlgebraicGroup.Instance.SLConnected
public import Theory.AlgebraicGroup.Irreducible.Product

/-!
# Gluing SL₂ root lifts through a finite kernel

Let `q : Y → Q` and `p : SL₂ → Q` be algebraic-group morphisms. Regular
homomorphic lifts `u,v : Ga → Y` of the standard upper and lower root curves
extend to a morphism `F : SL₂ → Y`, provided their values lie in a subgroup
`S` for which `ker(q) ∩ S` is finite. No centrality, reductivity or
surjectivity hypothesis is required.

The two first-column charts use the words
`v((c - 1)/a) u(a - 1) v(1) u((b - a + 1)/a)` and
`u((a - 1)/c) v(c) u((d - 1)/c)`. On the overlap, parametrized by
`D₂ × Ga` with `d = (1+bc)/a`, their projections agree by matrix identities.
Their difference has finite image, so connectedness and agreement at
`(a,c,b) = (1,1,0)` prove equality. Principal-open descent gives a regular
map. The same finite-kernel comparison on `SL₂ × SL₂`, based at `(1, 1)`,
proves its group law. The root restrictions follow directly from the a-chart.

This is the geometric lifting step for Borel, *Linear Algebraic Groups*,
§§13.13--13.14 (`refs/KGroup/Bor1/Chapter4.tex`), using the elementary root
words of GLS3, §1.12 (`refs/KGroup/GLS3/Chapter1.tex`). The chart words,
matrix factorizations and polynomial-map helpers below are adapted from
`Theory.AlgebraicGroup.Morphism.SL2RootRegularity`; its helpers are private.
The actual central PGL₂ application takes `S` to be the derived subgroup;
`RootRigidity` and `SL2Derived` supply its finite-kernel and membership inputs.
-/

noncomputable section
universe u
namespace Theory.AlgebraicGroup
namespace BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts.CentralLifting
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {Y Q : Variety k} [AlgebraicGroup Y] [AlgebraicGroup Q]

omit [IsAlgClosed k] in
private lemma kPlus_coord (s : k) : (kPlusPoint s).val PUnit.unit = s := rfl

private abbrev upper (a : k) := (standardSL2UpperMorphism (k := k)).onPoints (kPlusPoint a)
private abbrev lower (a : k) := (standardSL2LowerMorphism (k := k)).onPoints (kPlusPoint a)

private lemma factor_c (x : Variety.Point (slVariety k 2))
    (hc : x.val (ULift.up (1, 0)) ≠ 0) :
    upper ((x.val (ULift.up (0, 0)) - 1) / x.val (ULift.up (1, 0))) *
      lower (x.val (ULift.up (1, 0))) *
      upper ((x.val (ULift.up (1, 1)) - 1) / x.val (ULift.up (1, 0))) = x := by
  have hd := slPoint_det_eq_one 2 x
  rw [Matrix.det_fin_two] at hd
  simp only [slPointMatrix] at hd
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change Matrix.transvection (0 : Fin 2) 1 _ *
    Matrix.transvection (1 : Fin 2) 0 _ *
    Matrix.transvection (0 : Fin 2) 1 _ = slPointMatrix 2 x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, slPointMatrix,
      kPlus_coord] <;>
    (try field_simp) <;> grind only

private lemma factor_a (x : Variety.Point (slVariety k 2))
    (ha : x.val (ULift.up (0, 0)) ≠ 0) :
    lower ((x.val (ULift.up (1, 0)) - 1) / x.val (ULift.up (0, 0))) *
      upper (x.val (ULift.up (0, 0)) - 1) * lower (1 : k) *
      upper ((x.val (ULift.up (0, 1)) - x.val (ULift.up (0, 0)) + 1) /
        x.val (ULift.up (0, 0))) = x := by
  have hd := slPoint_det_eq_one 2 x
  rw [Matrix.det_fin_two] at hd
  simp only [slPointMatrix] at hd
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change Matrix.transvection (1 : Fin 2) 0 _ *
    Matrix.transvection (0 : Fin 2) 1 _ *
    Matrix.transvection (1 : Fin 2) 0 _ *
    Matrix.transvection (0 : Fin 2) 1 _ = slPointMatrix 2 x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, slPointMatrix,
      kPlus_coord] <;>
    (try field_simp) <;> grind only

private def polyLine {V : Variety k} (p : MvPolynomial V.Coordinates k) :
    Variety.Morphism V (KPlus k) where
  toFun x := kPlusPoint (evalPolynomial x.val p)
  regular _ := ⟨p, fun _ => rfl⟩

private def curve {V H : Variety k} [AlgebraicGroup H]
    (u : Morphism (KPlus k) H) (p : MvPolynomial V.Coordinates k) :
    Variety.Morphism V H := u.toVariety.comp (polyLine p)

omit [IsAlgClosed k] in
private lemma curve_apply {V H : Variety k} [AlgebraicGroup H]
    (u : Morphism (KPlus k) H) (p : MvPolynomial V.Coordinates k)
    (x : Variety.Point V) :
    (curve u p).toFun x = u.onPoints (kPlusPoint (evalPolynomial x.val p)) := rfl

private def mulMaps {V H : Variety k} [AlgebraicGroup H]
    (f g : Variety.Morphism V H) : Variety.Morphism V H :=
  (mulMorphism H).comp (f.pair g)

omit [IsAlgClosed k] in
private lemma mulMaps_apply {V H : Variety k} [AlgebraicGroup H]
    (f g : Variety.Morphism V H) (x : Variety.Point V) :
    (mulMaps f g).toFun x = f.toFun x * g.toFun x := by
  change ((Variety.prodPointEquiv H H) ((Variety.prodPointEquiv H H).symm _)).1 *
    ((Variety.prodPointEquiv H H) ((Variety.prodPointEquiv H H).symm _)).2 = _
  rw [Equiv.apply_symm_apply]

private def wordA (u v : Morphism (KPlus k) Y) (a b c : k) : Variety.Point Y :=
  v.onPoints (kPlusPoint ((c - 1)/a)) * u.onPoints (kPlusPoint (a - 1)) *
    v.onPoints (kPlusPoint 1) * u.onPoints (kPlusPoint ((b - a + 1)/a))

private def wordC (u v : Morphism (KPlus k) Y) (a c d : k) : Variety.Point Y :=
  u.onPoints (kPlusPoint ((a - 1)/c)) * v.onPoints (kPlusPoint c) *
    u.onPoints (kPlusPoint ((d - 1)/c))

omit [IsAlgClosed k] in
private lemma wordA_mem (u v : Morphism (KPlus k) Y) (S : Subgroup (Variety.Point Y))
    (hu : ∀ t, u.onPoints t ∈ S) (hv : ∀ t, v.onPoints t ∈ S) (a b c : k) :
    wordA u v a b c ∈ S :=
  S.mul_mem (S.mul_mem (S.mul_mem (hv _) (hu _)) (hv _)) (hu _)

omit [IsAlgClosed k] in
private lemma wordC_mem (u v : Morphism (KPlus k) Y) (S : Subgroup (Variety.Point Y))
    (hu : ∀ t, u.onPoints t ∈ S) (hv : ∀ t, v.onPoints t ∈ S) (a c d : k) :
    wordC u v a c d ∈ S :=
  S.mul_mem (S.mul_mem (hu _) (hv _)) (hu _)

private lemma map_wordA (q : Morphism Y Q) (p : Morphism (slVariety k 2) Q)
    (u v : Morphism (KPlus k) Y)
    (hu : q.comp u = p.comp standardSL2UpperMorphism)
    (hv : q.comp v = p.comp standardSL2LowerMorphism) (a b c : k) :
    q.onPoints (wordA u v a b c) =
      p.onPoints (wordA standardSL2UpperMorphism standardSL2LowerMorphism a b c) := by
  have hu' (t) : q.onPoints (u.onPoints t) =
      p.onPoints (standardSL2UpperMorphism.onPoints t) :=
    congrArg (fun f : Morphism (KPlus k) Q => f.onPoints t) hu
  have hv' (t) : q.onPoints (v.onPoints t) =
      p.onPoints (standardSL2LowerMorphism.onPoints t) :=
    congrArg (fun f : Morphism (KPlus k) Q => f.onPoints t) hv
  simp only [wordA, map_mul, hu', hv']

private lemma map_wordC (q : Morphism Y Q) (p : Morphism (slVariety k 2) Q)
    (u v : Morphism (KPlus k) Y)
    (hu : q.comp u = p.comp standardSL2UpperMorphism)
    (hv : q.comp v = p.comp standardSL2LowerMorphism) (a c d : k) :
    q.onPoints (wordC u v a c d) =
      p.onPoints (wordC standardSL2UpperMorphism standardSL2LowerMorphism a c d) := by
  have hu' (t) : q.onPoints (u.onPoints t) =
      p.onPoints (standardSL2UpperMorphism.onPoints t) :=
    congrArg (fun f : Morphism (KPlus k) Q => f.onPoints t) hu
  have hv' (t) : q.onPoints (v.onPoints t) =
      p.onPoints (standardSL2LowerMorphism.onPoints t) :=
    congrArg (fun f : Morphism (KPlus k) Q => f.onPoints t) hv
  simp only [wordC, map_mul, hu', hv']

private lemma matrix_words_agree (a b c : k) (ha : a ≠ 0) (hc : c ≠ 0) :
    wordA standardSL2UpperMorphism standardSL2LowerMorphism a b c =
      wordC standardSL2UpperMorphism standardSL2LowerMorphism a c ((1 + b * c)/a) := by
  apply (slPointEquiv 2).injective
  apply Subtype.ext
  change Matrix.transvection (1 : Fin 2) 0 _ * Matrix.transvection (0 : Fin 2) 1 _ *
      Matrix.transvection (1 : Fin 2) 0 _ * Matrix.transvection (0 : Fin 2) 1 _ =
    Matrix.transvection (0 : Fin 2) 1 _ * Matrix.transvection (1 : Fin 2) 0 _ *
      Matrix.transvection (0 : Fin 2) 1 _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, kPlus_coord] <;>
    field_simp <;> ring

omit [IsAlgClosed k] in
private lemma prod_connected {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hG : Variety.IsConnected G) (hH : Variety.IsConnected H) :
    Variety.IsConnected (Variety.prod G H) := by
  have hi := prodSet_irreducible_of_irreducible
    (connectedAlgebraicGroup_irreducible G hG)
    (connectedAlgebraicGroup_irreducible H hH)
  have he : Variety.prodSet (Set.univ : Set (Variety.Point G))
      (Set.univ : Set (Variety.Point H)) = Set.univ := by
    ext z
    simp [Variety.prodSet]
  rw [he] at hi
  exact hi.isConnected

-- The overlap coordinates are a,c in the torus and b on the additive line.
private abbrev overlap (k : Type u) [Field k] := Variety.prod (dVariety k 2) (KPlus k)

private def overlapPoint (a c : kˣ) (b : k) : Variety.Point (overlap k) :=
  (Variety.prodPointEquiv _ _).symm ((dPointEquiv 2).symm ![a, c], kPlusPoint b)

private def overlapA (u v : Morphism (KPlus k) Y) : Variety.Morphism (overlap k) Y :=
  let A := MvPolynomial.X (Sum.inl (Sum.inl (ULift.up (0 : Fin 2))))
  let C := MvPolynomial.X (Sum.inl (Sum.inl (ULift.up (1 : Fin 2))))
  let B := MvPolynomial.X (Sum.inr PUnit.unit)
  let Ai := MvPolynomial.X (Sum.inl (Sum.inr (ULift.up (0 : Fin 2))))
  mulMaps (mulMaps (mulMaps (curve v ((C - 1) * Ai)) (curve u (A - 1)))
    (curve v 1)) (curve u ((B - A + 1) * Ai))

private def overlapC (u v : Morphism (KPlus k) Y) : Variety.Morphism (overlap k) Y :=
  let A := MvPolynomial.X (Sum.inl (Sum.inl (ULift.up (0 : Fin 2))))
  let C := MvPolynomial.X (Sum.inl (Sum.inl (ULift.up (1 : Fin 2))))
  let B := MvPolynomial.X (Sum.inr PUnit.unit)
  let Ai := MvPolynomial.X (Sum.inl (Sum.inr (ULift.up (0 : Fin 2))))
  let Ci := MvPolynomial.X (Sum.inl (Sum.inr (ULift.up (1 : Fin 2))))
  mulMaps (mulMaps (curve u ((A - 1) * Ci)) (curve v C))
    (curve u (((1 + B * C) * Ai - 1) * Ci))

omit [IsAlgClosed k] in
private lemma overlapA_apply (u v : Morphism (KPlus k) Y)
    (a c : kˣ) (b : k) : (overlapA u v).toFun (overlapPoint a c b) =
      wordA u v a b c := by
  simp only [overlapA, mulMaps_apply, curve_apply, evalPolynomial,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_one, MvPolynomial.eval₂_X]
  simp [overlapPoint, Variety.prodPointEquiv, dPointEquiv, wordA, div_eq_mul_inv, kPlus_coord]

omit [IsAlgClosed k] in
private lemma overlapC_apply (u v : Morphism (KPlus k) Y)
    (a c : kˣ) (b : k) : (overlapC u v).toFun (overlapPoint a c b) =
      wordC u v a c ((1 + b * (c : k))/(a : k)) := by
  simp only [overlapC, mulMaps_apply, curve_apply, evalPolynomial,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_one, MvPolynomial.eval₂_X]
  simp [overlapPoint, Variety.prodPointEquiv, dPointEquiv, wordC, div_eq_mul_inv, kPlus_coord]

omit [IsAlgClosed k] in
private lemma overlapPoint_surjective (x : Variety.Point (overlap k)) :
    ∃ (a c : kˣ) (b : k), overlapPoint a c b = x := by
  let z := (Variety.prodPointEquiv _ _) x
  refine ⟨dPointEquiv 2 z.1 0, dPointEquiv 2 z.1 1, z.2.val PUnit.unit, ?_⟩
  apply (Variety.prodPointEquiv _ _).injective
  simp only [overlapPoint, Equiv.apply_symm_apply]
  apply Prod.ext
  · apply (dPointEquiv 2).injective
    simp only [Equiv.apply_symm_apply]
    ext i
    fin_cases i <;> rfl
  · exact kPlusPoint_coordinate z.2

private lemma words_agree (q : Morphism Y Q) (p : Morphism (slVariety k 2) Q)
    (u v : Morphism (KPlus k) Y)
    (hu : q.comp u = p.comp standardSL2UpperMorphism)
    (hv : q.comp v = p.comp standardSL2LowerMorphism)
    (S : Subgroup (Variety.Point Y))
    (huS : ∀ t, u.onPoints t ∈ S) (hvS : ∀ t, v.onPoints t ∈ S)
    (hfinite : (((q.kernel ⊓ S) : Subgroup (Variety.Point Y)) :
      Set (Variety.Point Y)).Finite)
    (a b c : k) (ha : a ≠ 0) (hc : c ≠ 0) :
    wordA u v a b c = wordC u v a c ((1 + b * c)/a) := by
  have he : overlapA u v = overlapC u v := by
    refine regular_maps_eq_of_finite_kernel
      (prod_connected (dVariety_isConnected 2) kPlus_isConnected) q S hfinite
      _ _ ?_ ?_ ?_ (overlapPoint (1 : kˣ) 1 0) ?_
    · intro x
      obtain ⟨a, c, b, rfl⟩ := overlapPoint_surjective x
      rw [overlapA_apply]
      exact wordA_mem u v S huS hvS _ _ _
    · intro x
      obtain ⟨a, c, b, rfl⟩ := overlapPoint_surjective x
      rw [overlapC_apply]
      exact wordC_mem u v S huS hvS _ _ _
    · intro x
      obtain ⟨a, c, b, rfl⟩ := overlapPoint_surjective x
      rw [overlapA_apply, overlapC_apply, map_wordA q p u v hu hv,
        map_wordC q p u v hu hv, matrix_words_agree _ _ _ a.ne_zero c.ne_zero]
    · rw [overlapA_apply, overlapC_apply]
      simp [wordA, wordC, show kPlusPoint (0 : k) = 1 from rfl]
  have hx := congrArg (fun f : Variety.Morphism (overlap k) Y =>
    f.toFun (overlapPoint (Units.mk0 a ha) (Units.mk0 c hc) b)) he
  simpa only [overlapA_apply, overlapC_apply, Units.val_mk0] using hx

private def chartA (u v : Morphism (KPlus k) Y) : Variety.Morphism
    ((slVariety k 2).principalOpenChart (sl2FirstColumnPolynomial 0)) Y :=
  let X (i j : Fin 2) : MvPolynomial (Option (slVariety k 2).Coordinates) k :=
    MvPolynomial.X (some (ULift.up (i, j)))
  let T : MvPolynomial (Option (slVariety k 2).Coordinates) k := MvPolynomial.X none
  mulMaps (mulMaps (mulMaps
    (curve v ((X 1 0 - 1) * T)) (curve u (X 0 0 - 1)))
    (curve v 1)) (curve u ((X 0 1 - X 0 0 + 1) * T))

private def chartC (u v : Morphism (KPlus k) Y) : Variety.Morphism
    ((slVariety k 2).principalOpenChart (sl2FirstColumnPolynomial 1)) Y :=
  let X (i j : Fin 2) : MvPolynomial (Option (slVariety k 2).Coordinates) k :=
    MvPolynomial.X (some (ULift.up (i, j)))
  let T : MvPolynomial (Option (slVariety k 2).Coordinates) k := MvPolynomial.X none
  mulMaps (mulMaps (curve u ((X 0 0 - 1) * T)) (curve v (X 1 0)))
    (curve u ((X 1 1 - 1) * T))

private abbrev entry (x : Variety.Point (slVariety k 2)) (i j : Fin 2) :=
  x.val (ULift.up (i, j))

private lemma chartA_apply (u v : Morphism (KPlus k) Y)
    (x : Variety.Point ((slVariety k 2).principalOpenChart (sl2FirstColumnPolynomial 0))) :
    let y := ((slVariety k 2).principalOpenChartInclusion (sl2FirstColumnPolynomial 0)).toFun x
    (chartA u v).toFun x = wordA u v (entry y 0 0) (entry y 0 1) (entry y 1 0) := by
  dsimp only
  have ht : x.val none = (x.val (some (ULift.up (0, 0))))⁻¹ := by
    simpa only [sl2FirstColumnPolynomial, evalPolynomial_X,
      Variety.principalOpenChartInclusion] using
      Variety.principalOpenChart_val_none (sl2FirstColumnPolynomial 0) x
  simp only [chartA, mulMaps_apply, curve_apply, evalPolynomial, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add, MvPolynomial.eval₂_one,
    MvPolynomial.eval₂_X, ht]
  simp only [wordA, entry, Variety.principalOpenChartInclusion, div_eq_mul_inv]

private lemma chartC_apply (u v : Morphism (KPlus k) Y)
    (x : Variety.Point ((slVariety k 2).principalOpenChart (sl2FirstColumnPolynomial 1))) :
    let y := ((slVariety k 2).principalOpenChartInclusion (sl2FirstColumnPolynomial 1)).toFun x
    (chartC u v).toFun x = wordC u v (entry y 0 0) (entry y 1 0) (entry y 1 1) := by
  dsimp only
  have ht : x.val none = (x.val (some (ULift.up (1, 0))))⁻¹ := by
    simpa only [sl2FirstColumnPolynomial, evalPolynomial_X,
      Variety.principalOpenChartInclusion] using
      Variety.principalOpenChart_val_none (sl2FirstColumnPolynomial 1) x
  simp only [chartC, mulMaps_apply, curve_apply, evalPolynomial, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_one,
    MvPolynomial.eval₂_X, ht]
  simp only [wordC, entry, Variety.principalOpenChartInclusion, div_eq_mul_inv]

-- Select the a-chart wherever possible; compatibility supplies the c-chart formula.
private def liftPoints (u v : Morphism (KPlus k) Y)
    (x : Variety.Point (slVariety k 2)) : Variety.Point Y := by
  classical
  exact if entry x 0 0 ≠ 0 then wordA u v (entry x 0 0) (entry x 0 1) (entry x 1 0)
  else wordC u v (entry x 0 0) (entry x 1 0) (entry x 1 1)

private lemma liftPoints_a (u v : Morphism (KPlus k) Y)
    (x : Variety.Point (slVariety k 2)) (ha : entry x 0 0 ≠ 0) :
    liftPoints u v x = wordA u v (entry x 0 0) (entry x 0 1) (entry x 1 0) := if_pos ha

private lemma liftPoints_mem (u v : Morphism (KPlus k) Y)
    (S : Subgroup (Variety.Point Y))
    (huS : ∀ t, u.onPoints t ∈ S) (hvS : ∀ t, v.onPoints t ∈ S)
    (x : Variety.Point (slVariety k 2)) : liftPoints u v x ∈ S := by
  unfold liftPoints
  split
  · exact wordA_mem u v S huS hvS _ _ _
  · exact wordC_mem u v S huS hvS _ _ _

private lemma liftPoints_proj (q : Morphism Y Q) (p : Morphism (slVariety k 2) Q)
    (u v : Morphism (KPlus k) Y)
    (hu : q.comp u = p.comp standardSL2UpperMorphism)
    (hv : q.comp v = p.comp standardSL2LowerMorphism)
    (x : Variety.Point (slVariety k 2)) :
    q.onPoints (liftPoints u v x) = p.onPoints x := by
  unfold liftPoints
  split_ifs with ha
  · rw [map_wordA q p u v hu hv]
    exact congrArg p.onPoints (factor_a x ha)
  · rw [map_wordC q p u v hu hv]
    exact congrArg p.onPoints (factor_c x ((sl2FirstColumn_covers x).resolve_left ha))

private lemma liftPoints_c (q : Morphism Y Q) (p : Morphism (slVariety k 2) Q)
    (u v : Morphism (KPlus k) Y)
    (hu : q.comp u = p.comp standardSL2UpperMorphism)
    (hv : q.comp v = p.comp standardSL2LowerMorphism)
    (S : Subgroup (Variety.Point Y))
    (huS : ∀ t, u.onPoints t ∈ S) (hvS : ∀ t, v.onPoints t ∈ S)
    (hfinite : (((q.kernel ⊓ S) : Subgroup (Variety.Point Y)) :
      Set (Variety.Point Y)).Finite)
    (x : Variety.Point (slVariety k 2)) (hc : entry x 1 0 ≠ 0) :
    liftPoints u v x = wordC u v (entry x 0 0) (entry x 1 0) (entry x 1 1) := by
  unfold liftPoints
  split_ifs with ha
  · rw [words_agree q p u v hu hv S huS hvS hfinite _ _ _ ha hc]
    have hd := slPoint_det_eq_one 2 x
    rw [Matrix.det_fin_two] at hd
    change entry x 0 0 * entry x 1 1 - entry x 0 1 * entry x 1 0 = 1 at hd
    have he : (1+entry x 0 1*entry x 1 0)/entry x 0 0 = entry x 1 1 := by
      apply (div_eq_iff ha).mpr
      linear_combination -hd
    rw [he]
  · rfl

private lemma exists_regular_lift (q : Morphism Y Q) (p : Morphism (slVariety k 2) Q)
    (u v : Morphism (KPlus k) Y)
    (hu : q.comp u = p.comp standardSL2UpperMorphism)
    (hv : q.comp v = p.comp standardSL2LowerMorphism)
    (S : Subgroup (Variety.Point Y))
    (huS : ∀ t, u.onPoints t ∈ S) (hvS : ∀ t, v.onPoints t ∈ S)
    (hfinite : (((q.kernel ⊓ S) : Subgroup (Variety.Point Y)) :
      Set (Variety.Point Y)).Finite) :
    ∃ F : Variety.Morphism (slVariety k 2) Y, F.toFun = liftPoints u v := by
  apply Variety.Morphism.exists_of_sl2_principalOpen _ (chartA u v) (chartC u v)
  · intro x
    rw [chartA_apply, liftPoints_a]
    simpa only [entry, sl2FirstColumnPolynomial, Variety.principalOpenChartInclusion,
      evalPolynomial_X] using
      Variety.principalOpenChart_nonzero (sl2FirstColumnPolynomial 0) x
  · intro x
    rw [chartC_apply, liftPoints_c q p u v hu hv S huS hvS hfinite]
    simpa only [entry, sl2FirstColumnPolynomial, Variety.principalOpenChartInclusion,
      evalPolynomial_X] using
      Variety.principalOpenChart_nonzero (sl2FirstColumnPolynomial 1) x

omit [IsAlgClosed k] in
private lemma wordA_upper (u v : Morphism (KPlus k) Y) (t : k) :
    wordA u v 1 t 0 = u.onPoints (kPlusPoint t) := by
  simp only [wordA, zero_sub, sub_self, div_one, sub_add_cancel,
    show kPlusPoint (0 : k) = 1 from rfl, map_one, mul_one]
  rw [← map_mul, kPlusPoint_mul]
  simp [show kPlusPoint (0 : k) = 1 from rfl]

omit [IsAlgClosed k] in
private lemma wordA_lower (u v : Morphism (KPlus k) Y) (t : k) :
    wordA u v 1 0 t = v.onPoints (kPlusPoint t) := by
  simp only [wordA, sub_self, div_one, zero_sub, neg_add_cancel,
    show kPlusPoint (0 : k) = 1 from rfl, map_one, mul_one]
  rw [← map_mul, kPlusPoint_mul, sub_add_cancel]

private lemma liftPoints_upper (u v : Morphism (KPlus k) Y) (s : Variety.Point (KPlus k)) :
    liftPoints u v (standardSL2UpperMorphism.onPoints s) = u.onPoints s := by
  obtain ⟨t, rfl⟩ : ∃ t, kPlusPoint t = s := ⟨_, kPlusPoint_coordinate s⟩
  rw [liftPoints_a]
  · simpa [entry, standardSL2UpperRootIndex, Matrix.transvection,
      kPlus_coord] using wordA_upper u v t
  · simp [entry, standardSL2UpperRootIndex, Matrix.transvection]

private lemma liftPoints_lower (u v : Morphism (KPlus k) Y) (s : Variety.Point (KPlus k)) :
    liftPoints u v (standardSL2LowerMorphism.onPoints s) = v.onPoints s := by
  obtain ⟨t, rfl⟩ : ∃ t, kPlusPoint t = s := ⟨_, kPlusPoint_coordinate s⟩
  rw [liftPoints_a]
  · simpa [entry, standardSL2LowerRootIndex, Matrix.transvection,
      kPlus_coord] using wordA_lower u v t
  · simp [entry, standardSL2LowerRootIndex, Matrix.transvection]

private lemma liftPoints_one (u v : Morphism (KPlus k) Y) : liftPoints u v 1 = 1 := by
  simpa only [map_one] using liftPoints_upper u v 1

/-- Regular lifts of the two standard SL₂ root curves through a morphism with
finite kernel on their containing subgroup extend to a morphism from SL₂.
All three composition identities are literal identities of morphisms. -/
public theorem exists_sl2Morphism_of_finite_kernel_root_lifts
    (q : Morphism Y Q) (p : Morphism (slVariety k 2) Q)
    (u v : Morphism (KPlus k) Y)
    (hu : q.comp u = p.comp standardSL2UpperMorphism)
    (hv : q.comp v = p.comp standardSL2LowerMorphism)
    (S : Subgroup (Variety.Point Y))
    (huS : ∀ t, u.onPoints t ∈ S) (hvS : ∀ t, v.onPoints t ∈ S)
    (hfinite : (((q.kernel ⊓ S) : Subgroup (Variety.Point Y)) :
      Set (Variety.Point Y)).Finite) :
    ∃ F : Morphism (slVariety k 2) Y,
      F.comp standardSL2UpperMorphism = u ∧
      F.comp standardSL2LowerMorphism = v ∧ q.comp F = p := by
  obtain ⟨F, hF⟩ := exists_regular_lift q p u v hu hv S huS hvS hfinite
  have hFS (x) : F.toFun x ∈ S := by
    rw [hF]
    exact liftPoints_mem u v S huS hvS x
  have hFq (x) : q.onPoints (F.toFun x) = p.onPoints x := by
    rw [hF]
    exact liftPoints_proj q p u v hu hv x
  have hFone : F.toFun 1 = 1 := by rw [hF, liftPoints_one]
  have hFmul (x y) : F.toFun (x * y) = F.toFun x * F.toFun y := by
    let f := F.comp (mulMorphism (slVariety k 2))
    let g := mulMaps (F.comp (Variety.Morphism.fst _ _))
      (F.comp (Variety.Morphism.snd _ _))
    have he : f = g := by
      refine regular_maps_eq_of_finite_kernel
        (prod_connected (slVariety_isConnected 2) (slVariety_isConnected 2))
        q S hfinite _ _ ?_ ?_ ?_ ((Variety.prodPointEquiv _ _).symm (1, 1)) ?_
      · intro z
        exact hFS _
      · intro z
        exact S.mul_mem (hFS _) (hFS _)
      · intro z
        change q.onPoints (F.toFun ((Variety.prodPointEquiv _ _ z).1 *
            (Variety.prodPointEquiv _ _ z).2)) =
          q.onPoints (F.toFun (Variety.prodPointEquiv _ _ z).1 *
            F.toFun (Variety.prodPointEquiv _ _ z).2)
        rw [map_mul, hFq, hFq, hFq, map_mul]
      · change F.toFun (1 * 1) = F.toFun 1 * F.toFun 1
        rw [one_mul, hFone, mul_one]
    exact congrArg (fun m : Variety.Morphism
      (Variety.prod (slVariety k 2) (slVariety k 2)) Y =>
        m.toFun ((Variety.prodPointEquiv _ _).symm (x, y))) he
  refine ⟨⟨F, hFone, hFmul⟩, ?_, ?_, ?_⟩
  · apply Morphism.ext
    funext s
    change F.toFun (standardSL2UpperMorphism.onPoints s) = u.onPoints s
    rw [hF, liftPoints_upper]
  · apply Morphism.ext
    funext s
    change F.toFun (standardSL2LowerMorphism.onPoints s) = v.onPoints s
    rw [hF, liftPoints_lower]
  · apply Morphism.ext
    exact funext hFq

end BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts.CentralLifting
end Theory.AlgebraicGroup
