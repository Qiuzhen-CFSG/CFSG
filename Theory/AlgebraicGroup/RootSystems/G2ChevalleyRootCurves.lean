module

public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyCarrier
public import Theory.AlgebraicGroup.RootSubgroups.Defs

/-!
# Root curves for the closed G2 Chevalley carrier

This module realizes each of the twelve integral G2 root curves as a closed
one-parameter subgroup of the closed Chevalley carrier.  Conjugation by the
rank-two split torus scales the root parameter by the corresponding Laurent
character.  The twelve characters are recorded explicitly in simple-coroot
coordinates, and each curve is packaged with `IsTorusRootSubgroup` and
`RootWeightEquation` witnesses.

The conjugation calculation first verifies, over the integral sparse tables,
that every nonzero entry of the `n`th divided power has weight `n` times the
root.  Diagonal conjugation then scales each of the four terms in the cubic
root curve.  No division occurs in the coefficient field, so the argument is
valid in characteristics two and three as well as in all other
characteristics.  A distinguished matrix entry recovers the root parameter;
its polynomial coordinate proves that each root morphism is a closed
embedding onto its image.

The construction uses the integral Chevalley representation and the split
torus isomorphism from `G2ChevalleyCarrier`.  It follows the standard integral
Chevalley-basis construction described by Steinberg, *Lectures on Chevalley
Groups*, Theorem 1, and does not use root classification or center results.
-/

open scoped BigOperators Matrix

open Theory AlgebraicGroup

namespace Theory.AlgebraicGroup.G2Chevalley

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

public def rootWeightExponent (r : Root) : Fin 2 → ℤ :=
  r.pairingSimple

public lemma rootWeightExponent_values :
    rootWeightExponent Root.short = ![2, -1] ∧
    rootWeightExponent Root.long = ![-3, 2] ∧
    rootWeightExponent Root.shortLong = ![-1, 1] ∧
    rootWeightExponent Root.twoShortLong = ![1, 0] ∧
    rootWeightExponent Root.threeShortLong = ![3, -1] ∧
    rootWeightExponent Root.threeShortTwoLong = ![0, 1] ∧
    rootWeightExponent Root.negShort = ![-2, 1] ∧
    rootWeightExponent Root.negLong = ![3, -2] ∧
    rootWeightExponent Root.negShortLong = ![1, -1] ∧
    rootWeightExponent Root.negTwoShortLong = ![-1, 0] ∧
    rootWeightExponent Root.negThreeShortLong = ![-3, 1] ∧
    rootWeightExponent Root.negThreeShortTwoLong = ![0, -1] := by
  repeat' apply And.intro
  all_goals
    funext i
    fin_cases i <;>
      norm_num [rootWeightExponent, Root.pairingSimple, Root.coord,
        Root.short, Root.long, Root.shortLong, Root.twoShortLong,
        Root.threeShortLong, Root.threeShortTwoLong, Root.negShort,
        Root.negLong, Root.negShortLong, Root.negTwoShortLong,
        Root.negThreeShortLong, Root.negThreeShortTwoLong]

public noncomputable def rootScale (u : TorusParameter k) (r : Root) : kˣ :=
  ∏ i : Fin 2, u i ^ rootWeightExponent r i

private def decidableForallFin {n : ℕ} (p : Fin n → Prop)
    (d : ∀ i, Decidable (p i)) : Decidable (∀ i, p i) :=
  @Fintype.decidableForallFintype (Fin n) p d inferInstance

private def supportWeightRootDecidable (r : Root) : Decidable
    (∀ (n : Fin 4) (i j : Basis),
      rootDividedPower r n i j ≠ 0 →
        ∀ q : Fin 2, basisWeight i q - basisWeight j q =
          (n.val : ℤ) * rootWeightExponent r q) :=
  decidableForallFin (fun n : Fin 4 =>
      ∀ (i j : Basis), rootDividedPower r n i j ≠ 0 →
        ∀ q : Fin 2, basisWeight i q - basisWeight j q =
          (n.val : ℤ) * rootWeightExponent r q) (fun n =>
      decidableForallFin (fun i : Basis =>
        ∀ j : Basis, rootDividedPower r n i j ≠ 0 →
          ∀ q : Fin 2, basisWeight i q - basisWeight j q =
            (n.val : ℤ) * rootWeightExponent r q) (fun i =>
        decidableForallFin (fun j : Basis =>
          rootDividedPower r n i j ≠ 0 →
            ∀ q : Fin 2, basisWeight i q - basisWeight j q =
              (n.val : ℤ) * rootWeightExponent r q) (fun j => by
          by_cases hzero : rootDividedPower r n i j = 0
          · exact isTrue (fun hne => (hne hzero).elim)
          · exact match decidableForallFin
                (fun q : Fin 2 => basisWeight i q - basisWeight j q =
                  (n.val : ℤ) * rootWeightExponent r q)
                (fun _ => inferInstance) with
            | isTrue h => isTrue (fun _ => h)
            | isFalse h => isFalse (fun hall => h (hall hzero)))))

private lemma rootDividedPower_support_weight :
    ∀ (r : Root) (n : Fin 4) (i j : Basis),
      rootDividedPower r n i j ≠ 0 →
        ∀ q : Fin 2, basisWeight i q - basisWeight j q =
          (n.val : ℤ) * rootWeightExponent r q := by
  intro r
  fin_cases r <;>
    exact @of_decide_eq_true _ (supportWeightRootDecidable _) (by decide)

omit [IsAlgClosed k] in
private lemma basisTorusUnit_ratio (u : TorusParameter k) (r : Root)
    (n : Fin 4) (i j : Basis)
    (hweight : ∀ q : Fin 2, basisWeight i q - basisWeight j q =
      (n.val : ℤ) * rootWeightExponent r q) :
    (basisTorusUnit u i)⁻¹ * basisTorusUnit u j =
      (rootScale u r) ^ n.val := by
  simp only [basisTorusUnit, rootScale]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro q hq
  rw [← zpow_neg, ← zpow_add]
  rw [show - -basisWeight i q + -basisWeight j q =
      (n.val : ℤ) * rootWeightExponent r q by
        have h := hweight q
        omega]
  rw [zpow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 1
  exact mul_comm _ _

omit [IsAlgClosed k] in
private lemma rootDividedPower_torus_entry
    (u : TorusParameter k) (r : Root) (n : Fin 4) (i j : Basis) :
    ((basisTorusUnit u i)⁻¹ : kˣ) *
          (specialize (R := k) (rootDividedPower r n) i j) *
          (basisTorusUnit u j : kˣ) =
      ((rootScale u r : k) ^ n.val) *
        specialize (R := k) (rootDividedPower r n) i j := by
  by_cases hzero : rootDividedPower r n i j = 0
  · simp [specialize, hzero]
  · have hratio : (basisTorusUnit u i)⁻¹ * basisTorusUnit u j =
        (rootScale u r) ^ n.val :=
      basisTorusUnit_ratio u r n i j
        (rootDividedPower_support_weight r n i j hzero)
    have hratioVal : (((basisTorusUnit u i)⁻¹ : kˣ) : k) *
        ((basisTorusUnit u j : kˣ) : k) =
          (rootScale u r : k) ^ n.val := by
      simpa using congrArg Units.val hratio
    change (((basisTorusUnit u i)⁻¹ : kˣ) : k) *
            (rootDividedPower r n i j : k) *
            ((basisTorusUnit u j : kˣ) : k) = _
    calc
      (((basisTorusUnit u i)⁻¹ : kˣ) : k) *
            (rootDividedPower r n i j : k) *
            ((basisTorusUnit u j : kˣ) : k) =
          ((((basisTorusUnit u i)⁻¹ : kˣ) : k) *
            ((basisTorusUnit u j : kˣ) : k)) *
              (rootDividedPower r n i j : k) := by ring
      _ = ((rootScale u r : k) ^ n.val) *
            (rootDividedPower r n i j : k) := by rw [hratioVal]

omit [IsAlgClosed k] in
private lemma rootDividedPower_torus_entry_mul
    (u : TorusParameter k) (r : Root) (n : Fin 4) (i j : Basis) (c : k) :
    ((((basisTorusUnit u i)⁻¹ : kˣ) : k) *
          (c * specialize (R := k) (rootDividedPower r n) i j)) *
          ((basisTorusUnit u j : kˣ) : k) =
      c * (((rootScale u r : k) ^ n.val) *
        specialize (R := k) (rootDividedPower r n) i j) := by
  rw [show ((((basisTorusUnit u i)⁻¹ : kˣ) : k) *
          (c * specialize (R := k) (rootDividedPower r n) i j)) *
          ((basisTorusUnit u j : kˣ) : k) =
      c * ((((basisTorusUnit u i)⁻¹ : kˣ) : k) *
        specialize (R := k) (rootDividedPower r n) i j *
        ((basisTorusUnit u j : kˣ) : k)) by ring]
  rw [rootDividedPower_torus_entry]

public noncomputable def rootWeight (r : Root) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    TorusWeight (splitTorus (k := k)) := by
  letI := (splitTorus (k := k)).carrierAlgebraicGroup
  exact splitTorusCharacter (k := k) (rootWeightExponent r)

/-- Pulling an explicit root weight back along the split-torus coordinates
recovers its Laurent exponent vector. -/
public lemma rootWeight_comp_splitTorusIso (r : Root) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (rootWeight (k := k) r).comp (splitTorusIso (k := k)).hom =
      dLaurentCharacter (k := k) 2 (rootWeightExponent r) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  apply AlgebraicGroup.Morphism.ext
  funext x
  change (dLaurentCharacter (k := k) 2 (rootWeightExponent r)).toVariety.toFun
      ((splitTorusIso (k := k)).inv.onPoints
        ((splitTorusIso (k := k)).hom.onPoints x)) =
    (dLaurentCharacter (k := k) 2 (rootWeightExponent r)).toVariety.toFun x
  rw [(splitTorusIso (k := k)).hom_inv_id]

public lemma rootWeight_pointCharacter (r : Root)
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (rootWeight (k := k) r).pointCharacter s =
      (rootScale
        (dPointEquiv 2 ((splitTorusIso (k := k)).inv.onPoints s)) r : k) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  change (dPointEquiv 1
      ((splitTorusCharacter (k := k) (rootWeightExponent r)).onPoints s) 0 : k) =
    ((∏ q : Fin 2,
      (dPointEquiv 2 ((splitTorusIso (k := k)).inv.onPoints s) q) ^
        rootWeightExponent r q : kˣ) : k)
  exact congrArg Units.val
    (splitTorusCharacter_apply_point (k := k) (rootWeightExponent r) s)

omit [IsAlgClosed k] in
public lemma rootCurveUnit_torus_conjugation
    (u : TorusParameter k) (r : Root) (t : k) :
    (torusElement u)⁻¹ * rootCurveUnit r t * torusElement u =
      rootCurveUnit r ((rootScale u r : k) * t) := by
  apply Units.ext
  change Matrix.diagonal
        (fun b : Basis => (((basisTorusUnit u b)⁻¹ : kˣ) : k)) *
      rootCurve r t *
      Matrix.diagonal (fun b : Basis => ((basisTorusUnit u b : kˣ) : k)) =
    rootCurve r ((rootScale u r : k) * t)
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [rootCurve, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [mul_add, mul_add, mul_add, add_mul, add_mul, add_mul]
  rw [rootDividedPower_torus_entry_mul u r 1 i j t,
    rootDividedPower_torus_entry_mul u r 2 i j (t ^ 2),
    rootDividedPower_torus_entry_mul u r 3 i j (t ^ 3)]
  by_cases hij : i = j
  · subst j
    simp
    ring
  · simp [hij]
    ring

private def rootRecoveryRow : Root → Basis
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 8
  | 4 => 1
  | 5 => 3
  | 6 => 0
  | 7 => 1
  | 8 => 0
  | 9 => 11
  | 10 => 1
  | 11 => 0

private def rootRecoveryColumn : Root → Basis
  | 0 => 8
  | 1 => 9
  | 2 => 10
  | 3 => 12
  | 4 => 12
  | 5 => 12
  | 6 => 2
  | 7 => 3
  | 8 => 4
  | 9 => 0
  | 10 => 6
  | 11 => 7

private def rootRecoverySign : Root → ℤ
  | 6 => -1
  | 7 => -1
  | _ => 1

omit [IsAlgClosed k] in
private lemma rootCurve_recovery (r : Root) (t : k) :
    (rootRecoverySign r : k) *
        rootCurve r t (rootRecoveryRow r) (rootRecoveryColumn r) = t := by
  fin_cases r <;>
    simp [rootRecoverySign, rootRecoveryRow, rootRecoveryColumn, rootCurve,
      rootDividedPower, rootOperator, rootOperatorEntries,
      rootDividedPowerTwoEntries, rootDividedPowerThreeEntries,
      specialize, matrixOfEntries]

private noncomputable def carrierMatrixCoordinate (i j : Basis) :
    Variety.PolynomialFunction (Carrier (k := k)) :=
  Variety.PolynomialFunction.pullback
    (ambientClosedCarrier (k := k)).inclusion.toVariety
    (generalLinearMatrixCoordinate (k := k)
      (Module.finrank k (Basis → k))
      (carrierIndexEquiv (k := k) i) (carrierIndexEquiv (k := k) j))

private lemma carrierMatrixCoordinate_rootMorphism_apply
    (r : Root) (i j : Basis) (x : Variety.Point (KPlus k)) :
    carrierMatrixCoordinate (k := k) i j ((rootMorphism r).onPoints x) =
      rootCurve r (x.val PUnit.unit) i j := by
  change generalLinearMatrixCoordinate (k := k)
      (Module.finrank k (Basis → k))
      (carrierIndexEquiv (k := k) i) (carrierIndexEquiv (k := k) j)
      ((ambientClosedCarrier (k := k)).inclusion.onPoints
        ((rootMorphism r).onPoints x)) = _
  rw [rootMorphism_inclusion_apply, generalLinearMatrixCoordinate_apply,
    rootAmbientMorphism_apply, generalLinearRepresentationPoint_matrix]
  simp [rootPointRepresentation, carrierBasis, Module.Basis.reindex_apply]
  rfl

private noncomputable def carrierRootRecovery (r : Root) :
    Variety.PolynomialFunction (Carrier (k := k)) :=
  algebraMap k (Variety.PolynomialFunction (Carrier (k := k)))
      (rootRecoverySign r : k) *
    carrierMatrixCoordinate (k := k) (rootRecoveryRow r) (rootRecoveryColumn r)

private lemma carrierRootRecovery_rootMorphism_apply
    (r : Root) (x : Variety.Point (KPlus k)) :
    carrierRootRecovery (k := k) r ((rootMorphism r).onPoints x) =
      x.val PUnit.unit := by
  dsimp only [carrierRootRecovery, Variety.PolynomialFunction.toFun,
    Subring.coe_mul, Pi.mul_apply]
  change (algebraMap k (Variety.PolynomialFunction (Carrier (k := k)))
      (rootRecoverySign r : k)).toFun ((rootMorphism r).onPoints x) *
        (carrierMatrixCoordinate (k := k) (rootRecoveryRow r)
          (rootRecoveryColumn r)).toFun ((rootMorphism r).onPoints x) = _
  rw [polynomialFunction_algebraMap_apply]
  rw [carrierMatrixCoordinate_rootMorphism_apply, rootCurve_recovery]

public lemma rootMorphism_injective (r : Root) :
    Function.Injective (rootMorphism (k := k) r).onPoints := by
  intro x y hxy
  apply (additiveGroupPointEquiv k).injective
  change x.val PUnit.unit = y.val PUnit.unit
  rw [← carrierRootRecovery_rootMorphism_apply r x,
    ← carrierRootRecovery_rootMorphism_apply r y, hxy]

public lemma rootMorphism_coordinate_preimage (r : Root) :
    ∀ c : (KPlus k).Coordinates,
      ∃ q : Variety.PolynomialFunction (Carrier (k := k)),
        Variety.PolynomialFunction.pullback (rootMorphism r).toVariety q =
          Variety.PolynomialFunction.ofPolynomial (KPlus k) (MvPolynomial.X c) := by
  intro c
  refine ⟨carrierRootRecovery (k := k) r, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  change carrierRootRecovery (k := k) r ((rootMorphism r).onPoints x) =
    evalPolynomial x.val (MvPolynomial.X c)
  rw [carrierRootRecovery_rootMorphism_apply, evalPolynomial_X]

@[expose]
public noncomputable def rootSubgroup (r : Root) : ClosedSubgroup (Carrier (k := k)) :=
  (rootMorphism r).imageClosedSubgroup

public noncomputable def rootParametrization (r : Root) :
    @OneParameterParametrization k _
      (rootSubgroup (k := k) r).carrierVariety
      (rootSubgroup (k := k) r).carrierAlgebraicGroup :=
  Classical.choose ((rootMorphism r).iso_imageClosedSubgroup_of_coordinate_preimage
    (rootMorphism_injective r) (rootMorphism_coordinate_preimage r))

public lemma rootSubgroup_isOneParameter (r : Root) :
    @IsOneParameterGroup k _
      (rootSubgroup (k := k) r).carrierVariety
      (rootSubgroup (k := k) r).carrierAlgebraicGroup :=
  ⟨rootParametrization r⟩

public lemma rootParametrization_hom (r : Root) :
    @AlgebraicGroup.Iso.hom k _ (KPlus k)
        (rootSubgroup (k := k) r).carrierVariety
        (inferInstance : AlgebraicGroup (KPlus k))
        (rootSubgroup (k := k) r).carrierAlgebraicGroup
        (rootParametrization (k := k) r) =
      (rootMorphism r).codRestrictClosedSubgroup
        (rootSubgroup (k := k) r) (fun y => ⟨y, rfl⟩) :=
  Classical.choose_spec
    ((rootMorphism r).iso_imageClosedSubgroup_of_coordinate_preimage
      (rootMorphism_injective r) (rootMorphism_coordinate_preimage r))

public lemma rootParametrization_include_value (r : Root) (a : k) :
    (rootSubgroup (k := k) r).includePoint
        (@OneParameterParametrization.value k _
          (rootSubgroup (k := k) r).carrierVariety
          (rootSubgroup (k := k) r).carrierAlgebraicGroup
          (rootParametrization r) a) =
      (rootMorphism r).onPoints (kPlusPoint a) := by
  let _ : AlgebraicGroup (rootSubgroup (k := k) r).carrierVariety :=
    (rootSubgroup (k := k) r).carrierAlgebraicGroup
  change (rootSubgroup (k := k) r).inclusion.onPoints
      ((@AlgebraicGroup.Iso.hom k _ (KPlus k)
          (rootSubgroup (k := k) r).carrierVariety
          (inferInstance : AlgebraicGroup (KPlus k))
          (rootSubgroup (k := k) r).carrierAlgebraicGroup
          (rootParametrization r)).onPoints (kPlusPoint a)) = _
  rw [rootParametrization_hom]
  exact (rootMorphism r).codRestrictClosedSubgroup_inclusion_apply
    (rootSubgroup (k := k) r) (fun y => ⟨y, rfl⟩) (kPlusPoint a)

private noncomputable def ambientRepresentationPointHom :
    LinearMap.GeneralLinearGroup k (Basis → k) →*
      Variety.Point (Ambient k) where
  toFun g := generalLinearRepresentationPoint (carrierBasis (k := k)) g
  map_one' := by
    simpa [Ambient, glVarietyOf] using
      generalLinearRepresentationPoint_one (carrierBasis (k := k))
  map_mul' g h := by
    simpa [Ambient, glVarietyOf] using
      generalLinearRepresentationPoint_mul (carrierBasis (k := k)) g h

private lemma rootMorphism_ambient_point (r : Root) (a : k) :
    (ambientClosedCarrier (k := k)).inclusion.onPoints
        ((rootMorphism r).onPoints (kPlusPoint a)) =
      ambientRepresentationPointHom
        (Matrix.GeneralLinearGroup.toLin (rootCurveUnit r a)) := by
  rw [rootMorphism_inclusion_apply, rootAmbientMorphism_apply]
  rfl

private lemma splitTorus_ambient_point
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    (ambientClosedCarrier (k := k)).inclusion.onPoints
        ((splitTorus (k := k)).includePoint s) =
      ambientRepresentationPointHom
        (Matrix.GeneralLinearGroup.toLin
          (torusElement
            (dPointEquiv 2 ((splitTorusIso (k := k)).inv.onPoints s)))) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  exact splitTorus_inclusion_torusElement_apply s

public lemma rootMorphism_splitTorus_conjugation (r : Root) (a : k)
    (s : Variety.Point (splitTorus (k := k)).carrierVariety) :
    letI := (splitTorus (k := k)).carrierAlgebraicGroup
    ((splitTorus (k := k)).includePoint s)⁻¹ *
          (rootMorphism r).onPoints (kPlusPoint a) *
          (splitTorus (k := k)).includePoint s =
      (rootMorphism r).onPoints
        (kPlusPoint ((rootWeight (k := k) r).pointCharacter s * a)) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  simp only [map_mul, map_inv]
  rw [splitTorus_ambient_point, rootMorphism_ambient_point,
    rootMorphism_ambient_point, rootWeight_pointCharacter]
  let ρ := ambientRepresentationPointHom (k := k)
  change (ρ _)⁻¹ * ρ _ * ρ _ = ρ _
  rw [← ρ.map_inv, ← ρ.map_mul, ← ρ.map_mul]
  congr 1
  simpa only [map_mul, map_inv] using
    congrArg Matrix.GeneralLinearGroup.toLin
      (rootCurveUnit_torus_conjugation
        (dPointEquiv 2 ((splitTorusIso (k := k)).inv.onPoints s)) r a)

public lemma rootSubgroup_invariant (r : Root) :
    IsClosedSubgroupInvariant (splitTorus (k := k)) (rootSubgroup (k := k) r) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  intro t ht x hx
  let s : Variety.Point (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).pointEquiv.symm ⟨t, ht⟩
  have hs : (splitTorus (k := k)).includePoint s = t := by
    change ((splitTorus (k := k)).pointEquiv s).val = t
    simp [s]
  change x ∈ (rootMorphism r).image at hx
  rcases hx with ⟨q, rfl⟩
  have qeq : q = kPlusPoint (q.val PUnit.unit) := by
    apply (additiveGroupPointEquiv k).injective
    rfl
  rw [qeq, ← hs, rootMorphism_splitTorus_conjugation]
  exact ⟨kPlusPoint ((rootWeight (k := k) r).pointCharacter s *
    q.val PUnit.unit), rfl⟩

public lemma rootWeightEquation (r : Root) :
    RootWeightEquation (splitTorus (k := k)) (rootSubgroup (k := k) r)
      (rootWeight (k := k) r) := by
  intro y t s
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  let _ : AlgebraicGroup (rootSubgroup (k := k) r).carrierVariety :=
    (rootSubgroup (k := k) r).carrierAlgebraicGroup
  let p := rootParametrization (k := k) r
  rcases oneParameterParametrization_eq_rescale p y with ⟨c, hc, _⟩
  rw [show (rootSubgroup (k := k) r).includePoint (y.value t) =
      (rootMorphism r).onPoints (kPlusPoint (c * t)) by
        rw [hc.2, rootParametrization_include_value]]
  rw [show (rootSubgroup (k := k) r).includePoint
        (y.value ((rootWeight (k := k) r).pointCharacter s * t)) =
      (rootMorphism r).onPoints
        (kPlusPoint (c * ((rootWeight (k := k) r).pointCharacter s * t))) by
        rw [hc.2, rootParametrization_include_value]]
  rw [rootMorphism_splitTorus_conjugation]
  exact congrArg
    (fun z : k => (rootMorphism r).onPoints (kPlusPoint z)) (by ring)

public lemma rootSubgroup_isTorusRootSubgroup (r : Root) :
    IsTorusRootSubgroup (splitTorus (k := k)) (rootSubgroup (k := k) r) :=
  ⟨rootSubgroup_invariant r, rootSubgroup_isOneParameter r⟩

public theorem rootSubgroup_package (r : Root) :
    IsTorusRootSubgroup (splitTorus (k := k)) (rootSubgroup (k := k) r) ∧
      RootWeightEquation (splitTorus (k := k)) (rootSubgroup (k := k) r)
        (rootWeight (k := k) r) :=
  ⟨rootSubgroup_isTorusRootSubgroup r, rootWeightEquation r⟩

end Theory.AlgebraicGroup.G2Chevalley
