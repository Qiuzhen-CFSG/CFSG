module

public import Theory.AlgebraicGroup.Borel.PositiveRootSupportGeometry.RegularCocharacter.Limit
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Mathlib.Algebra.Polynomial.Roots

/-!
Testing cocharacter limits on actual root curves.

The conjugation equation turns the curve into the monomial `t` raised to the
integral character--cocharacter pairing. Nonnegative exponents extend. For the
converse, a polynomial function on the ambient group restricts to the parameter
on the closed root curve; pulling it back along a proposed extension excludes
negative exponents by evaluation at zero. This works in every characteristic.
A centralizer equal to the torus excludes zero exponents for nontrivial roots.

Source: Borel, *Linear Algebraic Groups*, IV, 13.3, 13.14(4), 13.18(5)(b--d).
The actual equation here is inverse conjugation, exactly as in GLS3, 1.9.2.
-/

universe u

namespace Theory.AlgebraicGroup.BorelCocharacter

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

private lemma nonneg_of_polynomial_zpow
    (p : Polynomial k) (m : ℤ)
    (hp : ∀ t : k, t ≠ 0 → p.eval t = t ^ m) : 0 ≤ m := by
  by_contra hm
  have hmneg : m < 0 := lt_of_not_ge hm
  let n := (-m).toNat
  have hn : (n : ℤ) = -m := Int.toNat_of_nonneg (by omega)
  have hnpos : 0 < n := by omega
  have heq : p * Polynomial.X ^ n = 1 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.finite_singleton (0 : k)).infinite_compl.mono
    intro t ht
    have ht0 : t ≠ 0 := ht
    simp only [Set.mem_ofPred_eq, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    rw [hp t ht0, ← zpow_natCast, hn, ← zpow_add₀ ht0]
    simp
  have hzero := congrArg (Polynomial.eval (0 : k)) heq
  simp [hnpos.ne'] at hzero

private def powerCurve (a : k) (n : ℕ) :
    Variety.Morphism (KPlus k) (KPlus k) where
  toFun := fun t => kPlusPoint (t.val PUnit.unit ^ n * a)
  regular := by
    intro i
    refine ⟨MvPolynomial.X PUnit.unit ^ n * MvPolynomial.C a, ?_⟩
    intro t
    simp [evalPolynomial, kPlusPoint, additiveGroupPointEquiv]
    rfl

/-- A nonnegative pairing gives a polynomial extension of every point of the
root curve, using the monomial with that exponent. -/
public theorem root_value_hasLimit_of_nonneg
    {X : ClosedSubgroup G} {χ : TorusWeight T}
    (hχ : RootWeightEquation T X χ)
    (x : OneParameterParametrization X.carrierVariety)
    (c : ClosedSubgroupTorusCocharacter T)
    (hm : 0 ≤ characterCocharacterPairing T c (Additive.ofMul χ)) (a : k) :
    HasLimit c (X.includePoint (x.value a)) := by
  let m := characterCocharacterPairing T c (Additive.ofMul χ)
  refine ⟨(X.inclusion.comp x.hom).toVariety.comp (powerCurve a m.toNat), ?_⟩
  intro t
  rw [hχ x a (c.onPoints t), characterCocharacterPairing_spec T χ c t]
  change X.includePoint (x.value ((dPointEquiv 1 t 0 : k) ^ m.toNat * a)) = _
  rw [← zpow_natCast, Int.toNat_of_nonneg hm]

/-- An extension of a nonidentity root point forces a nonnegative pairing.
An ambient polynomial recovering the root parameter excludes a pole at zero. -/
public theorem nonneg_of_root_value_one_hasLimit
    {X : ClosedSubgroup G} {χ : TorusWeight T}
    (hχ : RootWeightEquation T X χ)
    (x : OneParameterParametrization X.carrierVariety)
    (c : ClosedSubgroupTorusCocharacter T)
    (hlim : HasLimit c (X.includePoint (x.value 1))) :
    0 ≤ characterCocharacterPairing T c (Additive.ofMul χ) := by
  obtain ⟨f, hf⟩ := hlim
  obtain ⟨F, hF⟩ := oneParameterParametrization_exists_ambient_parameterPolynomial X x
  obtain ⟨p, hp⟩ := (Variety.PolynomialFunction.pullback f F).representedBy
  let P := MvPolynomial.uniqueAlgEquiv k PUnit p
  apply nonneg_of_polynomial_zpow P
  intro a ha
  let t : Variety.Point (KMult k) :=
    (dPointEquiv 1).symm (fun _ => Units.mk0 a ha)
  have ht : (dPointEquiv 1 t 0 : k) = a := by
    simp [t]
  have heval : P.eval a = F (f.toFun (kPlusPoint a)) := by
    change P.eval a = (Variety.PolynomialFunction.pullback f F).toFun (kPlusPoint a)
    rw [hp]
    change P.eval a = MvPolynomial.eval₂ (RingHom.id k) (fun _ => a) p
    rw [← MvPolynomial.eval₂_const_uniqueAlgEquiv]
    rfl
  rw [← ht, hf, hχ x 1 (c.onPoints t), hF, mul_one,
    characterCocharacterPairing_spec T χ c t] at heval
  exact heval.trans (by rw [ht])

/-- A root subgroup is contained in the actual limit subgroup precisely when
its character pairs nonnegatively with the cocharacter. -/
public theorem rootSubgroup_hasLimit_iff_nonneg
    {X : ClosedSubgroup G} {χ : TorusWeight T}
    (hX : IsTorusRootSubgroup T X) (hχ : RootWeightEquation T X χ)
    (c : ClosedSubgroupTorusCocharacter T) :
    (∀ g, g ∈ X → HasLimit c g) ↔
      0 ≤ characterCocharacterPairing T c (Additive.ofMul χ) := by
  obtain ⟨x⟩ := hX.2
  constructor
  · intro h
    exact nonneg_of_root_value_one_hasLimit hχ x c
      (h _ (X.pointEquiv (x.value 1)).property)
  · intro hm g hg
    let y := X.pointEquiv.symm ⟨g, hg⟩
    let a := Multiplicative.toAdd (additiveGroupPointEquiv k (x.inv.onPoints y))
    have hxa : X.includePoint (x.value a) = g := by
      change X.includePoint (x.hom.onPoints (kPlusPoint a)) = g
      rw [show kPlusPoint a = x.inv.onPoints y from kPlusPoint_coordinate _, x.inv_hom_id]
      exact congrArg Subtype.val (X.pointEquiv.apply_symm_apply ⟨g, hg⟩)
    rw [← hxa]
    exact root_value_hasLimit_of_nonneg hχ x c hm a

/-- A nontrivial root character cannot have zero pairing when only torus
elements centralize the cocharacter. A fixed root point would lie in the torus
and commute with it, forcing its character to be trivial. -/
public theorem pairing_ne_zero_of_centralizesOnlyTorus
    (hT : IsSubtorus T) {X : ClosedSubgroup G} {χ : TorusWeight T}
    (hX : IsTorusRootSubgroup T X) (hχ : RootWeightEquation T X χ)
    (hne : χ ≠ 1) (c : ClosedSubgroupTorusCocharacter T)
    (hc : CentralizesOnlyTorus c) :
    characterCocharacterPairing T c (Additive.ofMul χ) ≠ 0 := by
  intro hzero
  obtain ⟨x⟩ := hX.2
  obtain ⟨F, hF⟩ := oneParameterParametrization_exists_ambient_parameterPolynomial X x
  let g := X.includePoint (x.value 1)
  have hg : g ∈ T := by
    apply hc
    intro t
    change (T.includePoint (c.onPoints t))⁻¹ * X.includePoint (x.value 1) * _ = _
    rw [hχ x 1, characterCocharacterPairing_spec T χ c, hzero, zpow_zero, one_mul]
  let y := T.pointEquiv.symm ⟨g, hg⟩
  have hy : T.includePoint y = g :=
    congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨g, hg⟩)
  apply hne
  apply TorusCharacter.pointCharacter_injective
  ext s
  have hcomm : g * T.includePoint s = T.includePoint s * g := by
    have h := congrArg T.inclusion.onPoints
      (isMulCommutative_iff.mp hT.isMulCommutative y s)
    simp only [map_mul] at h
    change T.includePoint y * T.includePoint s = T.includePoint s * T.includePoint y at h
    rwa [hy] at h
  have hconj : (T.includePoint s)⁻¹ * g * T.includePoint s = g := by
    rw [mul_assoc, hcomm, inv_mul_cancel_left]
  have heq := congrArg F ((hχ x 1 s).symm.trans hconj)
  change χ.pointCharacter s = 1
  simpa only [mul_one, g, hF] using heq


end Theory.AlgebraicGroup.BorelCocharacter
