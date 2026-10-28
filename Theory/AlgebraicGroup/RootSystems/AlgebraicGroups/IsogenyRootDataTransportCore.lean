module

public import Theory.AlgebraicGroup.Borel.AdjointCenter
public import Theory.AlgebraicGroup.Borel.IsogenyImage
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.AdditivePolynomialDegree
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Theory.AlgebraicGroup.RootSubgroups.Generation
public import Theory.AlgebraicGroup.Tori.Character.Operations

universe u

/-!
This file isolates the lower-layer transport interface for realized root data
under an isogeny.  Such an isogeny is only point-surjective with finite point
kernel, so in positive characteristic it may be inseparable.  In particular,
its restriction to a root subgroup is described by a nonzero additive
polynomial, not necessarily by a linear rescaling.  The degree of that
polynomial is a power of the field characteristic and gives the root-character
scale.

`IsogenyRootImageWitness` records this additive-polynomial parameter map and
proves the scaled character-pullback formula.  `IsogenyRootDataTransport` also
records the (possibly different) coroot scale.  Character--cocharacter
evaluation then gives the cross-multiplied Cartan identity
`q_alpha * <alpha,beta> = q_beta * <alpha',beta'>`.  Exact character and pairing
transport are exposed only under an explicit scale-one certificate.  This is
the form needed for central quotients such as `SL -> PSL`, while remaining
correct for Frobenius and exceptional inseparable isogenies.  The geometric
construction of root-image witnesses is kept separate from this algebraic
transport core.
-/

namespace Theory.AlgebraicGroup

set_option linter.style.haveILetI false

variable {k : Type u} [Field k] [IsAlgClosed k]

section ImageTorus

/- The morphism from a torus to its closed image under an ambient morphism. -/
public noncomputable def isogenyImageTorusMorphism
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (T : ClosedSubgroup K) :
    AlgebraicGroup.Morphism T.carrierVariety
      (φ.comp T.inclusion).imageClosedSubgroup.carrierVariety := by
  letI : AlgebraicGroup
      (φ.comp T.inclusion).imageClosedSubgroup.carrierVariety :=
    (φ.comp T.inclusion).imageClosedSubgroup.carrierAlgebraicGroup
  exact (φ.comp T.inclusion).codRestrictClosedSubgroup _ (by
    intro x
    change (φ.comp T.inclusion).onPoints x ∈
      (φ.comp T.inclusion).image
    exact ⟨x, rfl⟩)

public theorem isogenyImageTorusMorphism_surjective
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (T : ClosedSubgroup K) :
    Function.Surjective
      (isogenyImageTorusMorphism φ T).onPoints := by
  letI : AlgebraicGroup
      (φ.comp T.inclusion).imageClosedSubgroup.carrierVariety :=
    (φ.comp T.inclusion).imageClosedSubgroup.carrierAlgebraicGroup
  exact (φ.comp T.inclusion).codRestrictImageClosedSubgroup_surjective (by
    intro x
    change (φ.comp T.inclusion).onPoints x ∈
      (φ.comp T.inclusion).image
    exact ⟨x, rfl⟩)

public theorem isogenyImageTorus_isMaximalTorus
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (hφ : IsIsogeny φ)
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T) :
    IsMaximalTorus (φ.comp T.inclusion).imageClosedSubgroup :=
  isogeny_image_isMaximalTorus φ hφ T hT

end ImageTorus

section ImageWitness

omit [IsAlgClosed k] in
/-- A morphism between two parametrized one-parameter groups is represented by
a polynomial in the chosen additive coordinates. -/
public theorem oneParameterMorphism_exists_polynomial
    {X Y : Variety k} [AlgebraicGroup X] [AlgebraicGroup Y]
    (source : OneParameterParametrization X)
    (target : OneParameterParametrization Y)
    (f : AlgebraicGroup.Morphism X Y) :
    ∃ p : Polynomial k, ∀ t : k,
      f.onPoints (source.value t) = target.value (p.eval t) := by
  let coordinateMorphism : AlgebraicGroup.Morphism (KPlus k) (KPlus k) :=
    target.inv.comp (f.comp source.hom)
  obtain ⟨p, hp⟩ := coordinateMorphism.toVariety.regular PUnit.unit
  let polynomial : Polynomial k := MvPolynomial.uniqueAlgEquiv k PUnit p
  refine ⟨polynomial, ?_⟩
  intro t
  have hcoordinate :
      coordinateMorphism.onPoints (kPlusPoint t) =
        kPlusPoint (polynomial.eval t) := by
    apply Variety.Point.ext
    funext i
    cases i
    change (coordinateMorphism.toVariety.toFun (kPlusPoint t)).val PUnit.unit =
      (kPlusPoint (polynomial.eval t)).val PUnit.unit
    rw [hp]
    change MvPolynomial.eval₂ (RingHom.id k) (fun _ => t) p = polynomial.eval t
    exact MvPolynomial.eval₂_const_uniqueAlgEquiv.symm
  have htarget := congrArg target.hom.onPoints hcoordinate
  change target.hom.onPoints
      (target.inv.onPoints (f.onPoints (source.value t))) =
    target.value (polynomial.eval t) at htarget
  rw [target.inv_hom_id] at htarget
  exact htarget

/-
 A certificate that an image closed subgroup is one-parameter and that fixed
 source and target parameters are related by a nonzero polynomial.  Additivity
 is derived from the homomorphism law; over an algebraically closed field the
 resulting polynomial is automatically surjective.  The `image_eq` field keeps
 the certificate usable with an explicitly named target subgroup, including
 after a maximal-torus conjugation.
-/
public structure IsogenyRootImageWitness
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (X : ClosedSubgroup K)
    (Y : ClosedSubgroup H) where
  image_eq : (φ.comp X.inclusion).imageClosedSubgroup = Y
  source : OneParameterParametrization X.carrierVariety
  target : OneParameterParametrization Y.carrierVariety
  polynomial : Polynomial k
  polynomial_ne_zero : polynomial ≠ 0
  parameter_eq : ∀ t : k,
    φ.onPoints (X.includePoint (source.value t)) =
      Y.includePoint (target.value (polynomial.eval t))

/-- Construct a root-image witness from a surjective restricted morphism and
chosen one-parameter coordinates.  Surjectivity forces the coordinate
polynomial to be nonzero. -/
public noncomputable def IsogenyRootImageWitness.of_surjective
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (phi : AlgebraicGroup.Morphism K H) (X : ClosedSubgroup K)
    (Y : ClosedSubgroup H)
    (image_eq : (phi.comp X.inclusion).imageClosedSubgroup = Y)
    (source : OneParameterParametrization X.carrierVariety)
    (target : OneParameterParametrization Y.carrierVariety)
    (q : AlgebraicGroup.Morphism X.carrierVariety Y.carrierVariety)
    (hq : ∀ x, Y.includePoint (q.onPoints x) =
      phi.onPoints (X.includePoint x))
    (hqsurj : Function.Surjective q.onPoints) :
    IsogenyRootImageWitness phi X Y := by
  let hpoly := oneParameterMorphism_exists_polynomial source target q
  let polynomial := Classical.choose hpoly
  have hpolynomial := Classical.choose_spec hpoly
  have hne : polynomial ≠ 0 := by
    obtain ⟨x, hx⟩ := hqsurj (target.value 1)
    let t : k := Multiplicative.toAdd
      (additiveGroupPointEquiv k (source.inv.onPoints x))
    have hsource : source.value t = x := by
      change source.hom.onPoints (kPlusPoint t) = x
      rw [show kPlusPoint t = source.inv.onPoints x by
        exact kPlusPoint_coordinate (source.inv.onPoints x)]
      exact source.inv_hom_id x
    have heval : polynomial.eval t = 1 := by
      have hvalue : target.value (polynomial.eval t) = target.value 1 := by
        rw [← hpolynomial, hsource, hx]
      have hback := congrArg target.inv.onPoints hvalue
      change target.inv.onPoints
          (target.hom.onPoints (kPlusPoint (polynomial.eval t))) =
        target.inv.onPoints (target.hom.onPoints (kPlusPoint 1)) at hback
      rw [target.hom_inv_id, target.hom_inv_id] at hback
      exact congrArg (fun z : Variety.Point (KPlus k) =>
        Multiplicative.toAdd (additiveGroupPointEquiv k z)) hback
    intro hzero
    rw [hzero, Polynomial.eval_zero] at heval
    exact zero_ne_one heval
  exact {
    image_eq := image_eq
    source := source
    target := target
    polynomial := polynomial
    polynomial_ne_zero := hne
    parameter_eq := fun t => (hq (source.value t)).symm.trans
      (congrArg Y.includePoint (hpolynomial t)) }

public theorem IsogenyRootImageWitness.isOneParameter
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H} {X : ClosedSubgroup K}
    {Y : ClosedSubgroup H} (w : IsogenyRootImageWitness φ X Y) :
    IsOneParameterGroup Y.carrierVariety :=
  ⟨w.target⟩

public theorem IsogenyRootImageWitness.image_ne_bot
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H} {X : ClosedSubgroup K}
    {Y : ClosedSubgroup H} (w : IsogenyRootImageWitness φ X Y) :
    Y.toSubgroup ≠ ⊥ := by
  intro hY
  have hm : Y.includePoint (w.target.value 1) ∈ Y.toSubgroup :=
    (Y.pointEquiv (w.target.value 1)).property
  rw [hY] at hm
  have hpoint : Y.includePoint (w.target.value 1) = 1 :=
    Subgroup.mem_bot.mp hm
  have hpoint' : w.target.hom.onPoints (kPlusPoint 1) =
      (1 : Variety.Point Y.carrierVariety) := by
    apply Y.inclusion_injective
    exact hpoint
  have hi := congrArg w.target.inv.onPoints hpoint'
  rw [w.target.hom_inv_id, map_one] at hi
  have hzero : kPlusPoint (0 : k) = 1 := by
    apply (additiveGroupPointEquiv k).injective
    rfl
  have hcp : kPlusPoint (1 : k) = kPlusPoint (0 : k) :=
    hi.trans hzero.symm
  have hc := congrArg (additiveGroupPointEquiv k) hcp
  have : (1 : k) = 0 := by
    apply Multiplicative.ofAdd.injective
    simp [kPlusPoint] at hc
  exact one_ne_zero this

public theorem isogeny_image_rootSubgroup_isTorusRootSubgroup
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H) (T : ClosedSubgroup K)
    (X : ClosedSubgroup K) (hInv : IsClosedSubgroupInvariant T X)
    (w : IsogenyRootImageWitness φ X
      (φ.comp X.inclusion).imageClosedSubgroup) :
    IsTorusRootSubgroup
      (φ.comp T.inclusion).imageClosedSubgroup
      (φ.comp X.inclusion).imageClosedSubgroup := by
  constructor
  · exact morphism_image_rootSubgroup_invariant φ T X hInv
  · exact w.isOneParameter

end ImageWitness

section CharacterTransport

omit [IsAlgClosed k] in
private lemma oneParameterParametrization_value_injective
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X) : Function.Injective x.value := by
  intro s t hst
  have h := congrArg x.inv.onPoints hst
  change x.inv.onPoints (x.hom.onPoints (kPlusPoint s)) =
      x.inv.onPoints (x.hom.onPoints (kPlusPoint t)) at h
  rw [x.hom_inv_id, x.hom_inv_id] at h
  exact congrArg (fun z : Variety.Point (KPlus k) =>
    Multiplicative.toAdd (additiveGroupPointEquiv k z)) h

omit [IsAlgClosed k] in
private lemma oneParameterParametrization_value_add
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X) (s t : k) :
    x.value (s + t) = x.value s * x.value t := by
  change x.hom.onPoints (kPlusPoint (s + t)) =
    x.hom.onPoints (kPlusPoint s) * x.hom.onPoints (kPlusPoint t)
  rw [show kPlusPoint (s + t) = kPlusPoint s * kPlusPoint t by
    apply (additiveGroupPointEquiv k).injective
    rfl, map_mul]

omit [IsAlgClosed k] in
private lemma torusCharacter_pointCharacter_pow
    {T : Variety k} [AlgebraicGroup T]
    (χ : TorusCharacter T) (n : ℕ) (s : Variety.Point T) :
    (χ ^ n).pointCharacter s = χ.pointCharacter s ^ n := by
  induction n with
  | zero =>
    change (dPointEquiv 1 (1 : Variety.Point (KMult k)) 0 : k) = _
    rw [dPointEquiv_one]
    simp
  | succ n ih =>
    rw [pow_succ]
    change (dPointEquiv 1 ((χ ^ n).onPoints s * χ.onPoints s) 0 : k) = _
    rw [dPointEquiv_mul]
    change (χ ^ n).pointCharacter s * χ.pointCharacter s = _
    rw [ih, pow_succ]

private lemma IsogenyRootImageWitness.parameter_additive
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H} {X : ClosedSubgroup K}
    {Y : ClosedSubgroup H} (w : IsogenyRootImageWitness φ X Y) :
    IsAdditivePolynomial w.polynomial := by
  apply (isAdditivePolynomial_iff _).mpr
  intro s t
  apply oneParameterParametrization_value_injective w.target
  apply Y.inclusion_injective
  calc
    Y.includePoint (w.target.value (w.polynomial.eval (s + t))) =
        φ.onPoints (X.includePoint (w.source.value (s + t))) := by
      rw [w.parameter_eq]
    _ = φ.onPoints (X.includePoint (w.source.value s) *
        X.includePoint (w.source.value t)) := by
      rw [oneParameterParametrization_value_add]
      rfl
    _ = φ.onPoints (X.includePoint (w.source.value s)) *
        φ.onPoints (X.includePoint (w.source.value t)) := φ.map_mul _ _
    _ = Y.includePoint (w.target.value (w.polynomial.eval s)) *
        Y.includePoint (w.target.value (w.polynomial.eval t)) := by
      rw [w.parameter_eq, w.parameter_eq]
    _ = Y.includePoint
        (w.target.value (w.polynomial.eval s + w.polynomial.eval t)) := by
      rw [oneParameterParametrization_value_add]
      rfl

public theorem IsogenyRootImageWitness.natDegree_ne_zero
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H} {X : ClosedSubgroup K}
    {Y : ClosedSubgroup H} (w : IsogenyRootImageWitness φ X Y) :
    w.polynomial.natDegree ≠ 0 := by
  intro hdegree
  have hevalZero : w.polynomial.eval 0 = 0 := by
    have hadd := (isAdditivePolynomial_iff w.polynomial).mp
      w.parameter_additive 0 0
    have h := congrArg (fun z : k => z - w.polynomial.eval 0) hadd
    simpa using h.symm
  apply w.polynomial_ne_zero
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdegree]
  have hcoeff : w.polynomial.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact hevalZero
  rw [hcoeff, Polynomial.C_0]

public theorem IsogenyRootImageWitness.polynomial_surjective
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H} {X : ClosedSubgroup K}
    {Y : ClosedSubgroup H} (w : IsogenyRootImageWitness φ X Y) :
    Function.Surjective w.polynomial.eval :=
  IsAlgClosed.eval_surjective w.natDegree_ne_zero

private lemma IsogenyRootImageWitness.parameter_scaling
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H}
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    {X : ClosedSubgroup K} {Y : ClosedSubgroup H}
    (w : IsogenyRootImageWitness φ X Y)
    (τ : AlgebraicGroup.Morphism T.carrierVariety T'.carrierVariety)
    (hτ : ∀ s, T'.includePoint (τ.onPoints s) =
      φ.onPoints (T.includePoint s))
    (χ : TorusWeight T) (χ' : TorusWeight T')
    (hsource : RootWeightEquation T X χ)
    (htarget : RootWeightEquation T' Y χ')
    (s : Variety.Point T.carrierVariety) (t : k) :
    χ'.pointCharacter (τ.onPoints s) * w.polynomial.eval t =
      w.polynomial.eval (χ.pointCharacter s * t) := by
  have hs := hsource w.source t s
  have hsφ := congrArg φ.onPoints hs
  simp only [map_mul, map_inv] at hsφ
  have ht := htarget w.target (w.polynomial.eval t) (τ.onPoints s)
  rw [← hτ s] at hsφ
  rw [w.parameter_eq, w.parameter_eq] at hsφ
  have hpoint := ht.symm.trans hsφ
  have hparam : w.target.value
      (χ'.pointCharacter (τ.onPoints s) * w.polynomial.eval t) =
      w.target.value
        (w.polynomial.eval (χ.pointCharacter s * t)) := by
    apply Y.inclusion_injective
    exact hpoint
  exact oneParameterParametrization_value_injective w.target hparam

/-- The root character pulled back along an isogeny is the source root
character raised to the degree of the additive root-parameter polynomial. -/
public theorem IsogenyRootImageWitness.weight_pullback_eq_pow_natDegree
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H}
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    {X : ClosedSubgroup K} {Y : ClosedSubgroup H}
    (w : IsogenyRootImageWitness φ X Y)
    (τ : AlgebraicGroup.Morphism T.carrierVariety T'.carrierVariety)
    (hτ : ∀ s, T'.includePoint (τ.onPoints s) =
      φ.onPoints (T.includePoint s))
    (χ : TorusWeight T) (χ' : TorusWeight T')
    (hsource : RootWeightEquation T X χ)
    (htarget : RootWeightEquation T' Y χ') :
    TorusCharacter.pullback τ χ' = χ ^ w.polynomial.natDegree := by
  apply TorusCharacter.pointCharacter_injective
  ext s
  let c := χ.pointCharacter s
  let d := χ'.pointCharacter (τ.onPoints s)
  have hev : ∀ t : k,
      w.polynomial.eval (c * t) = d * w.polynomial.eval t := by
    intro t
    simpa [c, d] using
      (w.parameter_scaling τ hτ χ χ' hsource htarget s t).symm
  have hpoly : w.polynomial.comp (Polynomial.C c * Polynomial.X) =
      Polynomial.C d * w.polynomial := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    exact hev t
  let n := w.polynomial.natDegree
  have hcoeff : w.polynomial.coeff n ≠ 0 := by
    rw [show w.polynomial.coeff n = w.polynomial.leadingCoeff by rfl]
    exact Polynomial.leadingCoeff_ne_zero.mpr w.polynomial_ne_zero
  have hc := congrArg (fun p : Polynomial k => p.coeff n) hpoly
  rw [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C_mul] at hc
  have hcd : c ^ n = d := by
    apply mul_right_cancel₀ hcoeff
    calc
      c ^ n * w.polynomial.coeff n =
          w.polynomial.coeff n * c ^ n := mul_comm _ _
      _ = d * w.polynomial.coeff n := hc
  exact hcd.symm.trans
    (torusCharacter_pointCharacter_pow χ n s).symm

/-- The root scale of an isogeny is a power of the field characteristic. -/
public theorem IsogenyRootImageWitness.natDegree_eq_ringChar_pow
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H} {X : ClosedSubgroup K}
    {Y : ClosedSubgroup H} (w : IsogenyRootImageWitness φ X Y) :
    ∃ e : ℕ, w.polynomial.natDegree = ringChar k ^ e :=
  additivePolynomial_natDegree_eq_ringChar_pow w.parameter_additive
    w.polynomial_ne_zero

omit [IsAlgClosed k] in
public lemma torusCharacter_pullback_injective_of_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (hf : Function.Surjective f.onPoints) :
    Function.Injective (TorusCharacter.pullback f) := by
  intro χ ψ hχψ
  apply TorusCharacter.pointCharacter_injective
  ext x
  obtain ⟨y, hy⟩ := hf x
  have h := congrArg (fun z : TorusCharacter G => z.pointCharacter y) hχψ
  change χ.pointCharacter (f.onPoints y) = ψ.pointCharacter (f.onPoints y) at h
  simpa [hy] using h

/-- If a character pulls back with scale `q` and a cocharacter pushes forward
with scale `r`, their integral pairings satisfy `q * m = r * m'`. -/
public theorem scaled_weightCocharacter_pairing
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    (τ : AlgebraicGroup.Morphism T.carrierVariety T'.carrierVariety)
    (χ : TorusWeight T) (χ' : TorusWeight T')
    (h : ClosedSubgroupTorusCocharacter T)
    (h' : ClosedSubgroupTorusCocharacter T')
    (characterScale cocharacterScale : ℕ)
    (hχ : TorusCharacter.pullback τ χ' = χ ^ characterScale)
    (hh : ∀ t : Variety.Point (KMult k),
      τ.onPoints (h.onPoints t) = h'.onPoints (t ^ cocharacterScale))
    (m m' : ℤ)
    (hm : WeightCocharacterEquation T χ h m)
    (hm' : WeightCocharacterEquation T' χ' h' m') :
    (characterScale : ℤ) * m = (cocharacterScale : ℤ) * m' := by
  have hleft : WeightCocharacterEquation T
      (TorusCharacter.pullback τ χ') h ((characterScale : ℤ) * m) := by
    intro t
    rw [hχ]
    calc
      (χ ^ characterScale).pointCharacter (h.onPoints t) =
          χ.pointCharacter (h.onPoints t) ^ characterScale :=
        torusCharacter_pointCharacter_pow χ characterScale _
      _ = ((dPointEquiv 1 t 0 : k) ^ m) ^ characterScale := by rw [hm t]
      _ = (dPointEquiv 1 t 0 : k) ^ ((characterScale : ℤ) * m) := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm]
  have hright : WeightCocharacterEquation T
      (TorusCharacter.pullback τ χ') h ((cocharacterScale : ℤ) * m') := by
    intro t
    change χ'.pointCharacter (τ.onPoints (h.onPoints t)) = _
    rw [hh t, hm' (t ^ cocharacterScale)]
    rw [show (dPointEquiv 1 (t ^ cocharacterScale) 0 : k) =
        (dPointEquiv 1 t 0 : k) ^ cocharacterScale by
      exact congrArg Units.val
        (congrFun (dPointEquiv_pow 1 cocharacterScale t) 0)]
    rw [← zpow_natCast, ← zpow_mul]
  exact (weightCocharacterEquation_existsUnique T
    (TorusCharacter.pullback τ χ') h).unique hleft hright

end CharacterTransport

section RootDataTransport

/- A scaling-aware transport certificate for realized root data. -/
public structure IsogenyRootDataTransport
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism K H)
    (T : ClosedSubgroup K) (T' : ClosedSubgroup H)
    (D : RootGroupData K T) (D' : RootGroupData H T') where
  target_maximal : IsMaximalTorus T'
  torusMap : AlgebraicGroup.Morphism T.carrierVariety T'.carrierVariety
  torusMap_surjective : Function.Surjective torusMap.onPoints
  torusMap_apply : ∀ s : Variety.Point T.carrierVariety,
    T'.includePoint (torusMap.onPoints s) = φ.onPoints (T.includePoint s)
  rootEquiv : D.Root ≃ D'.Root
  imageWitness : ∀ α,
    IsogenyRootImageWitness φ (D.rootSubgroup α)
      (D'.rootSubgroup (rootEquiv α))
  image_invariant : ∀ α,
    IsClosedSubgroupInvariant T'
      ((φ.comp (D.rootSubgroup α).inclusion).imageClosedSubgroup)
  cocharacterScale : D.Root → ℕ
  cocharacterScale_ne_zero : ∀ α, cocharacterScale α ≠ 0
  cocharacterScale_charPower : ∀ α,
    ∃ e : ℕ, cocharacterScale α = ringChar k ^ e
  cocharacter_pushforward : ∀ α (t : Variety.Point (KMult k)),
    torusMap.onPoints ((D.rootCocharacter α).onPoints t) =
      (D'.rootCocharacter (rootEquiv α)).onPoints
        (t ^ cocharacterScale α)
  reflection_transport : ∀ α β,
    rootEquiv (D.reflect α β) = D'.reflect (rootEquiv α) (rootEquiv β)

/-- The root-character scale is the degree of the root-parameter polynomial. -/
public def IsogenyRootDataTransport.rootScale
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H}
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    {D : RootGroupData K T} {D' : RootGroupData H T'}
    (R : IsogenyRootDataTransport φ T T' D D') (alpha : D.Root) : ℕ :=
  (R.imageWitness alpha).polynomial.natDegree

/-- Both root and coroot parameter maps have scale one.  This is an explicit
separability/root-coordinate certificate, not a consequence of `IsIsogeny`. -/
public def IsogenyRootDataTransport.IsScaleOne
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H}
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    {D : RootGroupData K T} {D' : RootGroupData H T'}
    (R : IsogenyRootDataTransport φ T T' D D') : Prop :=
  (∀ alpha, R.rootScale alpha = 1) ∧ (∀ alpha, R.cocharacterScale alpha = 1)

public theorem IsogenyRootDataTransport.rootScale_ne_zero
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H}
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    {D : RootGroupData K T} {D' : RootGroupData H T'}
    (R : IsogenyRootDataTransport φ T T' D D') (alpha : D.Root) :
    R.rootScale alpha ≠ 0 :=
  (R.imageWitness alpha).natDegree_ne_zero

public theorem IsogenyRootDataTransport.rootScale_charPower
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H}
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    {D : RootGroupData K T} {D' : RootGroupData H T'}
    (R : IsogenyRootDataTransport φ T T' D D') (alpha : D.Root) :
    ∃ e : ℕ, R.rootScale alpha = ringChar k ^ e :=
  (R.imageWitness alpha).natDegree_eq_ringChar_pow

/-- The target root character pulls back to the characteristic-power multiple
of the source root character certified by the root parameter map. -/
public theorem IsogenyRootDataTransport.weight_pullback
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H}
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    {D : RootGroupData K T} {D' : RootGroupData H T'}
    (R : IsogenyRootDataTransport φ T T' D D')
    (hD : D.IsRealization) (hD' : D'.IsRealization) (alpha : D.Root) :
    TorusCharacter.pullback R.torusMap (D'.rootWeight (R.rootEquiv alpha)) =
      D.rootWeight alpha ^ R.rootScale alpha :=
  (R.imageWitness alpha).weight_pullback_eq_pow_natDegree
    R.torusMap R.torusMap_apply (D.rootWeight alpha)
      (D'.rootWeight (R.rootEquiv alpha))
      (hD.2.2.1 alpha).2 (hD'.2.2.1 (R.rootEquiv alpha)).2

public theorem IsogenyRootDataTransport.image_rootSubgroup_eq
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H}
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    {D : RootGroupData K T} {D' : RootGroupData H T'}
    (R : IsogenyRootDataTransport φ T T' D D') (alpha : D.Root) :
    (φ.comp (D.rootSubgroup alpha).inclusion).imageClosedSubgroup =
      D'.rootSubgroup (R.rootEquiv alpha) :=
  (R.imageWitness alpha).image_eq

/-- Root and coroot scales control the Cartan pairing across an isogeny. -/
public theorem IsogenyRootDataTransport.scaled_pairing
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H}
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    {D : RootGroupData K T} {D' : RootGroupData H T'}
    (R : IsogenyRootDataTransport φ T T' D D')
    (hD : D.IsRealization) (hD' : D'.IsRealization)
    (alpha beta : D.Root) :
    (R.rootScale alpha : ℤ) * D.pairing alpha beta =
      (R.cocharacterScale beta : ℤ) *
        D'.pairing (R.rootEquiv alpha) (R.rootEquiv beta) := by
  have h := scaled_weightCocharacter_pairing R.torusMap
    (D.rootWeight alpha) (D'.rootWeight (R.rootEquiv alpha))
    (D.rootCocharacter beta) (D'.rootCocharacter (R.rootEquiv beta))
    (R.rootScale alpha) (R.cocharacterScale beta)
    (R.weight_pullback hD hD' alpha) (R.cocharacter_pushforward beta)
    (D.weightPairing (D.rootWeight alpha) beta)
    (D'.weightPairing (D'.rootWeight (R.rootEquiv alpha)) (R.rootEquiv beta))
    (hD.weightPairing_spec (D.rootWeight alpha) beta)
    (hD'.weightPairing_spec (D'.rootWeight (R.rootEquiv alpha))
      (R.rootEquiv beta))
  rw [hD.weightPairing_rootWeight,
    hD'.weightPairing_rootWeight] at h
  exact h

/-- Exact Cartan-pairing transport is the scale-one specialization. -/
public theorem IsogenyRootDataTransport.pairing_preserved_of_scaleOne
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H}
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    {D : RootGroupData K T} {D' : RootGroupData H T'}
    (R : IsogenyRootDataTransport φ T T' D D')
    (hD : D.IsRealization) (hD' : D'.IsRealization)
    (hscale : R.IsScaleOne) (alpha beta : D.Root) :
    D'.pairing (R.rootEquiv alpha) (R.rootEquiv beta) = D.pairing alpha beta := by
  have h := R.scaled_pairing hD hD' alpha beta
  rw [hscale.1 alpha, hscale.2 beta] at h
  simpa using h.symm

/-- Exact root-character pullback is the scale-one specialization. -/
public theorem IsogenyRootDataTransport.weight_pullback_of_scaleOne
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H}
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    {D : RootGroupData K T} {D' : RootGroupData H T'}
    (R : IsogenyRootDataTransport φ T T' D D')
    (hD : D.IsRealization) (hD' : D'.IsRealization)
    (hscale : R.IsScaleOne) (alpha : D.Root) :
    TorusCharacter.pullback R.torusMap (D'.rootWeight (R.rootEquiv alpha)) =
      D.rootWeight alpha := by
  rw [R.weight_pullback hD hD' alpha, hscale.1 alpha, pow_one]

public theorem IsogenyRootDataTransport.reflect_preserved
    {K H : Variety k} [AlgebraicGroup K] [AlgebraicGroup H]
    {φ : AlgebraicGroup.Morphism K H}
    {T : ClosedSubgroup K} {T' : ClosedSubgroup H}
    {D : RootGroupData K T} {D' : RootGroupData H T'}
    (R : IsogenyRootDataTransport φ T T' D D')
    (α β : D.Root) :
    R.rootEquiv (D.reflect α β) =
      D'.reflect (R.rootEquiv α) (R.rootEquiv β) :=
  R.reflection_transport α β

end RootDataTransport

end Theory.AlgebraicGroup
