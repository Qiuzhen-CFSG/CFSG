module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.WeightCone.Core
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.Coefficients

/-!
# Polynomial root actions preserve weight cones

Every coefficient of degree `n` of a rational one-parameter action shifts the
weight by the `n`-th power of its direct root character. Dual annihilators
recover the entire root action from these coefficients. Thus a lower weight
cone is stable under all root subgroups whose raw characters belong to its
monoid, and under the Borel they generate together with the torus.

This uses all polynomial degrees, without differentiation or factorial
inversion, and is valid in positive characteristic. The scalar polynomial
construction is reused from `AlgebraicTensor.RestrictedStep.Coefficients`;
no `D4Geometry`, negative-word spanning or irreducibility assumption is used.

Source: Steinberg, *Representations of algebraic groups* (1963), §§2 and 8;
GLS3 §1.14.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.WeightCone
open Theory.AlgebraicGroup AlgebraicTensor.RestrictedStep
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The degree-`n` coefficient of the actual rational action along a curve. -/
def curveCoefficient (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K) (n : ℕ) : Module.End k V :=
  let b := Module.finBasis k V
  { toFun := fun v => ∑ i, (curvePolynomial rho hrho x (b.coord i) v).coeff n • b i
    map_add' := by
      intro v w
      simp only [curvePolynomial_add, Polynomial.coeff_add, add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro c v
      simp only [curvePolynomial_smul, Polynomial.coeff_smul, smul_eq_mul,
        mul_smul, Finset.smul_sum, RingHom.id_apply] }

/-- Covectors characterize every coefficient independently of the chosen basis. -/
theorem dual_curveCoefficient
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K) (n : ℕ)
    (l : Module.Dual k V) (v : V) :
    l (curveCoefficient rho hrho x n v) = (curvePolynomial rho hrho x l v).coeff n := by
  let b := Module.finBasis k V
  have hp : curvePolynomial rho hrho x l v =
      ∑ i, l (b i) • curvePolynomial rho hrho x (b.coord i) v := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, curvePolynomial_eval]
    conv_lhs => rw [← b.sum_repr ((rho.action (x.onPoints (kPlusPoint t))).val v)]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply, mul_comm]
  rw [hp]
  change l (∑ i, (curvePolynomial rho hrho x (b.coord i) v).coeff n • b i) = _
  simp only [map_sum, map_smul, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    smul_eq_mul, mul_comm]

/-- A subspace containing every coefficient contains every point of the orbit. -/
theorem curve_action_mem_of_coefficients
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K) (W : Submodule k V)
    (v : V) (hv : ∀ n, curveCoefficient rho hrho x n v ∈ W) (a : k) :
    (rho.action (x.onPoints (kPlusPoint a))).1 v ∈ W := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  have hp : curvePolynomial rho hrho x l v = 0 := by
    ext n
    rw [← dual_curveCoefficient]
    exact (Submodule.mem_dualAnnihilator _).mp hl _ (hv n)
  rw [← curvePolynomial_eval rho hrho x l v a, hp, Polynomial.eval_zero]

/-- Scaling the parameter scales the degree-`n` coefficient by the `n`-th power. -/
theorem curveCoefficient_intertwine
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K)
    (A B : Module.End k V) (c : k)
    (h : ∀ (a : k) (v : V),
      A ((rho.action (x.onPoints (kPlusPoint a))).val v) =
        (rho.action (x.onPoints (kPlusPoint (c * a)))).val (B v)) (n : ℕ) :
    A * curveCoefficient rho hrho x n = c ^ n • (curveCoefficient rho hrho x n * B) := by
  ext v
  apply (Module.finBasis k V).repr.injective
  ext i
  let l := (Module.finBasis k V).coord i
  have hp : curvePolynomial rho hrho x (l.comp A) v =
      (curvePolynomial rho hrho x l (B v)).comp (Polynomial.C c * Polynomial.X) := by
    apply Polynomial.funext
    intro a
    simp only [curvePolynomial_eval, Polynomial.eval_comp,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, LinearMap.comp_apply, h]
  have hc := congrArg (fun p : Polynomial k => p.coeff n) hp
  rw [← dual_curveCoefficient, Polynomial.comp_C_mul_X_coeff,
    ← dual_curveCoefficient] at hc
  change l (A (curveCoefficient rho hrho x n v)) = l (c ^ n • curveCoefficient rho hrho x n (B v))
  simpa only [LinearMap.comp_apply, map_smul, smul_eq_mul, mul_comm] using hc

omit [IsAlgClosed k] in
private theorem pointCharacter_mul (chi psi : TorusWeight T) (t : Variety.Point T.carrierVariety) :
    (chi * psi).pointCharacter t = chi.pointCharacter t * psi.pointCharacter t := rfl

omit [IsAlgClosed k] in
private theorem pointCharacter_pow (chi : TorusWeight T) (n : ℕ)
    (t : Variety.Point T.carrierVariety) :
    (chi ^ n).pointCharacter t = chi.pointCharacter t ^ n := by
  change (dPointEquiv 1 (chi ^ n |>.onPoints t) 0 : k) = _
  have h : (chi ^ n).onPoints t = chi.onPoints t ^ n := by
    induction n with
    | zero => simp only [pow_zero]; rfl
    | succ n ih => change (chi ^ n).onPoints t * chi.onPoints t = _; rw [ih, pow_succ]
  rw [h, dPointEquiv_pow]
  rfl

/-- The actual included root parametrization as a regular group morphism. -/
def rootCurve (D : RootGroupData K T) (a : D.Root)
    (x : OneParameterParametrization (D.rootSubgroup a).carrierVariety) :
    Theory.AlgebraicGroup.Morphism (KPlus k) K :=
  (D.rootSubgroup a).inclusion.comp x.hom

/-- All polynomial root coefficients have the full expected character shift. -/
theorem root_coefficient_weight
    (D : RootGroupData K T) (hD : D.IsRealization)
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (a : D.Root) (x : OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (n : ℕ) {mu : TorusWeight T} {v : V} (hv : v ∈ weightSpace rho T mu) :
    curveCoefficient rho hrho (rootCurve D a x) n v ∈
      weightSpace rho T (mu * ((D.rootWeight a)⁻¹) ^ n) := by
  intro t
  let A : Module.End k V := (rho.action (T.includePoint t)).val
  let c := ((D.rootWeight a)⁻¹).pointCharacter t
  have he := curveCoefficient_intertwine rho hrho (rootCurve D a x) A A c (by
    intro b w
    have hg := LeftWeights.direct_conjugation (hD.2.2.1 a).2 x b t
    have hh : T.includePoint t * (rootCurve D a x).onPoints (kPlusPoint b) =
        (rootCurve D a x).onPoints (kPlusPoint (c * b)) * T.includePoint t := by
      change T.includePoint t * (D.rootSubgroup a).includePoint (x.value b) =
        (D.rootSubgroup a).includePoint (x.value (c * b)) * T.includePoint t
      rw [← hg]
      group
    have h := congrArg (fun g => (rho.action g).val w) hh
    simpa only [map_mul, Units.val_mul, Module.End.mul_apply, A] using h) n
  have he' := congrArg (fun L : Module.End k V => L v) he
  change A (curveCoefficient rho hrho (rootCurve D a x) n v) =
    c ^ n • curveCoefficient rho hrho (rootCurve D a x) n (A v) at he'
  have ht := hv t
  change A v = _ at ht
  rw [ht, map_smul, smul_smul] at he'
  rw [pointCharacter_mul, pointCharacter_pow]
  change A (curveCoefficient rho hrho (rootCurve D a x) n v) =
    (mu.pointCharacter t * c ^ n) • curveCoefficient rho hrho (rootCurve D a x) n v
  rw [mul_comm (c ^ n)] at he'
  exact he'

private theorem character_shift {A : Type*} [CommGroup A] (chi mu beta : A) (n : ℕ) :
    chi * (mu * (beta⁻¹) ^ n)⁻¹ = (chi * mu⁻¹) * beta ^ n := by
  rw [mul_inv_rev, ← inv_pow, inv_inv]
  ac_rfl

/-- Every point of a root subgroup preserves the lower cone when its raw
character belongs to the cone monoid. -/
theorem lowerSpace_root_stable
    (D : RootGroupData K T) (hD : D.IsRealization)
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (M : Submonoid (TorusWeight T)) (chi : TorusWeight T)
    (a : D.Root) (ha : D.rootWeight a ∈ M)
    (x : OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (g : Variety.Point K) (hg : g ∈ D.rootSubgroup a)
    {v : V} (hv : v ∈ lowerSpace rho T M chi) :
    (rho.action g).1 v ∈ lowerSpace rho T M chi := by
  let y := (D.rootSubgroup a).pointEquiv.symm ⟨g, hg⟩
  let z := x.inv.onPoints y
  let c := Multiplicative.toAdd (additiveGroupPointEquiv k z)
  have hcz : kPlusPoint c = z := by
    apply (additiveGroupPointEquiv k).injective
    simp [kPlusPoint, c]
  have hxg : (rootCurve D a x).onPoints (kPlusPoint c) = g := by
    change (D.rootSubgroup a).includePoint (x.hom.onPoints (kPlusPoint c)) = g
    rw [hcz, x.inv_hom_id]
    exact congrArg Subtype.val ((D.rootSubgroup a).pointEquiv.apply_symm_apply ⟨g, hg⟩)
  rw [← hxg]
  refine Submodule.iSup_induction _ (motive := fun w =>
    (rho.action ((rootCurve D a x).onPoints (kPlusPoint c))).1 w ∈
      lowerSpace rho T M chi) hv ?_ ?_ ?_
  · intro mu w hw
    refine Submodule.iSup_induction _ (motive := fun w =>
      (rho.action ((rootCurve D a x).onPoints (kPlusPoint c))).1 w ∈
        lowerSpace rho T M chi) hw ?_ ?_ ?_
    · intro hmu w hw
      apply curve_action_mem_of_coefficients rho hrho (rootCurve D a x)
      intro n
      apply weightSpace_le_lowerSpace rho M chi (mu * ((D.rootWeight a)⁻¹) ^ n) _
        (root_coefficient_weight D hD rho hrho a x n hw)
      rw [character_shift]
      exact M.mul_mem hmu (M.pow_mem ha n)
    · simp
    · intro w z hw hz
      simpa only [map_add] using (lowerSpace rho T M chi).add_mem hw hz
  · simp
  · intro w z hw hz
    simpa only [map_add] using (lowerSpace rho T M chi).add_mem hw hz

/-- Root-subgroup stability extends to their actual generated subgroup. -/
theorem lowerSpace_generated_stable
    (D : RootGroupData K T) (hD : D.IsRealization)
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (M : Submonoid (TorusWeight T)) (chi : TorusWeight T)
    (P : Set D.Root) (hP : ∀ a ∈ P, D.rootWeight a ∈ M)
    (x : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (g : Variety.Point K) (hg : g ∈ RootSubgroupGenerated D P)
    {v : V} (hv : v ∈ lowerSpace rho T M chi) :
    (rho.action g).1 v ∈ lowerSpace rho T M chi := by
  let W := lowerSpace rho T M chi
  have h : (∀ w ∈ W, (rho.action g).1 w ∈ W) ∧
      (∀ w ∈ W, (rho.action g⁻¹).1 w ∈ W) := by
    apply Subgroup.closure_induction (p := fun g _ =>
      (∀ w ∈ W, (rho.action g).1 w ∈ W) ∧
        (∀ w ∈ W, (rho.action g⁻¹).1 w ∈ W)) ?_ ?_ ?_ ?_ hg
    · intro g hg
      simp only [Set.mem_iUnion] at hg
      obtain ⟨a, ha, hg⟩ := hg
      exact ⟨fun w hw => lowerSpace_root_stable D hD rho hrho M chi a (hP a ha)
        (x a) g hg hw, fun w hw => lowerSpace_root_stable D hD rho hrho M chi a (hP a ha)
        (x a) g⁻¹ ((D.rootSubgroup a).inv_mem hg) hw⟩
    · constructor <;> intro w hw <;> simpa using hw
    · intro g h hg hh hgw hhw
      constructor
      · intro w hw
        simpa only [map_mul, Units.val_mul, Module.End.mul_apply] using hgw.1 _ (hhw.1 w hw)
      · intro w hw
        simpa only [mul_inv_rev, map_mul, Units.val_mul, Module.End.mul_apply] using
          hhw.2 _ (hgw.2 w hw)
    · intro g hg hgw
      simpa only [inv_inv] using hgw.symm
  exact h.1 v hv

/-- The pointwise torus/unipotent decomposition proves stability under the
whole actual Borel. -/
theorem lowerSpace_borel_stable
    (D : RootGroupData K T) (hD : D.IsRealization)
    (rho : RationalRepresentation K V) (hrho : IsRationalRepresentation rho)
    (M : Submonoid (TorusWeight T)) (chi : TorusWeight T)
    {P : Set D.Root} {B : ClosedSubgroup K} (hB : IsBorelOfPositiveSystem D P B)
    (hP : ∀ a ∈ P, D.rootWeight a ∈ M)
    (x : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (g : Variety.Point K) (hg : g ∈ B)
    {v : V} (hv : v ∈ lowerSpace rho T M chi) :
    (rho.action g).1 v ∈ lowerSpace rho T M chi := by
  obtain ⟨t, u, ht, hu, rfl⟩ := (BorelOfPositiveSystem.pointwise_decomposition hB g).mp hg
  let t' := T.pointEquiv.symm ⟨t, ht⟩
  have ht' : T.includePoint t' = t := congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨t, ht⟩)
  rw [← ht', map_mul]
  exact lowerSpace_torus_stable rho M chi t'
    (lowerSpace_generated_stable D hD rho hrho M chi P hP x u hu hv)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.WeightCone
