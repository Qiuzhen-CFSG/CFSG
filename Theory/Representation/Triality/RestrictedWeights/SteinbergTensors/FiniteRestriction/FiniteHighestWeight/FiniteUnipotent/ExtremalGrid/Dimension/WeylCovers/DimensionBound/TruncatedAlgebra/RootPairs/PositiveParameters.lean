module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.CoefficientLaws
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.Basic
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.RootWeights

/-!
# Positive D4 root-parameter relations

Distinct positive D4 roots are independent. Their common squared length two
forces every positive mixed root to have coefficients `(1, 1)`. Thus the
commutator containment has either trivial target or the actual sum-root subgroup.

For the sum-root case, the regular word `b(t)⁻¹ a(s) b(t) a(s)⁻¹` factors through
that closed subgroup. Composing with the inverse of its given parametrization
produces a polynomial on the affine plane. Raw inverse conjugation makes it
an eigenfunction with the sum-root character. Comparing coefficients and
actual coroot pairings forces every supported monomial to be `s * t`.
The resulting constant is independent of both parameters; it may be zero.

The norm argument adapts the elementary D4 calculations in
`CoefficientBrackets.ChevalleyExchanges`, without using its Chevalley hypotheses.
The polynomial argument specializes `CoordinateRing.BiaffineSupport` to the
needed coefficient comparison, with narrow imports. The two-variable monomial
expansion is the elementary finite-product proof of Mathlib's
`MvPolynomial.monomial_fin_two` (Apache 2.0).

Sources: GLS3, Theorems 1.12.1(b), 1.12.7(b),
`refs/KGroup/GLS3/Chapter1.tex`; Steinberg (1963), §2 and (6.2)(b),
`refs/KGroup/GLS3/Chapter2St2.tex`. Nonvanishing and Weyl transport are separate
from this positive-system intermediate theorem.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators commutatorElement
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
public noncomputable section
open ClassBound.ConnectedCentralizer.Bruhat.Coordinates.Normalization

private abbrev P := typeDRootPairing 2
private abbrev rv (r : TypeDRootIndex 4) : Vec 4 := typeDRootEmbedding 4 r

private lemma pairing_symm (α β : TypeDRootIndex 4) :
    P.pairing α β = P.pairing β α := by
  simp only [P, typeDRootPairing_pairing]
  exact dot_comm _ _

private lemma pairing_lower (α β : TypeDRootIndex 4)
    (hli : LinearIndependent ℝ ![P.root α, P.root β]) :
    (-1 : ℝ) ≤ P.pairing α β := by
  have hsym : P.pairingIn ℤ α β = P.pairingIn ℤ β α := by
    apply Int.cast_injective (α := ℝ)
    change (algebraMap ℤ ℝ) (P.pairingIn ℤ α β) = (algebraMap ℤ ℝ) (P.pairingIn ℤ β α)
    simpa only [P.algebraMap_pairingIn] using pairing_symm α β
  have hle := P.coxeterWeightIn_le_four ℤ α β
  have hne := (P.linearIndependent_iff_coxeterWeightIn_ne_four ℤ).mp hli
  rw [RootPairing.coxeterWeightIn, ← hsym] at hle hne
  have hlt := lt_of_le_of_ne hle hne
  have h : (-1 : ℤ) ≤ P.pairingIn ℤ α β := by nlinarith
  rw [← P.algebraMap_pairingIn ℤ]
  change (-1 : ℝ) ≤ (P.pairingIn ℤ α β : ℝ)
  exact_mod_cast h

private lemma norm_root (α : TypeDRootIndex 4) : dot (rv α) (rv α) = 2 :=
  typeDRootInSpan_coroot_eval 4 α

private lemma norm_mixed (x y : Vec 4) (a b : ℝ) :
    dot (a • x + b • y) (a • x + b • y) =
      a ^ 2 * dot x x + b ^ 2 * dot y y + 2 * a * b * dot x y := by
  unfold dot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma mixed_coefficients (α β γ : TypeDRootIndex 4) (i j : ℕ)
    (hi : 0 < i) (hj : 0 < j)
    (hli : LinearIndependent ℝ ![P.root α, P.root β])
    (hr : P.root γ = (i : ℝ) • P.root α + (j : ℝ) • P.root β) :
    i = 1 ∧ j = 1 := by
  have hv : rv γ = (i : ℝ) • rv α + (j : ℝ) • rv β :=
    congrArg (fun x : typeDRootSpan 4 => (x : Vec 4)) hr
  have hn := norm_root γ
  rw [hv, norm_mixed, norm_root, norm_root] at hn
  have hl : (-1 : ℝ) ≤ dot (rv α) (rv β) := by
    simpa only [P, typeDRootPairing_pairing, rv, dot_comm] using pairing_lower α β hli
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hprod : (0 : ℝ) ≤ i * j * (dot (rv α) (rv β) + 1) :=
    mul_nonneg (by positivity) (by linarith)
  have hij : (i : ℝ) * j ≤ 1 := by nlinarith [sq_nonneg ((i : ℝ) - j)]
  have hi1 : (i : ℝ) = 1 := by nlinarith
  have hj1 : (j : ℝ) = 1 := by nlinarith
  exact ⟨by exact_mod_cast hi1, by exact_mod_cast hj1⟩

section Polynomial
variable {k : Type*} [Field k]
private def additiveBiaffineEvalPoint (x y : k) : Fin 2 → k := ![x,y]
omit [Field k] in
private lemma additiveBiaffineEvalPoint_zero (x y : k) :
    additiveBiaffineEvalPoint x y 0 = x := rfl
omit [Field k] in
private lemma additiveBiaffineEvalPoint_one (x y : k) :
    additiveBiaffineEvalPoint x y 1 = y := rfl

private def additiveBiaffineMonomialWeight (a b : k) (m : Fin 2 →₀ ℕ) : k :=
  a ^ m 0 * b ^ m 1

private noncomputable def additiveBiaffineScalePolynomial (a b : k)
    (p : MvPolynomial (Fin 2) k) : MvPolynomial (Fin 2) k :=
  ∑ m ∈ p.support,
    MvPolynomial.monomial m
      (p.coeff m * additiveBiaffineMonomialWeight a b m)

private lemma additiveBiaffineScalePolynomial_coeff (a b : k)
    (p : MvPolynomial (Fin 2) k) (n : Fin 2 →₀ ℕ) :
    (additiveBiaffineScalePolynomial a b p).coeff n =
      p.coeff n * additiveBiaffineMonomialWeight a b n := by
  classical
  rw [additiveBiaffineScalePolynomial, MvPolynomial.coeff_sum]
  by_cases hn : n ∈ p.support
  · rw [Finset.sum_eq_single n]
    · simp [MvPolynomial.coeff_monomial]
    · intro m hm hmn
      simp [MvPolynomial.coeff_monomial, hmn]
    · intro hnnot
      contradiction
  · rw [Finset.sum_eq_zero]
    · rw [MvPolynomial.notMem_support_iff.mp hn]
      simp
    · intro m hm
      by_cases hmn : m = n
      · subst m
        contradiction
      · simp [MvPolynomial.coeff_monomial, hmn]

private lemma monomial_two (d : Fin 2 →₀ ℕ) (a : k) :
    MvPolynomial.monomial d a =
      MvPolynomial.C a * MvPolynomial.X 0 ^ d 0 * MvPolynomial.X 1 ^ d 1 := by
  rw [MvPolynomial.monomial_eq, mul_assoc,
    d.prod_fintype _ (fun _ => pow_zero _), Fin.prod_univ_two]

private lemma additiveBiaffineScalePolynomial_eval_monomial
    (a b x y c : k) (m : Fin 2 →₀ ℕ) :
    MvPolynomial.eval (additiveBiaffineEvalPoint x y)
      (MvPolynomial.monomial m
        (c * additiveBiaffineMonomialWeight a b m)) =
      MvPolynomial.eval (additiveBiaffineEvalPoint (a * x) (b * y))
        (MvPolynomial.monomial m c) := by
  rw [monomial_two, monomial_two]
  simp [additiveBiaffineEvalPoint_zero, additiveBiaffineEvalPoint_one,
    additiveBiaffineMonomialWeight, mul_pow]
  ring_nf

private lemma additiveBiaffineScalePolynomial_eval (a b x y : k)
    (p : MvPolynomial (Fin 2) k) :
    MvPolynomial.eval (additiveBiaffineEvalPoint x y)
      (additiveBiaffineScalePolynomial a b p) =
      MvPolynomial.eval (additiveBiaffineEvalPoint (a * x) (b * y)) p := by
  classical
  rw [additiveBiaffineScalePolynomial]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact additiveBiaffineScalePolynomial_eval_monomial a b x y (p.coeff m) m

private lemma TorusCharacter.pointCharacter_mul_apply
    {T : Variety k} [AlgebraicGroup T]
    (χ ψ : TorusCharacter T) (t : Variety.Point T) :
    (χ * ψ).pointCharacter t =
      χ.pointCharacter t * ψ.pointCharacter t := by
  change (dPointEquiv 1 ((χ * ψ).onPoints t) 0 : k) =
    (dPointEquiv 1 (χ.onPoints t) 0 : k) *
      (dPointEquiv 1 (ψ.onPoints t) 0 : k)
  change (dPointEquiv 1 (χ.onPoints t * ψ.onPoints t) 0 : k) =
    (dPointEquiv 1 (χ.onPoints t) 0 : k) *
      (dPointEquiv 1 (ψ.onPoints t) 0 : k)
  exact congrArg Units.val
    (congrFun (dPointEquiv_mul 1 (χ.onPoints t) (ψ.onPoints t)) 0)

private lemma TorusCharacter.pointCharacter_one_apply
    {T : Variety k} [AlgebraicGroup T] (t : Variety.Point T) :
    (1 : TorusCharacter T).pointCharacter t = 1 := by
  change (dPointEquiv 1 ((1 : TorusCharacter T).onPoints t) 0 : k) = 1
  change (dPointEquiv 1 (1 : Variety.Point (KMult k)) 0 : k) = 1
  exact congrArg Units.val (congrFun (dPointEquiv_one (k := k) 1) 0)

private lemma TorusCharacter.pointCharacter_pow_apply
    {T : Variety k} [AlgebraicGroup T]
    (χ : TorusCharacter T) (n : ℕ) (t : Variety.Point T) :
    (χ ^ n).pointCharacter t = χ.pointCharacter t ^ n := by
  induction n with
  | zero =>
      simpa using TorusCharacter.pointCharacter_one_apply (k := k) (T := T) t
  | succ n ih =>
      rw [pow_succ, TorusCharacter.pointCharacter_mul_apply, ih, pow_succ]

private theorem additiveBiaffine_coeff_character_of_scalePolynomial
    [IsAlgClosed k]
    {T : Variety k} [AlgebraicGroup T]
    (alpha beta gamma : TorusCharacter T)
    {p : MvPolynomial (Fin 2) k}
    (hscale : ∀ t : Variety.Point T,
      additiveBiaffineScalePolynomial
          (alpha.pointCharacter t) (beta.pointCharacter t) p =
        MvPolynomial.C (gamma.pointCharacter t) * p)
    {m : Fin 2 →₀ ℕ} (hm : p.coeff m ≠ 0) :
    gamma = alpha ^ (m 0) * beta ^ (m 1) := by
  apply TorusCharacter.pointCharacter_injective
  ext t
  have hcoeff :=
    congrArg (fun P : MvPolynomial (Fin 2) k => P.coeff m) (hscale t)
  rw [additiveBiaffineScalePolynomial_coeff, MvPolynomial.coeff_C_mul] at hcoeff
  have hval : gamma.pointCharacter t =
      alpha.pointCharacter t ^ m 0 * beta.pointCharacter t ^ m 1 := by
    apply mul_left_cancel₀ hm
    calc
      p.coeff m * gamma.pointCharacter t =
          gamma.pointCharacter t * p.coeff m := by
        rw [mul_comm]
      _ =
          p.coeff m *
            (alpha.pointCharacter t ^ m 0 * beta.pointCharacter t ^ m 1) := by
        rw [← hcoeff]
        rw [additiveBiaffineMonomialWeight]
  simpa [TorusCharacter.pointCharacter_mul_apply,
    TorusCharacter.pointCharacter_pow_apply] using hval

private theorem additiveBiaffine_coeff_character_of_eval_scaling
    [IsAlgClosed k]
    {T : Variety k} [AlgebraicGroup T]
    (alpha beta gamma : TorusCharacter T)
    {p : MvPolynomial (Fin 2) k}
    (hscale : ∀ (t : Variety.Point T) (x y : k),
      MvPolynomial.eval
        (additiveBiaffineEvalPoint (alpha.pointCharacter t * x)
          (beta.pointCharacter t * y)) p =
        gamma.pointCharacter t *
          MvPolynomial.eval (additiveBiaffineEvalPoint x y) p)
    {m : Fin 2 →₀ ℕ} (hm : p.coeff m ≠ 0) :
    gamma = alpha ^ (m 0) * beta ^ (m 1) := by
  apply additiveBiaffine_coeff_character_of_scalePolynomial
    (alpha := alpha) (beta := beta) (gamma := gamma) (p := p)
  · intro t
    apply MvPolynomial.funext
    intro v
    have hv : additiveBiaffineEvalPoint (v 0) (v 1) = v := by
      funext i
      fin_cases i <;> rfl
    calc
      MvPolynomial.eval v
          (additiveBiaffineScalePolynomial (alpha.pointCharacter t)
            (beta.pointCharacter t) p) =
          MvPolynomial.eval (additiveBiaffineEvalPoint (v 0) (v 1))
            (additiveBiaffineScalePolynomial (alpha.pointCharacter t)
              (beta.pointCharacter t) p) := by
        rw [hv]
      _ = MvPolynomial.eval
          (additiveBiaffineEvalPoint (alpha.pointCharacter t * v 0)
            (beta.pointCharacter t * v 1)) p := by
        rw [additiveBiaffineScalePolynomial_eval]
      _ = gamma.pointCharacter t *
          MvPolynomial.eval (additiveBiaffineEvalPoint (v 0) (v 1)) p :=
        hscale t (v 0) (v 1)
      _ = MvPolynomial.eval v (MvPolynomial.C (gamma.pointCharacter t) * p) := by
        rw [hv]
        simp
  · exact hm

end Polynomial

universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

private lemma independent_positive (S : Geometry K) (a b : S.roots.Root)
    (ha : a ∈ S.roots.positive) (hb : b ∈ S.roots.positive) (hne : a ≠ b) :
    LinearIndependent ℝ ![P.root (S.rootIndex a), P.root (S.rootIndex b)] := by
  apply RootPairing.IsReduced.linearIndependent
  · exact fun h => hne (S.rootIndex.injective h)
  · intro h
    have he : b = S.roots.neg a := by
      apply S.rootIndex.injective
      apply P.root.injective
      rw [S.based.2.2.1 a, P.root_reflectionPerm, P.reflection_apply_self]
      exact (neg_eq_iff_eq_neg.mpr h).symm
    have ha' := (S.positive a).mp ha
    have hb' := (S.positive b).mp hb
    rw [he, S.based.2.2.1, RootPairing.Base.isPos_iff] at hb'
    have hh := (typeDRootPairing_base 2).height_reflectionPerm_self (S.rootIndex a)
    change (typeDRootPairing_base 2).height (P.reflectionPerm (S.rootIndex a) (S.rootIndex a)) = _ at hh
    rw [hh] at hb'
    rw [RootPairing.Base.isPos_iff] at ha'
    omega

private lemma correction_root_sum (S : Geometry K) (a b d : S.roots.Root)
    (hli : LinearIndependent ℝ ![P.root (S.rootIndex a), P.root (S.rootIndex b)])
    (hd : d ∈ positiveCommutatorRoots S a b) : RootSum S a b d := by
  obtain ⟨_, i, j, hi, hj, hr⟩ := hd
  obtain ⟨rfl, rfl⟩ := mixed_coefficients _ _ _ i j hi hj hli hr
  simpa only [RootSum, Nat.cast_one, one_smul] using hr

private lemma commutator_le_sum (S : Geometry K)
    (hcomm : PositiveCommutatorContainment S) (a b c : S.roots.Root)
    (ha : a ∈ S.roots.positive) (hb : b ∈ S.roots.positive)
    (hsum : RootSum S a b c) :
    ⁅(S.roots.rootSubgroup a).toSubgroup, (S.roots.rootSubgroup b).toSubgroup⁆ ≤
      (S.roots.rootSubgroup c).toSubgroup := by
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨S.rootIndex c, hsum⟩
  have hne : a ≠ b := by
    intro h
    subst b
    exact one_ne_zero (LinearIndependent.pair_iff.mp hli 1 (-1) (by simp)).1
  apply (hcomm a ha b hb hne).trans
  rw [← RootSubgroupGenerated_singleton S.roots c]
  apply RootSubgroupGenerated_mono
  intro d hd
  apply Set.mem_singleton_iff.mpr
  apply S.rootIndex.injective
  apply P.root.injective
  exact (correction_root_sum S a b d hli hd).trans hsum.symm

private lemma curve_mem (S : Geometry K) (a : S.roots.Root) (z : Variety.Point (KPlus k)) :
    (rootCurve S a).onPoints z ∈ (S.roots.rootSubgroup a).toSubgroup :=
  ((S.roots.rootSubgroup a).pointEquiv ((S.rootParameter a).hom.onPoints z)).property

/-- Positive roots with no sum root have commuting actual root parameters. -/
theorem positive_rootCurve_commute (S : Geometry K)
    (hcomm : PositiveCommutatorContainment S) (a b : S.roots.Root)
    (ha : a ∈ S.roots.positive) (hb : b ∈ S.roots.positive) (hne : a ≠ b)
    (hno : ¬ ∃ c, RootSum S a b c) (s t : k) :
    Commute ((rootCurve S a).onPoints (kPlusPoint s))
      ((rootCurve S b).onPoints (kPlusPoint t)) := by
  have hroots : positiveCommutatorRoots S a b = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro d hd
    exact hno ⟨d, correction_root_sum S a b d (independent_positive S a b ha hb hne) hd⟩
  have hc := hcomm a ha b hb hne
  rw [hroots, RootSubgroupGenerated_empty] at hc
  have hone := Subgroup.mem_bot.mp (hc
    (Subgroup.commutator_mem_commutator (curve_mem S a (kPlusPoint s)) (curve_mem S b (kPlusPoint t))))
  exact commutatorElement_eq_one_iff_commute.mp hone


private def planePoint (z : Fin 2 → k) :
    Variety.Point (affineSpaceVariety k (ULift.{u} (Fin 2))) :=
  affineSpacePoint (fun i => z i.down)

private def planeCoordinate (i : Fin 2) :
    Variety.Morphism (affineSpaceVariety k (ULift.{u} (Fin 2))) (KPlus k) where
  toFun z := kPlusPoint (z.val (ULift.up i))
  regular j := ⟨MvPolynomial.X (ULift.up i), fun z => by
    change z.val (ULift.up i) = evalPolynomial z.val (MvPolynomial.X (ULift.up i))
    rw [evalPolynomial_X]⟩

/-- The word b(t)⁻¹ a(s) b(t) a(s)⁻¹ has exactly the desired exchange order. -/
private def exchangeWord (S : Geometry K) (a b : S.roots.Root) :
    Variety.Morphism (affineSpaceVariety k (ULift.{u} (Fin 2))) K :=
  (Theory.AlgebraicGroup.commutatorMorphism K).comp
    (((Theory.AlgebraicGroup.invMorphism K).comp
      ((rootCurve S b).toVariety.comp (planeCoordinate 1))).pair
      ((rootCurve S a).toVariety.comp (planeCoordinate 0)))

private lemma exchangeWord_apply (S : Geometry K) (a b : S.roots.Root) (z : Fin 2 → k) :
    (exchangeWord S a b).toFun (planePoint z) =
      ⁅((rootCurve S b).onPoints (kPlusPoint (z 1)))⁻¹,
        (rootCurve S a).onPoints (kPlusPoint (z 0))⁆ := rfl

private lemma exchangeWord_mem (S : Geometry K)
    (hcomm : PositiveCommutatorContainment S) (a b c : S.roots.Root)
    (ha : a ∈ S.roots.positive) (hb : b ∈ S.roots.positive)
    (hsum : RootSum S a b c) (z : Variety.Point (affineSpaceVariety k (ULift.{u} (Fin 2)))) :
    (exchangeWord S a b).toFun z ∈ (S.roots.rootSubgroup c).toSubgroup := by
  apply commutator_le_sum S hcomm a b c ha hb hsum
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator
    ((S.roots.rootSubgroup b).toSubgroup.inv_mem (curve_mem S b _)) (curve_mem S a _)

private def exchangeWordInRoot (S : Geometry K)
    (hcomm : PositiveCommutatorContainment S) (a b c : S.roots.Root)
    (ha : a ∈ S.roots.positive) (hb : b ∈ S.roots.positive)
    (hsum : RootSum S a b c) :
    Variety.Morphism (affineSpaceVariety k (ULift.{u} (Fin 2))) (S.roots.rootSubgroup c).carrierVariety where
  toFun z := (S.roots.rootSubgroup c).pointEquiv.symm
    ⟨(exchangeWord S a b).toFun z, exchangeWord_mem S hcomm a b c ha hb hsum z⟩
  regular i := by
    obtain ⟨p, hp⟩ := (exchangeWord S a b).regular i
    refine ⟨p, fun z => ?_⟩
    change ((S.roots.rootSubgroup c).pointEquiv ((S.roots.rootSubgroup c).pointEquiv.symm _)).val.val i = _
    rw [Equiv.apply_symm_apply]
    exact hp z

private def exchangeParameter (S : Geometry K)
    (hcomm : PositiveCommutatorContainment S) (a b c : S.roots.Root)
    (ha : a ∈ S.roots.positive) (hb : b ∈ S.roots.positive)
    (hsum : RootSum S a b c) :
    Variety.Morphism (affineSpaceVariety k (ULift.{u} (Fin 2))) (KPlus k) :=
  (S.rootParameter c).inv.toVariety.comp (exchangeWordInRoot S hcomm a b c ha hb hsum)

private lemma exchangeParameter_spec (S : Geometry K)
    (hcomm : PositiveCommutatorContainment S) (a b c : S.roots.Root)
    (ha : a ∈ S.roots.positive) (hb : b ∈ S.roots.positive)
    (hsum : RootSum S a b c) (z : Variety.Point (affineSpaceVariety k (ULift.{u} (Fin 2)))) :
    (rootCurve S c).onPoints ((exchangeParameter S hcomm a b c ha hb hsum).toFun z) =
      (exchangeWord S a b).toFun z := by
  change (S.roots.rootSubgroup c).includePoint
    ((S.rootParameter c).hom.onPoints ((S.rootParameter c).inv.onPoints _)) = _
  rw [(S.rootParameter c).inv_hom_id]
  change ((S.roots.rootSubgroup c).pointEquiv
    ((S.roots.rootSubgroup c).pointEquiv.symm _)).val = _
  rw [Equiv.apply_symm_apply]

private lemma curve_injective (S : Geometry K) (a : S.roots.Root) :
    Function.Injective (rootCurve S a).onPoints :=
  (S.roots.rootSubgroup a).inclusion_injective.comp (S.rootParameter a).toMulEquiv.injective

private lemma curve_scale (S : Geometry K) (a : S.roots.Root)
    (z : k) (t : Variety.Point S.torus.carrierVariety) :
    (rootCurve S a).onPoints (kPlusPoint ((S.roots.rootWeight a).pointCharacter t * z)) =
      (S.torus.includePoint t)⁻¹ * (rootCurve S a).onPoints (kPlusPoint z) *
        S.torus.includePoint t :=
  ((S.realized.2.2.1 a).2 (S.rootParameter a) z t).symm

private lemma exchangeWord_scale (S : Geometry K) (a b : S.roots.Root)
    (z : Fin 2 → k) (t : Variety.Point S.torus.carrierVariety) :
    (exchangeWord S a b).toFun (planePoint
      ![(S.roots.rootWeight a).pointCharacter t * z 0,
        (S.roots.rootWeight b).pointCharacter t * z 1]) =
      (S.torus.includePoint t)⁻¹ * (exchangeWord S a b).toFun (planePoint z) *
        S.torus.includePoint t := by
  rw [exchangeWord_apply, exchangeWord_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [curve_scale, curve_scale]
  simp only [commutatorElement_def]
  group


private lemma exists_exchangePolynomial (S : Geometry K)
    (hcomm : PositiveCommutatorContainment S) (a b c : S.roots.Root)
    (ha : a ∈ S.roots.positive) (hb : b ∈ S.roots.positive)
    (hsum : RootSum S a b c) :
    ∃ p : MvPolynomial (Fin 2) k, ∀ z : Fin 2 → k,
      (rootCurve S c).onPoints (kPlusPoint (MvPolynomial.eval z p)) =
        (exchangeWord S a b).toFun (planePoint z) := by
  let f := exchangeParameter S hcomm a b c ha hb hsum
  obtain ⟨p, hp⟩ := f.regular PUnit.unit
  refine ⟨MvPolynomial.rename ULift.down p, fun z => ?_⟩
  have he : kPlusPoint (MvPolynomial.eval z (MvPolynomial.rename ULift.down p)) =
      f.toFun (planePoint z) := by
    apply Variety.Point.ext
    funext i
    cases i
    change MvPolynomial.eval z (MvPolynomial.rename ULift.down p) = _
    rw [MvPolynomial.eval_rename]
    exact (hp (planePoint z)).symm
  rw [he]
  exact exchangeParameter_spec S hcomm a b c ha hb hsum _

private lemma exchangePolynomial_scale (S : Geometry K) (a b c : S.roots.Root)
    (p : MvPolynomial (Fin 2) k)
    (hp : ∀ z : Fin 2 → k,
      (rootCurve S c).onPoints (kPlusPoint (MvPolynomial.eval z p)) =
        (exchangeWord S a b).toFun (planePoint z))
    (t : Variety.Point S.torus.carrierVariety) (x y : k) :
    MvPolynomial.eval
      (additiveBiaffineEvalPoint ((S.roots.rootWeight a).pointCharacter t * x)
        ((S.roots.rootWeight b).pointCharacter t * y)) p =
      (S.roots.rootWeight c).pointCharacter t *
        MvPolynomial.eval (additiveBiaffineEvalPoint x y) p := by
  have he : (rootCurve S c).onPoints (kPlusPoint
      (MvPolynomial.eval
        (additiveBiaffineEvalPoint ((S.roots.rootWeight a).pointCharacter t * x)
          ((S.roots.rootWeight b).pointCharacter t * y)) p)) =
      (rootCurve S c).onPoints (kPlusPoint
        ((S.roots.rootWeight c).pointCharacter t *
          MvPolynomial.eval (additiveBiaffineEvalPoint x y) p)) := by
    rw [hp, curve_scale, hp]
    exact exchangeWord_scale S a b (additiveBiaffineEvalPoint x y) t
  exact congrArg (fun z : Variety.Point (KPlus k) => z.val PUnit.unit)
    (curve_injective S c he)

private lemma sum_coefficients (S : Geometry K) (a b c : S.roots.Root)
    (hsum : RootSum S a b c) (i j : ℕ)
    (hrel : P.root (S.rootIndex c) =
      (i : ℝ) • P.root (S.rootIndex a) + (j : ℝ) • P.root (S.rootIndex b)) :
    i = 1 ∧ j = 1 := by
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨S.rootIndex c, hsum⟩
  have hzero : ((i : ℝ) - 1) • P.root (S.rootIndex a) +
      ((j : ℝ) - 1) • P.root (S.rootIndex b) = 0 := by
    rw [sub_smul (i : ℝ) (1 : ℝ) (P.root (S.rootIndex a)),
      sub_smul (j : ℝ) (1 : ℝ) (P.root (S.rootIndex b)),
      one_smul, one_smul, sub_add_sub_comm,
      ← hrel, ← show P.root (S.rootIndex c) =
        P.root (S.rootIndex a) + P.root (S.rootIndex b) from hsum, sub_self]
  obtain ⟨hi, hj⟩ := LinearIndependent.pair_iff.mp hli _ _ hzero
  exact ⟨by exact_mod_cast sub_eq_zero.mp hi, by exact_mod_cast sub_eq_zero.mp hj⟩

/-- The sum-root exchange has a single parameter-independent scalar. -/
theorem positive_rootCurve_exchange [IsAlgClosed k] (S : Geometry K)
    (hcomm : PositiveCommutatorContainment S) (a b c : S.roots.Root)
    (ha : a ∈ S.roots.positive) (hb : b ∈ S.roots.positive)
    (hsum : RootSum S a b c) :
    ∃ κ : k, ∀ s t : k,
      (rootCurve S a).onPoints (kPlusPoint s) * (rootCurve S b).onPoints (kPlusPoint t) =
        (rootCurve S b).onPoints (kPlusPoint t) *
          (rootCurve S c).onPoints (kPlusPoint (κ * s * t)) *
            (rootCurve S a).onPoints (kPlusPoint s) := by
  classical
  obtain ⟨p, hp⟩ := exists_exchangePolynomial S hcomm a b c ha hb hsum
  let d : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1
  have hsupport : ∀ m ∈ p.support, m = d := by
    intro m hm
    have hchar := additiveBiaffine_coeff_character_of_eval_scaling
      (S.roots.rootWeight a) (S.roots.rootWeight b) (S.roots.rootWeight c)
      (exchangePolynomial_scale S a b c p hp) (MvPolynomial.mem_support_iff.mp hm)
    obtain ⟨h0, h1⟩ := sum_coefficients S a b c hsum (m 0) (m 1)
      (root_eq_nat_combination_of_weight_eq S hchar)
    ext i
    fin_cases i <;> simp [d, h0, h1]
  have hpmono := MvPolynomial.eq_monomial_of_support_subset_singleton hsupport
  refine ⟨p.coeff d, fun s t => ?_⟩
  have hev : MvPolynomial.eval (additiveBiaffineEvalPoint s t) p = p.coeff d * s * t := by
    rw [hpmono, monomial_two]
    simp [d, additiveBiaffineEvalPoint]
  have he := hp (additiveBiaffineEvalPoint s t)
  rw [hev, exchangeWord_apply] at he
  change (rootCurve S c).onPoints (kPlusPoint (p.coeff d * s * t)) =
    ⁅((rootCurve S b).onPoints (kPlusPoint t))⁻¹,
      (rootCurve S a).onPoints (kPlusPoint s)⁆ at he
  rw [he]
  simp only [commutatorElement_def]
  group

/-- Positive D4 parameter laws from the actual commutator containment alone.
No nonvanishing assertion or choice of Chevalley generators is used. -/
theorem positiveRootPairParameterRelations_of_containment [IsAlgClosed k]
    (S : Geometry K) (hcomm : PositiveCommutatorContainment S) :
    PositiveRootPairParameterRelations S where
  commute a ha b hb hne hno := positive_rootCurve_commute S hcomm a b ha hb hne hno
  exchange a ha b hb c hsum := positive_rootCurve_exchange S hcomm a b c ha hb hsum

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
