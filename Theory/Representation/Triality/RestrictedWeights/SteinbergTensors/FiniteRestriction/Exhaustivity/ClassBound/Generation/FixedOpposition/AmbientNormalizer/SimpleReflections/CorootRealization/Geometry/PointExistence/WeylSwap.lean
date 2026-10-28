module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Geometry.PointExistence.Relations
public import Theory.AlgebraicGroup.RootSubgroups.Conjugation
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup
public import Theory.AlgebraicGroup.Borel.OppositeBigCell.Separation

/-!
# Calibrating a simple-root pair from subgroup transport

Let `x` and `y` parametrize the actual opposite root subgroups and put
`w = x(1)y(1)x(1)`. If conjugation by `w` carries the positive subgroup onto
the negative subgroup, its action on the two algebraic parametrizations is
multiplication by a scalar. The three-factor word and trivial intersection
of the opposite root groups force that scalar to be one. Trivial intersection
is proved here from the supplied opposite Borel big cell.

Consequently any nonzero three-factor word transporting the two subgroups
can be calibrated by rescaling both parametrizations. Subgroup transport is
an explicit hypothesis in these results. Its existence from the intrinsic
rank-one geometry remains necessary for unconditional parameter existence.
No compatible SL₂ map or diagonal-word relation is assumed.

Sources: GLS3, Theorem 1.12.1(h), Proposition 1.3.5(a), and the root geometry
in Theorem 1.9.5 and Remarks 1.9.6, `refs/KGroup/GLS3/Chapter1.tex`;
Steinberg §6, `refs/KGroup/GLS3/Chapter2St2.tex`.
-/

open Theory.AlgebraicGroup

namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

private lemma conjugate_parameter_scalar
    {X Y : ClosedSubgroup K}
    (x : OneParameterParametrization X.carrierVariety)
    (y : OneParameterParametrization Y.carrierVariety)
    (g : Variety.Point K) (h : X.conjugate g = Y) :
    ∃ c : k, c ≠ 0 ∧ ∀ a : k,
      g * X.inclusion.onPoints (x.value a) * g⁻¹ =
        Y.inclusion.onPoints (y.value (c * a)) := by
  subst Y
  let z : OneParameterParametrization (X.conjugate g).carrierVariety :=
    (X.conjugateIso g).comp x
  obtain ⟨c, ⟨hc, hcz⟩, _⟩ := oneParameterParametrization_eq_rescale y z
  refine ⟨c, hc, fun a => ?_⟩
  rw [← hcz a]
  exact (X.conjugateIso_hom_inclusion_apply g (x.value a)).symm

end Theory.AlgebraicGroup

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- The two actual simple-root groups meet only at the identity. -/
public lemma simpleRoot_opposite_disjoint (S : Geometry K) (i : Fin 4) :
    Disjoint (S.roots.rootSubgroup (S.simpleRoot i).val).toSubgroup
      (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).toSubgroup := by
  have hpos : (S.simpleRoot i).val ∈ S.roots.positive :=
    ((S.realized.2.2.2.2.2.2.2.2.2.2.2.1 _).mp (S.simpleRoot i).property).1
  apply (show Disjoint (RootSubgroupGenerated S.roots S.roots.positive)
      S.bigCell.data.Bopp.toSubgroup from
    disjoint_iff.mpr (S.bigCell.positive_inf_negativeBorel_eq_bot S.maximalTorus.1)).mono
  · exact rootSubgroup_le_RootSubgroupGenerated S.roots hpos
  · apply le_trans (rootSubgroup_le_RootSubgroupGenerated S.roots ?_)
      S.bigCell.negative_le_borel
    change S.roots.neg (S.roots.neg (S.simpleRoot i).val) ∈ S.roots.positive
    rwa [S.realized.neg_neg]

namespace SimpleRootSL2Parameters
variable {S : Geometry K} {i : Fin 4} (P : SimpleRootSL2Parameters S i)

private noncomputable abbrev ambientMap (_P : SimpleRootSL2Parameters S i) :
    Target (S := S) (i := i) →* Variety.Point K :=
  (oppositePairGeneratedSubgroup
    (S.roots.rootSubgroup (S.simpleRoot i).val)
    (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val))).inclusion.onPoints

omit [IsAlgClosed k] in
private lemma ambient_upper (a : k) : P.ambientMap (P.upper a) =
    (S.roots.rootSubgroup (S.simpleRoot i).val).inclusion.onPoints (P.plus.value a) := by
  rw [P.upper_eq]
  exact oppositePairPlusMorphism_inclusion_apply _ _ _

omit [IsAlgClosed k] in
private lemma ambient_lower (a : k) : P.ambientMap (P.lower a) =
    (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).inclusion.onPoints
      (P.minus.value a) := by
  rw [P.lower_eq]
  exact oppositePairMinusMorphism_inclusion_apply _ _ _

omit [IsAlgClosed k] in
private lemma lower_injective : Function.Injective P.lower := by
  intro a b h
  have h' := congrArg P.ambientMap h
  rw [P.ambient_lower, P.ambient_lower] at h'
  have h'' := (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).inclusion_injective h'
  have hp := congrArg P.minus.inv.onPoints h''
  change P.minus.inv.onPoints (P.minus.hom.onPoints (kPlusPoint a)) =
    P.minus.inv.onPoints (P.minus.hom.onPoints (kPlusPoint b)) at hp
  rw [P.minus.hom_inv_id, P.minus.hom_inv_id] at hp
  exact congrArg (fun z : Variety.Point (KPlus k) => z.val PUnit.unit) hp

/-- The three-factor word regarded as a point of the original group. -/
public noncomputable abbrev ambientWeyl : Variety.Point K :=
  (oppositePairGeneratedSubgroup
    (S.roots.rootSubgroup (S.simpleRoot i).val)
    (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val))).inclusion.onPoints P.weyl

/-- Setwise transport by the three-factor word forces exact, same-parameter
transport of the two curves. This proves the scalar calibration. -/
public lemma weylSwaps_of_conjugate_eq
    (h : (S.roots.rootSubgroup (S.simpleRoot i).val).conjugate
      P.ambientWeyl =
      S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)) : P.WeylSwaps := by
  let w := P.ambientMap P.weyl
  let x := fun a => P.ambientMap (P.upper a)
  let y := fun a => P.ambientMap (P.lower a)
  have hw : w * w = 1 := by
    dsimp [w]
    rw [← map_mul, P.weyl_sq, map_one]
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  obtain ⟨c, _hc, hc⟩ := conjugate_parameter_scalar P.plus P.minus w h
  have hcx (a) : w * x a * w = y (c * a) := by
    dsimp [x, y]
    rw [P.ambient_upper, P.ambient_lower]
    simpa only [hwinv] using hc a
  have hx1 : x 1 ∈ (S.roots.rootSubgroup (S.simpleRoot i).val).toSubgroup := by
    rw [show x 1 = _ from P.ambient_upper 1]
    exact ((S.roots.rootSubgroup (S.simpleRoot i).val).pointEquiv (P.plus.value 1)).property
  have hy (a) : y a ∈ (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).toSubgroup := by
    rw [show y a = _ from P.ambient_lower a]
    exact ((S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).pointEquiv
      (P.minus.value a)).property
  have hwy : w * y 1 * w ∈ (S.roots.rootSubgroup (S.simpleRoot i).val).toSubgroup := by
    have hy' := hy 1
    change y 1 ∈ S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val) at hy'
    rw [← h, ClosedSubgroup.mem_conjugate_iff] at hy'
    change w⁻¹ * y 1 * w ∈ _ at hy'
    simpa only [hwinv] using hy'
  have hxsq : x 1 * x 1 = 1 := by
    dsimp [x]
    rw [← map_mul, P.upper_sq, map_one]
  have hwdef : w = x 1 * y 1 * x 1 := by
    dsimp [w, x, y]
    rw [weyl, map_mul, map_mul]
  have hword : (w * x 1 * w) * y 1 = (w * y 1 * w) * x 1 := by
    simp only [hwdef, mul_assoc, hxsq, mul_one]
  have hinter : y (c * 1) * y 1 = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← disjoint_iff.mp (simpleRoot_opposite_disjoint S i)]
    constructor
    · rw [← hcx 1, hword]
      exact (S.roots.rootSubgroup (S.simpleRoot i).val).mul_mem hwy hx1
    · exact (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).mul_mem (hy _) (hy _)
  have hc1 : c = 1 := by
    have heq : P.lower c * P.lower 1 = 1 := by
      apply (oppositePairGeneratedSubgroup _ _).inclusion_injective
      simpa only [map_mul, map_one, mul_one] using hinter
    have : P.lower c = P.lower 1 := by
      calc
        P.lower c = (P.lower c * P.lower 1) * P.lower 1 := by
          rw [mul_assoc, P.lower_sq, mul_one]
        _ = P.lower 1 := by rw [heq, one_mul]
    exact P.lower_injective this
  intro a
  apply (oppositePairGeneratedSubgroup _ _).inclusion_injective
  simpa only [map_mul, hc1, one_mul] using hcx a

end SimpleRootSL2Parameters

/-- Rescaling the two curves jointly calibrates any nonzero three-factor
word which interchanges the actual root subgroups. -/
public lemma exists_weylSwapParameters_of_conjugate_word (S : Geometry K) (i : Fin 4)
    (a b : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (S.roots.rootSubgroup (S.simpleRoot i).val).conjugate
      ((S.roots.rootSubgroup (S.simpleRoot i).val).inclusion.onPoints
          ((S.rootParameter (S.simpleRoot i).val).value a) *
        (S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).inclusion.onPoints
          ((S.rootParameter (S.roots.neg (S.simpleRoot i).val)).value b) *
        (S.roots.rootSubgroup (S.simpleRoot i).val).inclusion.onPoints
          ((S.rootParameter (S.simpleRoot i).val).value a)) =
      S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)) :
    ∃ P : SimpleRootSL2Parameters S i, P.WeylSwaps := by
  let P : SimpleRootSL2Parameters S i :=
    { plus := (S.rootParameter (S.simpleRoot i).val).rescale a ha
      minus := (S.rootParameter (S.roots.neg (S.simpleRoot i).val)).rescale b hb }
  refine ⟨P, P.weylSwaps_of_conjugate_eq ?_⟩
  convert h using 1
  congr 1
  change P.ambientMap (P.upper 1 * P.lower 1 * P.upper 1) = _
  rw [map_mul, map_mul, P.ambient_upper, P.ambient_lower]
  simp only [P, oneParameterParametrization_rescale_apply, mul_one]

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
