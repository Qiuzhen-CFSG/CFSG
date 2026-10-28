module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.GeometryRelations.ParameterLaws

/-!
# Nonvanishing from the actual rank-one geometry

For a root sum a+b=c, first transport a to a simple root. If the two root
groups commuted, the absent-sum law would also make U(-a) commute with U(b).
The chart word in U(a) and U(-a) would fix U(b), but root transport sends it
to U(c). Equality is impossible: a realized root subgroup determines its
root weight, and c differs from b. Thus an exchange constant cannot be zero.

Only the supplied rank-one charts (through their coroot words), actual
root-subgroup uniqueness, and positive-root laws enter this argument.
Sources: GLS3 1.9.2, 1.12.1(b,h,k); Steinberg (1963), §2.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.RootPairGeometry
open ClassBound ClassBound.FixedOpposition.AmbientNormalizer
open CorootRealization
public noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
theorem rootCurve_surjective (S : Geometry K) (a : S.roots.Root)
    (x : K.Point) (hx : x ∈ S.roots.rootSubgroup a) :
    ∃ t, (rootCurve S a).onPoints (kPlusPoint t) = x := by
  obtain ⟨z, hz⟩ := (S.rootParameter a).toMulEquiv.surjective
    ((S.roots.rootSubgroup a).pointEquiv.symm ⟨x, hx⟩)
  refine ⟨Multiplicative.toAdd (additiveGroupPointEquiv k z), ?_⟩
  change (S.roots.rootSubgroup a).includePoint ((S.rootParameter a).hom.onPoints
    ((additiveGroupPointEquiv k).symm (additiveGroupPointEquiv k z))) = x
  rw [Equiv.symm_apply_apply]
  change (S.roots.rootSubgroup a).includePoint ((S.rootParameter a).toMulEquiv z) = x
  rw [hz]
  exact congrArg Subtype.val ((S.roots.rootSubgroup a).pointEquiv.apply_symm_apply ⟨x, hx⟩)

omit [IsAlgClosed k] in
theorem pairCommutes_points (S : Geometry K) {a b : S.roots.Root}
    (h : PairCommutes S a b) (x y : K.Point)
    (hx : x ∈ S.roots.rootSubgroup a) (hy : y ∈ S.roots.rootSubgroup b) :
    Commute x y := by
  obtain ⟨s, rfl⟩ := rootCurve_surjective S a x hx
  obtain ⟨t, rfl⟩ := rootCurve_surjective S b y hy
  exact h s t

omit [IsAlgClosed k] in
theorem rootSubgroup_injective (S : Geometry K) : Function.Injective S.roots.rootSubgroup := by
  intro a b h
  apply S.realized.1
  apply rootWeightEquation_unique S.torus (S.roots.rootSubgroup a) ⟨S.rootParameter a⟩
    (S.realized.2.2.1 a).2
  rw [h]
  exact (S.realized.2.2.1 b).2

omit [IsAlgClosed k] [CharP k 2] in
theorem conjugate_eq_of_commutes (X : ClosedSubgroup K) (g : K.Point)
    (hc : ∀ x : K.Point, x ∈ X → Commute g x) : X.conjugate g = X := by
  apply SetLike.coe_injective
  ext x
  change x ∈ X.conjugate g ↔ x ∈ X
  rw [X.mem_conjugate_iff]
  constructor
  · intro hx
    have he : g * (g⁻¹ * x * g) * g⁻¹ = g⁻¹ * x * g := by
      rw [(hc _ hx).eq]
      group
    have he' : x = g⁻¹ * x * g := by
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using he
    rwa [← he'] at hx
  · intro hx
    rw [(hc x hx).inv_mul_cancel]
    exact hx

omit [IsAlgClosed k] in
theorem simpleWord_conjugate_eq_of_pairCommutes (S : Geometry K)
    (D : SimpleCorootWordData S) (i : Fin 4) (b : S.roots.Root)
    (hp : PairCommutes S (S.simpleRoot i).val b)
    (hm : PairCommutes S (S.roots.neg (S.simpleRoot i).val) b) :
    (S.roots.rootSubgroup b).conjugate ((D.parameters i).word 1) =
      S.roots.rootSubgroup b := by
  apply conjugate_eq_of_commutes
  intro x hx
  have hplus (t : k) := pairCommutes_points S hp
    ((S.roots.rootSubgroup (S.simpleRoot i).val).includePoint ((D.parameters i).plus.value t)) x
    ((S.roots.rootSubgroup _).pointEquiv _).property hx
  have hminus (t : k) := pairCommutes_points S hm
    ((S.roots.rootSubgroup (S.roots.neg (S.simpleRoot i).val)).includePoint
      ((D.parameters i).minus.value t)) x
    ((S.roots.rootSubgroup _).pointEquiv _).property hx
  exact ((hplus _).mul_left (hminus _)).mul_left (hplus _)

theorem simple_sum_not_commute (S : Geometry K)
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (D : SimpleCorootWordData S) (hpos : PositiveRootPairParameterRelations S)
    (i : Fin 4) (b c : S.roots.Root) (hs : RootSum S (S.simpleRoot i).val b c) :
    ¬ PairCommutes S (S.simpleRoot i).val b := by
  intro hp
  have hm : PairCommutes S (S.roots.neg (S.simpleRoot i).val) b :=
    all_commute_of_positive S hu D hpos _ _ (rootSum_nonopposite S hs).symm
      (by simpa only [S.realized.neg_neg] using (rootSum_ne S hs).symm)
      (rootSum_no_difference S hs)
  have hfix := simpleWord_conjugate_eq_of_pairCommutes S D i b hp hm
  have hmove := simpleWord_conjugate_rootSubgroup_of_unique S hu D i b
  rw [rootSum_reflection S hs, hfix] at hmove
  exact rootSum_right_ne S hs ((rootSubgroup_injective S hmove).symm)

theorem rootSum_not_commute (S : Geometry K)
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (D : SimpleCorootWordData S) (hpos : PositiveRootPairParameterRelations S)
    (a b c : S.roots.Root) (hs : RootSum S a b c) : ¬ PairCommutes S a b := by
  intro hab
  obtain ⟨w, i, hi⟩ := wordAction_to_simple S a
  have hs' := (wordAction_sum_iff S w a b c).mpr hs
  have hab' := (word_commute_iff S hu D w a b).mp hab
  rw [hi] at hs' hab'
  exact simple_sum_not_commute S hu D hpos i _ _ hs' hab'

omit [IsAlgClosed k] in
theorem pairExchange_zero_commutes (S : Geometry K) (a b c : S.roots.Root)
    (h : PairExchange S a b c 0) : PairCommutes S a b := by
  intro s t
  have he := h s t
  have hz : kPlusPoint (0 : k) = 1 := by
    apply Variety.Point.ext
    funext i
    cases i
    rfl
  exact (commute_iff_eq _ _).mpr (by
    simpa only [zero_mul, hz, map_one, mul_one] using he)


end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.RootPairGeometry
