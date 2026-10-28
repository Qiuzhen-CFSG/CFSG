module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs.GeometryRelations.WeylTransport

/-!
# Transport of positive-root parameter laws

Move two distinct nonopposite roots into the supplied positive system using
one simultaneous Weyl word. Its algebraic conjugation transports commutation.
For an exchange law the three individual parameter scalars give the descended
constant `cc⁻¹ * κ * ca * cb`; this constant is nonzero if κ is nonzero.
Positive exchange constants are still permitted to vanish at this stage.

Sources: GLS3 1.12.1(b,h), 1.12.7; Steinberg (1963), §2.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.RootPairGeometry
open ClassBound ClassBound.FixedOpposition.AmbientNormalizer
open CorootRealization
public noncomputable section
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

@[expose] def PairCommutes (S : Geometry K) (a b : S.roots.Root) : Prop :=
  ∀ s t : k, Commute ((rootCurve S a).onPoints (kPlusPoint s))
    ((rootCurve S b).onPoints (kPlusPoint t))

@[expose] def PairExchange (S : Geometry K) (a b c : S.roots.Root) (κ : k) : Prop :=
  ∀ s t : k,
    (rootCurve S a).onPoints (kPlusPoint s) * (rootCurve S b).onPoints (kPlusPoint t) =
      (rootCurve S b).onPoints (kPlusPoint t) *
        (rootCurve S c).onPoints (kPlusPoint (κ * s * t)) *
          (rootCurve S a).onPoints (kPlusPoint s)

theorem word_commute_iff (S : Geometry K)
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (D : SimpleCorootWordData S) (w : List (Fin 4)) (a b : S.roots.Root) :
    PairCommutes S a b ↔ PairCommutes S (wordAction S w a) (wordAction S w b) := by
  obtain ⟨ca, hca, ha⟩ := word_parameter S hu D w a
  obtain ⟨cb, hcb, hb⟩ := word_parameter S hu D w b
  let f := MulAut.conj (wordPoint D w)
  have hfa t : f ((rootCurve S a).onPoints (kPlusPoint t)) =
      (rootCurve S (wordAction S w a)).onPoints (kPlusPoint (ca * t)) := ha t
  have hfb t : f ((rootCurve S b).onPoints (kPlusPoint t)) =
      (rootCurve S (wordAction S w b)).onPoints (kPlusPoint (cb * t)) := hb t
  constructor
  · intro h s t
    have he := (h (ca⁻¹ * s) (cb⁻¹ * t)).map f
    rw [hfa, hfb] at he
    simpa only [← mul_assoc, mul_inv_cancel₀ hca, mul_inv_cancel₀ hcb, one_mul] using he
  · intro h s t
    apply Commute.of_map f.injective
    rw [hfa, hfb]
    exact h _ _

theorem word_exchange_descend (S : Geometry K)
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (D : SimpleCorootWordData S) (w : List (Fin 4)) (a b c : S.roots.Root)
    (κ : k) (he : PairExchange S (wordAction S w a) (wordAction S w b)
      (wordAction S w c) κ) :
    ∃ κ' : k, (κ ≠ 0 → κ' ≠ 0) ∧ PairExchange S a b c κ' := by
  obtain ⟨ca, hca, ha⟩ := word_parameter S hu D w a
  obtain ⟨cb, hcb, hb⟩ := word_parameter S hu D w b
  obtain ⟨cc, hcc, hc⟩ := word_parameter S hu D w c
  refine ⟨cc⁻¹ * κ * ca * cb, fun hκ =>
    mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero hcc) hκ) hca) hcb, ?_⟩
  intro s t
  let f := MulAut.conj (wordPoint D w)
  apply f.injective
  simp only [map_mul]
  change
    (wordPoint D w * (rootCurve S a).onPoints (kPlusPoint s) * (wordPoint D w)⁻¹) *
      (wordPoint D w * (rootCurve S b).onPoints (kPlusPoint t) * (wordPoint D w)⁻¹) =
    (wordPoint D w * (rootCurve S b).onPoints (kPlusPoint t) * (wordPoint D w)⁻¹) *
      (wordPoint D w * (rootCurve S c).onPoints
        (kPlusPoint (cc⁻¹ * κ * ca * cb * s * t)) * (wordPoint D w)⁻¹) *
      (wordPoint D w * (rootCurve S a).onPoints (kPlusPoint s) * (wordPoint D w)⁻¹)
  rw [ha, hb, hc]
  have hs : cc * (cc⁻¹ * κ * ca * cb * s * t) = κ * (ca * s) * (cb * t) := by
    field_simp
  rw [hs]
  exact he _ _

omit [IsAlgClosed k] in
theorem wordAction_positive_pair (S : Geometry K) (a b : S.roots.Root)
    (hab : a ≠ b) (hop : b ≠ S.roots.neg a) :
    ∃ w : List (Fin 4), wordAction S w a ∈ S.roots.positive ∧
      wordAction S w b ∈ S.roots.positive := by
  have hop' : S.rootIndex b ≠
      (typeDRootPairing 2).reflectionPerm (S.rootIndex a) (S.rootIndex a) := by
    rw [← S.based.2.2.1]
    exact S.rootIndex.injective.ne hop
  obtain ⟨w, ha, hb⟩ := d4_pair_positive_word _ _ (S.rootIndex.injective.ne hab) hop'
  refine ⟨w, (S.positive _).mpr ?_, (S.positive _).mpr ?_⟩
  · simpa only [wordAction, Equiv.trans_apply, Equiv.apply_symm_apply] using ha
  · simpa only [wordAction, Equiv.trans_apply, Equiv.apply_symm_apply] using hb

theorem all_commute_of_positive (S : Geometry K)
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (D : SimpleCorootWordData S) (hpos : PositiveRootPairParameterRelations S)
    (a b : S.roots.Root) (hab : a ≠ b) (hop : b ≠ S.roots.neg a)
    (hs : ¬ ∃ c, RootSum S a b c) : PairCommutes S a b := by
  obtain ⟨w, ha, hb⟩ := wordAction_positive_pair S a b hab hop
  apply (word_commute_iff S hu D w a b).mpr
  apply hpos.commute _ ha _ hb ((wordAction S w).injective.ne hab)
  rintro ⟨c, hc⟩
  obtain ⟨c, rfl⟩ := (wordAction S w).surjective c
  exact hs ⟨c, (wordAction_sum_iff S w a b c).mp hc⟩

theorem all_exchange_of_positive (S : Geometry K)
    (hu : ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (D : SimpleCorootWordData S) (hpos : PositiveRootPairParameterRelations S)
    (a b c : S.roots.Root) (hs : RootSum S a b c) :
    ∃ κ : k, PairExchange S a b c κ := by
  obtain ⟨w, ha, hb⟩ := wordAction_positive_pair S a b
    (rootSum_ne S hs) (rootSum_nonopposite S hs)
  obtain ⟨κ, hk⟩ := hpos.exchange _ ha _ hb _ ((wordAction_sum_iff S w a b c).mpr hs)
  obtain ⟨κ', _, hk'⟩ := word_exchange_descend S hu D w a b c κ hk
  exact ⟨κ', hk'⟩


end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.RootPairGeometry
