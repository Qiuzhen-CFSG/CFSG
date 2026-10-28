module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.FoldedRoots
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl

/-!
# Pinned root markings and the highest-root class in binary triality

The folded long and short curves agree with the faithful pinned SL₂ root
maps after the actual elementary restriction and central quotient. The
rotation in the relative Weyl group sends root position 11 to the central
simple root at position 3. The fixed-field/base-field equivalence therefore
identifies every nonidentity highest-root element as a long-root involution.
The checked unipotent-center calculation gives the same conclusion for the
literal embedded center, including q = 2.

Source: GLS3 §§2.4–2.6 (`refs/KGroup/GLS3/chapter2.tex`), and the inner
triality clauses of Aschbacher–Smith 16.1.4(1), 16.1.6 and 16.5.13–14
(`refs/quasithin.pdf`, printed pp.1171–1172 and 1201–1203).
-/

public section

noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
namespace Triality.Standard.EvenInvolutionGeometry
open Parabolics ConcreteBruhat PositiveCoordinates
open RadicalCoordinates.Centers RadicalCoordinates.LeviCommutators

variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

theorem foldedLong_zero_eq_longRoot (t : GaloisField 2 n) :
    long P rfl 0 (baseFieldEquivFixed P t) = longRoot n hn t := by
  change toCarrier P (longElementary P rfl 0 (baseFieldEquivFixed P t)) =
    toCarrier P (sl2ElementaryLift P rfl (longRankOneFixed n hn)
      (Matrix.SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd t)))
  apply congrArg (toCarrier P)
  apply Subtype.ext
  apply Subtype.ext
  exact (longElementary_val P rfl 0 (baseFieldEquivFixed P t)).trans
    ((curve_simple P 1 _).trans (longRankOneFixed_upper_val n hn t).symm)

theorem foldedShort_zero_eq_shortRoot (t : ExtensionField P) :
    short P rfl 0 t = shortRoot n hn t := by
  change toCarrier P (shortElementary P rfl 0 t) =
    toCarrier P (sl2ElementaryLift P rfl (shortRankOneFixed n hn)
      (Matrix.SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd t)))
  apply congrArg (toCarrier P)
  apply Subtype.ext
  apply Subtype.ext
  refine (shortElementary_val P rfl 0 t).trans ?_
  change curve P (simplePosition 0) t * curve P (simplePosition 2) _ *
    curve P (simplePosition 3) _ = _
  exact (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (curve_simple P 0 t)
      (curve_simple P 2 (fieldFrobenius P t)))
    (curve_simple P 3 (fieldFrobenius P (fieldFrobenius P t)))).trans
      (shortRankOneFixed_upper_val n hn t).symm

private theorem rotation_highest_root :
    (rootRepresentative (.r 1)).val (rootIndex 11) = rootIndex 3 := by
  change ((foldedRootReflection .arms * foldedRootReflection .central) ^ (1 : ℕ)).val
    (rootIndex 11) = rootIndex 3
  rw [pow_one]
  change rootReflection 0 (rootReflection 2 (rootReflection 3
    (rootReflection 1 (rootIndex 11)))) = rootIndex 3
  simp only [← rootEnumeration_positiveIndex 11, rootReflection,
    ← rootEnumeration_reflectionTable]
  rfl

private theorem highestHom_conjugate_long (Q : Parameters) (hp : Q.prime = 2)
    (t : fixedField Q) :
    weylRepresentative Q hp (.r 1) * highestHom Q hp (Multiplicative.ofAdd t) *
      (weylRepresentative Q hp (.r 1))⁻¹ = long Q hp 0 t := by
  have hs : splitRepresentative Q hp (.r 1) * curve Q 11 t.val *
      (splitRepresentative Q hp (.r 1))⁻¹ = longSplit Q 0 t := by
    apply Subtype.ext
    change (splitRepresentative Q hp (.r 1)).val * (curve Q 11 t.val).val *
        (splitRepresentative Q hp (.r 1)).val⁻¹ = (curve Q 3 t.val).val
    simp only [curve_unit]
    rw [splitRepresentative_rootCurveUnit_conjugation, rotation_highest_root]
  have he : weylElementary Q hp (.r 1) * elementaryHighestHom Q hp (Multiplicative.ofAdd t) *
      (weylElementary Q hp (.r 1))⁻¹ = longElementary Q hp 0 t := by
    apply (show Function.Injective (elementaryInclusion Q) from
      fun _ _ h => Subtype.ext (Subtype.ext h))
    simpa only [map_mul, map_inv, elementaryHighestHom_val, longElementary_val,
      toAdd_ofAdd, splitRepresentative] using hs
  simpa only [map_mul, map_inv, weylRepresentative, long, highestHom,
    MonoidHom.comp_apply] using congrArg (toCarrier Q) he

theorem highestHom_conjugate_longRoot (t : GaloisField 2 n) :
    weylRepresentative P rfl (.r 1) *
      highestHom P rfl (Multiplicative.ofAdd (baseFieldEquivFixed P t)) *
      (weylRepresentative P rfl (.r 1))⁻¹ = longRoot n hn t :=
  (highestHom_conjugate_long P rfl (baseFieldEquivFixed P t)).trans
    (foldedLong_zero_eq_longRoot n hn t)

theorem isLongRootInvolution_of_mem_highestRoot {r : BinaryCarrier n hn}
    (hr : r ∈ highestRoot P) (hne : r ≠ 1) : IsLongRootInvolution n hn r := by
  rw [← highestHom_range P rfl] at hr
  obtain ⟨z, rfl⟩ := hr
  obtain ⟨t, ht⟩ := (baseFieldEquivFixed P).surjective z.toAdd
  have hz : z = Multiplicative.ofAdd (baseFieldEquivFixed P t) :=
    congrArg Multiplicative.ofAdd ht.symm
  subst z
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    exact hne (by rw [(baseFieldEquivFixed P).map_zero]; exact map_one (highestHom P rfl))
  exact ⟨t, ht0, (isConj_iff.mpr ⟨weylRepresentative P rfl (.r 1),
    highestHom_conjugate_longRoot n hn t⟩).symm⟩

theorem isLongRootInvolution_of_mem_center_unipotent {r : BinaryCarrier n hn}
    (hr : r ∈ (Subgroup.center (unipotent P)).map (unipotent P).subtype)
    (hne : r ≠ 1) : IsLongRootInvolution n hn r :=
  isLongRootInvolution_of_mem_highestRoot n hn
    (embedded_center_unipotent P rfl ▸ hr) hne

theorem IsLongRootInvolution.of_isConj {r s : BinaryCarrier n hn}
    (hr : IsLongRootInvolution n hn r) (h : IsConj r s) :
    IsLongRootInvolution n hn s := by
  obtain ⟨t, ht, hc⟩ := hr
  exact ⟨t, ht, hc.trans h⟩

theorem IsShortRootInvolution.of_isConj {r s : BinaryCarrier n hn}
    (hr : IsShortRootInvolution n hn r) (h : IsConj r s) :
    IsShortRootInvolution n hn s := by
  obtain ⟨t, ht, hc⟩ := hr
  exact ⟨t, ht, hc.trans h⟩

end Triality.Standard.EvenInvolutionGeometry
