module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.Order
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.FourCompletion

/-!
# Prepared U₄ recognition at odd ordinary degree

The original quotient action makes the outer index odd when m is odd. Apply
the same-extension Thompson equality, construct the full source extension,
and discharge the order input of the published completion recognizer. Both
ordinary orientations remain; the recognized parameter is 2^m and n = 2m.

This specialized route has no remaining realization, fusion, centralizer,
parity or order callback. Even-degree and degree-two rows retain their
original source obligations, including q = 4.

Source: Aschbacher--Smith 5.3.2--4 and F.4.24,38,43, pp.659,287,294,296.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse))
include d h hH hp hc

/-- At odd ordinary degree the source proves the order equality on any
specified marked extension; no parity or order input remains. -/
theorem Preparation.unitaryFour_ordinary_order_of_odd (hmOdd : Odd m)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm) :
    Nat.card G = Nat.card r.extension.carrier :=
  d.unitaryFour_order_of_odd_outer h hH hp m hm (Or.inl hc) r
    (d.unitaryFour_ordinary_outer_odd_of_odd h hH hp m hm hc hmOdd r)

/-- The original ordinary odd-degree row constructs the genuine full
extension and proves the ambient order comparison, with both orientations. -/
theorem Preparation.unitaryFour_ordinary_source_of_odd (hmOdd : Odd m) :
    ∃ E : FourExtension m hm, Compatible L (residual H) E ∧
      Nat.card G ≤ Nat.card E.carrier := by
  let r := d.unitaryFourNormalizerMarking h hH hp m hm (Or.inl hc)
  exact ⟨r.extension,r.full_comparison,
    (d.unitaryFour_ordinary_order_of_odd h hH hp m hm hc hmOdd r).le⟩

/-- The actual faithful completion, whole image overlap and both native
coset bounds, after proving the ambient order on the same constructed carrier. -/
theorem Preparation.unitaryFour_ordinary_completion_of_odd (hmOdd : Odd m) :
    let E := (d.unitaryFourNormalizerMarking h hH hp m hm (Or.inl hc)).extension
    1 < m ∧ n = 2*m ∧
      ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
          (G := NormalizerJoin L (residual H)),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (NormalizerJoin L (residual H)) ≤ Nat.card E.carrier ∧
        ∀ i : Bool, Nat.card (NormalizerJoin L (residual H) ⧸ c.cosetFamily i) ≤
          Nat.card (ProjectiveGroup m hm ⧸ SourceExtension.nativeFamily
            (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm) i) :=
  d.unitaryFour_constructed_completion h hH hp m hm (Or.inl hc)
    (d.unitaryFour_ordinary_order_of_odd h hH hp m hm hc hmOdd _).le

/-- Apply the published completion recognizer after discharging its source
and order inputs in the ordinary odd-degree branch. The unitary exponent is m. -/
theorem Preparation.unitaryFour_ordinary_recognition_of_odd (hmOdd : Odd m) :
    1 < m ∧ n = 2*m ∧ Nat.card G = Nat.card
      (d.unitaryFourNormalizerMarking h hH hp m hm (Or.inl hc)).extension.carrier ∧
      ClassicalGroup.IsPSU G 4 (2^m) :=
  d.unitaryFour_constructed_recognition h hH hp m hm (Or.inl hc)
    (d.unitaryFour_ordinary_order_of_odd h hH hp m hm hc hmOdd _).le

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

