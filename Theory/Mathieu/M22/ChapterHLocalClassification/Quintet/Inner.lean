module

public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Translations
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Conjugation

/-!
# Discharging the native quintet inner-intersection inputs

The native inner M22 is normal in the pair stabilizer, while the intrinsic
quintet two-core is normalized by Q. Their intersection A0 is consequently
normalized by Q. The certified source translation exchanging the two deleted
points lies in that core, giving index two for A0. The existing native inner
involution displacement theorem then gives fixed dimension six on the actual
M22 cocode. These arguments construct the literal downstream `InnerInputs`
without assuming the quintet core orders, quotient or conjugation modules.

Source: Aschbacher--Smith H.14.3(1--2), H.14.4(2--3), and their use in H.15.4,
printed pp.397--400, combined manuscript of 1 March 2004.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode MathieuCode.M22Quintet
open MathieuCode.M22Quintet.CocodeTransfer Representation.BinaryOffender
namespace Sporadic.Mathieu.M22ChapterH.Quintet

/-- The intrinsic inner intersection is normal only in the quintet stabilizer. -/
theorem innerIntersection_normalizer :
    Q ≤ Subgroup.normalizer (A0 : Set m22PairStabilizer) := by
  let : L.Normal := inner_normal
  exact (le_inf Q_le_normalizer_K
    (show Q ≤ Subgroup.normalizer (L : Set m22PairStabilizer) by
      rw [Subgroup.normalizer_eq_top]; exact le_top)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

/-- The source translation exchanging the deleted pair belongs to the intrinsic core. -/
theorem pairSwap_mem_core : pairSwap ∈ K := Sextet.outerTranslations_le_core pairSwap_mem

/-- Thus the intrinsic core, without any prior order identification, has inner index two. -/
theorem innerIntersection_core_index : A0.relIndex K = 2 :=
  innerIntersection_index K pairSwap_mem_core

/-- H.14.4's native inner involution displacement gives the exact fixed dimension. -/
theorem inner_involution_fixed (i : m22PairStabilizer) (hi : i ∈ L) (ho : orderOf i = 2) :
    Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i)) = 6 := by
  have hd := m22Outer_cocode_involution_displacement_of_fixed_zero i ho
    ((m22ToPairStabilizer_mem_range_iff_fixed_zero i).mp hi)
  have he := fixedCodim_add_finrank m22OuterCocodeRepresentation (Subgroup.zpowers i)
  rw [hd, finrank_m22Cocode] at he
  omega

/-- The literal downstream witness, with normality, index and involution premise discharged. -/
theorem innerInputs : InnerInputs where
  normalizer := innerIntersection_normalizer
  index := innerIntersection_core_index
  involution_fixed i hi ho := inner_involution_fixed i hi.2 ho

end Sporadic.Mathieu.M22ChapterH.Quintet
