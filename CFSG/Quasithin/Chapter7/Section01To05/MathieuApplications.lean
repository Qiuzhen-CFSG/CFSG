module

public import CFSG.Quasithin.Chapter7.Section01To05.WeakClosure
public import CFSG.Quasithin.Chapter7.Section01To05.M23Span
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient

/-!
# Marked Mathieu applications of the terminal contradiction

The code application uses the actual native M₂₃ representation and discharges
H.16.8 with `m23Code_fixedSpan_bound`. The M₁₂ application retains the
original residual/module markings and constructs the full ambient extension;
its native rank, outer-fusion and outer fixed-subgroup rows remain explicit
inputs owned by the H.11 source assembly. Both applications still require
the global bounds from 7.2–7.4, so neither asserts 7.5.4 from the FSU alone.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
7.5.4 with H.11.1(4) and H.16.8, printed pp.700,392–393,405.
-/

public section
namespace CFSG.Quasithin.Chapter7
open Subgroup Representation.BinaryOffender ChapterE
open scoped IsMulCommutative

private theorem card_sixteen_of_rank_four {X : Type*} [Group X] [Finite X]
    (I : Subgroup X) (hI : IsElementaryAbelian 2 I) (hrank : rank I = 4) :
    Nat.card I = 16 := by
  let _ : IsElementaryAbelian 2 I := hI
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 I).exists_card_eq
  have hn4 : n = 4 := by
    simpa only [rank, hn, Nat.log_pow Nat.one_lt_two] using hrank
  rw [hn, hn4]
  rfl

/-- The M₂₃ code application of the terminal fixed-span contradiction.
The remaining native input is exactly H.16.8 for elementary sixteens. -/
theorem not_m23Code_of_native_bound
    {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hq : primeRank 2 (Automizer V) ≤ 4) (hw : globalW V T ≤ 2)
    (hr : 6 ≤ globalR V) (hm : 2 < localM V)
    (hnative : ∀ A : Subgroup Sporadic.Mathieu.M23, IsElementaryAbelian 2 A →
      Nat.card A = 16 → Module.finrank (ZMod 2)
        (MathieuCode.Code ⧸ fixedSpaceSpan MathieuCode.m23CodeRepresentation A) ≤ 1) :
    ¬ MathieuCode.IsM23Code (automizerRepresentation V) := by
  intro hmodel
  apply m23_exclusion_of_fixedSpan_bound hT hFF hq hw hr hm
  intro I hI hcard
  exact ChapterH.Section13To16.m23Code_fixedSpan_bound_of_native
    (automizerRepresentation V) hmodel hnative I hI
    (card_sixteen_of_rank_four I hI hcard)

/-- The M₁₂ heart application, preserving the actual residual and module
markings. The ambient extension is constructed; only the native rank,
outer-fusion and fixed-subgroup rows from H.11 remain explicit. -/
theorem not_m12Heart_of_native_rows
    {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hq : primeRank 2 (Automizer V) ≤ 4) (hw : globalW V T ≤ 2)
    (hr : 6 ≤ globalR V) (hm : 2 < localM V)
    (hinner : primeRank 2 Sporadic.Mathieu.M12 ≤ 3)
    (hfusion : ChapterH.Section10To12.M12Calculations.LocalActors.OuterInvolutionFusion)
    (hout : ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers.OuterFixedSubgroupRows) :
    ¬ Nonempty (ChapterH.Section10To12.M12ModuleInput (automizerRepresentation V)) := by
  rintro ⟨hmodel⟩
  apply m12_exclusion_of_fixedSpace_bounds hT hFF hq hw hr hm
    (hmodel.finrank_eq_ten (automizerRepresentation V))
  intro I hI hrank
  exact ChapterH.Section10To12.M12Calculations.LocalActors.dimensions_of_elementary_sixteen
    (automizerRepresentation V) hmodel
    (ChapterH.Section10To12.M12Calculations.ambientExtension _ hmodel)
    hinner hfusion hout I hI (card_sixteen_of_rank_four I hI hrank)

/-- The M₂₃-code exclusion with the H.16.8 premise fully discharged. Only
actual global bounds from 7.2–7.4 remain for the source assembly. -/
theorem not_m23Code_of_parameter_bounds
    {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hq : primeRank 2 (Automizer V) ≤ 4) (hw : globalW V T ≤ 2)
    (hr : 6 ≤ globalR V) (hm : 2 < localM V) :
    ¬ MathieuCode.IsM23Code (automizerRepresentation V) :=
  not_m23Code_of_native_bound hT hFF hq hw hr hm m23Code_fixedSpan_bound

end CFSG.Quasithin.Chapter7
