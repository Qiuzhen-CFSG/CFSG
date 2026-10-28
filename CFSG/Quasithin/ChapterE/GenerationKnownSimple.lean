module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.MinimalGeneration
public import CFSG.Quasithin.ChapterE.Section01.MinimalParabolicGeneration
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment

/-!
# Attained E-generation for every KnownSimple SQTK group

The original minimal-parabolic source dispatcher supplies a positive bound
for every intrinsic minimal parabolic. McBride generation and a finite
maximum give a positive bound for the whole group. In even order the
parameter is therefore positive and attained, with no existence callback.

For E.3.35 the original nontrivial elementary V lies inside the relative
Sylow image, so its order forces the subgroup H to have even order. The
proved containment theorem now applies to the actual numeric parameter
of every KnownSimple SQTK H without an attainment premise.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
E.1.11--12, printed pp.212--214; E.2.2 and E.3.35, pp.216--218,238--239.
The claim is for the full KnownSimple SQTK domain; unrestricted finite-group
E.1.11 is not used or asserted.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

theorem source_generation_exists_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (T : Sylow 2 G) :
    ∃ n : ℕ, 0 < n ∧ IsEGenerated n G :=
  exists_generation_of_minimalParabolics T
    (source_intrinsic_minimalParabolic_generation_knownSimple hG T)

theorem source_generation_spec_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (heven : ¬ Odd (Nat.card G)) :
    0 < generationParameter G ∧ IsEGenerated (generationParameter G) G :=
  generationParameter_spec heven (source_generation_exists_knownSimple hG T)

namespace SourceContainment

theorem le_of_sqtk_knownSimple {V M H : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} (hT : HypothesisE322 V T) (S : Sylow 2 H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hunique : maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) = {M})
    (hCV : H ⊓ centralizer (V : Set G) ≤ M)
    (hQS : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ (S : Subgroup H).map H.subtype)
    (hn : (generationParameter H : ℕ∞) < min (globalW V T) (globalR V)) : H ≤ M := by
  have hVH : V ≤ H := (le_inf hT.le_sylow
    (le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans
      (hQS.trans (map_subtype_le _))
  let : Nontrivial V := (nontrivial_iff_ne_bot _).mpr hT.nontrivial
  obtain ⟨n, hnpos, hc⟩ :=
    (inferInstance : IsElementaryAbelian 2 V).isPGroup.nontrivial_iff_card.mp
      (inferInstance : Nontrivial V)
  have heven : ¬ Odd (Nat.card H) := by
    apply Nat.not_odd_iff_even.mpr
    apply even_iff_two_dvd.mpr
    apply dvd_trans _ (card_dvd_of_le hVH)
    rw [hc]
    exact dvd_pow_self 2 (Nat.ne_of_gt hnpos)
  exact le_of_generationParameter_pos hT S hunique hCV hQS
    (source_generation_spec_knownSimple hH S heven).1 hn
end SourceContainment
end CFSG.Quasithin.ChapterE

