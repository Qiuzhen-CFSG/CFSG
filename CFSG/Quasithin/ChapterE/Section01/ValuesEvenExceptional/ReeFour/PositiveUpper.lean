module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.Ambient
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.PositiveUpper.Quotients
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.ReeFour

/-!
# Positive-parameter Ree upper E-generation

The two actual O^{2′} factors of the marked Ree parabolics contain the same
Sylow two-subgroup and generate the fixed-point carrier. Their intrinsic
two-core quotients are Sz(q) and PSL₂(q), for q = 2^(2*m+1). The quotient
calculations give E-generation at rank 2*m+1. E.1.10(7) lifts this across
the normal two-cores, and restriction and E.1.8(2) place both factors in
the ambient generation target. Their join then proves the upper bound.

The final theorem uses the established positive-parameter ambient equivalence
to cover the source group G = F*(G)T. No additional SQTK or simplicity premise
is needed for this upper bound. The binary endpoint and the lower bound are
separate calculations.

Source: Aschbacher–Smith E.1.14(1), printed p.214/PDF p.225 of
`refs/quasithin.pdf`, citing Aschbacher, *GF(2)-representations of finite
groups* (1982), Lemma 4.7, DOI 10.2307/2374202. The lifting and inheritance
use E.1.2's corrected local tau convention and E.1.5's quotient-image rank.
-/

public section

namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour

open Subgroup Theory.GroupTheory ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds

private noncomputable abbrev markedSylow (m : ℕ) :=
  CFSG.Quasithin.ChapterF.GreenBook.LieModels.ReeFour.sylow m

/-- Each actual marked factor has the required local E-generation bound,
after lifting through its intrinsic normal two-core. -/
theorem positive_localFactor_isEGenerated {m : ℕ} (hm : 0 < m) (s : Side) :
    IsEGenerated (2 * m + 1) (localFactor m s) := by
  apply IsEGenerated.of_normal_two_subgroup (pCore 2 (localFactor m s)) pCore_isPGroup
  cases s with
  | suzuki =>
    exact (PositiveUpper.suzuki_quotient_isEGenerated hm).map_equiv
      (suzukiLocalQuotientEquiv m).symm
  | linear =>
    exact (PositiveUpper.linear_quotient_isEGenerated hm).map_equiv
      (linearLocalQuotientEquiv m).symm

/-- The positive-parameter Ree carrier is E-generated at the field exponent.
Both factors use the same concrete fixed-positive Sylow subgroup. -/
theorem positive_model_isEGenerated {m : ℕ} (hm : 0 < m) :
    IsEGenerated (2 * m + 1) (Model m) := by
  apply IsEGeneratedAt.isEGenerated (T := markedSylow m)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget (2 * m + 1) (markedSylow m) Ω
  rw [← CFSG.Quasithin.ChapterF.GreenBook.LieModels.ReeFour.localFactors_generate m]
  apply sup_le
  · exact ChiefOrbit.overgroup_le_generationTarget (markedSylow m) _
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.ReeFour.sylow_le_localFactor m .suzuki)
      hΩ (positive_localFactor_isEGenerated hm .suzuki)
  · exact ChiefOrbit.overgroup_le_generationTarget (markedSylow m) _
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.ReeFour.sylow_le_localFactor m .linear)
      hΩ (positive_localFactor_isEGenerated hm .linear)

/-- The upper-bound half of E.1.14(1) for a positive-parameter derived Ree
socle, including the source ambient group G = F*(G)T. -/
theorem positive_isEGenerated {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L : Subgroup G) (hL : L = generalizedFitting G)
    (hgen : L ⊔ (T : Subgroup G) = ⊤) {m : ℕ} (hm : 0 < m)
    (e : L ≃* commutator (Model m)) : IsEGenerated (2 * m + 1) G :=
  (positive_model_isEGenerated hm).map_equiv (positiveAmbientEquiv T L hL hgen hm e).symm

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour
