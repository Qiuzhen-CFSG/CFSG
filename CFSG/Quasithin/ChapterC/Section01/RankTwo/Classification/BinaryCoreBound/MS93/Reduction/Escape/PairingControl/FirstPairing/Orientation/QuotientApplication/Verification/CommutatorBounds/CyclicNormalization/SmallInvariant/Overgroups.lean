module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Parabolics.Model
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# Small-index overgroups of the binary parabolic residual

The embedded two-residual has order twelve. Its normalizer is the parabolic:
maximality and simplicity exclude a larger normalizer. An overgroup of index
at most eight has order 24, 84 or 168. Simplicity excludes order 84; in order
24 the residual has index two and hence is normal, giving the desired
containment through its already identified normalizer.

This is the concrete SL₃(2) input to the lifting argument on MS93 printed
p.883, retaining the actual flag and residual conventions of p.832.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.CyclicNormalization.SmallInvariant.Overgroups
open Subgroup
open Matrix.PSL3Two hiding SL
open Matrix.PSL3Two.MarkedAutomorphisms

private theorem card_residual (g : SL) (i : Bool) :
    Nat.card (residual (modelParabolic g i)) = 12 := by
  unfold modelParabolic Matrix.PSL3Two.MarkedAutomorphisms.residual
  rw [← map_embedded_pResidual]
  rw [card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  cases i
  · exact card_point_residual
  · exact card_line_residual

private theorem normalizer_residual (g : SL) (i : Bool) :
    normalizer (residual (modelParabolic g i) : Set SL) = modelParabolic g i := by
  let P := modelParabolic g i
  let R := residual P
  have hRP : R ≤ P := map_subtype_le _
  have hPN : P ≤ normalizer (R : Set SL) :=
    (normal_subgroupOf_iff_le_normalizer hRP).mp
      (normal_embedded_pResidual_subgroupOf 2 (le_refl P) (by
        rw [subgroupOf_self]; infer_instance))
  have hmax : IsCoatom P := by
    change IsCoatom ((if i then lineParabolicSL else pointParabolicSL).map
      (MulAut.conj g).toMonoidHom)
    apply ((MulAut.conj g).mapSubgroup.isCoatom_iff _).mpr
    cases i
    · exact isCoatom_pointParabolicSL
    · exact isCoatom_lineParabolicSL
  rcases eq_or_lt_of_le hPN with he | ht
  · exact he.symm
  · have he := hmax.2 _ ht
    have hnormal : R.Normal := normalizer_eq_top_iff.mp he
    let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
    have hc : Nat.card R = 12 := card_residual g i
    rcases hnormal.eq_bot_or_eq_top with hb | hb
    · rw [hb, card_bot] at hc
      contradiction
    · rw [hb, card_top, Matrix.PSL3Two.card_SL] at hc
      contradiction

/-- An overgroup of the parabolic two-residual with index at most eight
contains the whole parabolic, in the original flag coordinates. -/
theorem small_index_overgroup (g : SL) (i : Bool) (A : Subgroup SL)
    (hRA : residual (modelParabolic g i) ≤ A) (hi : A.index ≤ 8) :
    modelParabolic g i ≤ A := by
  let R := residual (modelParabolic g i)
  have hR : Nat.card R = 12 := card_residual g i
  have hd : Nat.card A ∣ 168 := by simpa only [Matrix.PSL3Two.card_SL] using A.card_subgroup_dvd_card
  have hdR : 12 ∣ Nat.card A := by
    simpa only [card_residual] using card_dvd_of_le hRA
  have hmul : A.index * Nat.card A = 168 := by
    simpa only [Matrix.PSL3Two.card_SL] using A.index_mul_card
  have choices : Nat.card A = 12 ∨ Nat.card A = 24 ∨ Nat.card A = 84 ∨ Nat.card A = 168 := by
    have sieve : ∀ d ∈ Nat.divisors 168, 12 ∣ d →
        d = 12 ∨ d = 24 ∨ d = 84 ∨ d = 168 := by decide +kernel
    exact sieve _ (Nat.mem_divisors.mpr ⟨hd, by decide⟩) hdR
  rcases choices with hc | hc | hc | hc
  · rw [hc] at hmul
    omega
  · have hrel : (R.subgroupOf A).index = 2 := by
      have hh := (R.subgroupOf A).index_mul_card
      have hcard : Nat.card (R.subgroupOf A) = 12 :=
        (Nat.card_congr (subgroupOfEquivOfLe hRA).toEquiv).trans hR
      rw [hcard, hc] at hh
      omega
    have hn : A ≤ normalizer (R : Set SL) :=
      (normal_subgroupOf_iff_le_normalizer hRA).mp (normal_of_index_eq_two hrel)
    rw [normalizer_residual] at hn
    have he : A = modelParabolic g i := eq_of_le_of_card_ge hn (by
      rw [hc, card_modelParabolic])
    exact he.ge
  · have hindex : A.index = 2 := by rw [hc] at hmul; omega
    have hn : A.Normal := normal_of_index_eq_two hindex
    let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
    rcases hn.eq_bot_or_eq_top with hb | hb
    · rw [hb, card_bot] at hc
      contradiction
    · rw [hb, card_top, Matrix.PSL3Two.card_SL] at hc
      contradiction
  · rw [eq_top_of_card_eq A (hc.trans Matrix.PSL3Two.card_SL.symm)]
    exact le_top


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.CyclicNormalization.SmallInvariant.Overgroups
