module
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.Basic

/-!
# Identifying the Held word core from the native-kernel upper bound

If the native six-point kernel is contained in the word core joined with the
distinguished cube-one element, then O₂(M) maps into a cyclic three-group in
M/wordCore. Its image is also a two-group, hence trivial. The reverse core
inclusion follows from the existing intrinsic normal two-group proof.
The concrete kernel upper bound remains explicit here.

Source: elementary coprime group theory applied to the unchanged ATLAS locals
of GLS3 Table 5.3p; no group identification is inferred from an order.
-/

public section
open Subgroup
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel

theorem wordCore_eq_pCore_of_kernel (i : Bool)
    (hk : (SixPoint.action i).ker ≤ kernelEnvelope i) :
    wordCore i = pCore 2 (localOvergroup i) := by
  let _ := wordCore_normal i
  have hc : wordCore i ≤ pCore 2 (localOvergroup i) :=
    le_sSup ⟨wordCore_normal i, wordCore_isPGroup i⟩
  apply le_antisymm hc
  let q := QuotientGroup.mk' (wordCore i)
  have hqC : (wordCore i).map q = ⊥ := QuotientGroup.map_mk'_self _
  have hle : (pCore 2 (localOvergroup i)).map q ≤ zpowers (q (kernelThird i)) := by
    calc
      _ ≤ (kernelEnvelope i).map q := map_mono ((SixPoint.twoCore_le_ker_action i).trans hk)
      _ = _ := by simp only [kernelEnvelope, Subgroup.map_sup, hqC, bot_sup_eq, MonoidHom.map_zpowers]
  have hthree : IsPGroup 3 (zpowers (q (kernelThird i))) := by
    apply isPGroup_iff_card_dvd_pow.mpr
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, pow_one]
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, kernelThird_cube, map_one]
  have hbot : (pCore 2 (localOvergroup i)).map q = ⊥ :=
    (IsPGroup.disjoint_of_coprime (pCore_isPGroup.map q) hthree (by decide)).eq_bot_of_le hle
  have hker : pCore 2 (localOvergroup i) ≤ q.ker :=
    map_le_iff_le_comap.mp hbot.le
  simpa only [q, QuotientGroup.ker_mk'] using hker

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
