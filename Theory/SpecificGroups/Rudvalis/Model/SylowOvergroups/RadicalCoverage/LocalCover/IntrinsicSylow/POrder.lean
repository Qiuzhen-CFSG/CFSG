module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.PLevel0
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.PLevel1
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.PLevel2
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.PLevel3
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.PLevel4
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.PLevel5
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.PLevel6
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.PLevel7
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.PLevel8
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.Comparison

/-!
# The fixed Rudvalis word subgroup is a two-group

The nine checked Schreier steps exhaust the word subgroup, with terminal
stabilizer trivial. Their orbit lengths multiply to 16384. The comparison
identifies this subgroup with the image of `localP` in the original faithful
permutation representation; no ambient order formula is used.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow

public theorem localP_card : Nat.card localP = 16384 := by
  have h := Nat.card_congr
    (localP.equivMapOfInjective permutation Subtype.val_injective).toEquiv
  rw [map_localP] at h
  rw [h, P.L0.card_step, P.L1.card_step, P.L2.card_step, P.L3.card_step,
    P.L4.card_step, P.L5.card_step, P.L6.card_step, P.L7.card_step,
    P.L8.card_step, P.L9.card]

public theorem localP_isPGroup : IsPGroup 2 localP :=
  IsPGroup.of_card (n := 14) localP_card

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow
