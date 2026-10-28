module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.KernelUpperBound
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB

/-!
# Three-core bounds for the literal Held two-local quotients

For max3 and max4, the certified native six-point kernel lies in the join
of the normal word two-core and a specified cube-one element. After factoring
out the intrinsic two-core, the kernel therefore has order dividing three.
The quotient three-core maps trivially to S₆: a nontrivial normal subgroup
of S₆ contains A₆, which cannot be a three-group. Consequently that three-core
also has order dividing three.

For max5, the certified order 21504 already excludes a factor of nine from
every subgroup of every quotient. All groups and maps here belong to the
fixed degree-2058 Held carrier; no abstract extension-shape premise, ambient
order or simplicity hypothesis is used.

Source: GLS3 Table 5.3p, the two `E64.(3.S6)` classes and the
`2^(1+6).L3(2)` involution centralizer. These are the numerical obstructions
used in the Held branch of Aschbacher--Smith 15.3.41--42, printed p.1138.
Exhaustive coverage of the eligible local subgroups is a separate obligation.
-/

public section

open Subgroup
open Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel

namespace Held.TwoLocalCandidates.ThreeCoreBounds

private theorem symmetricSix_threeCore : pCore 3 (Equiv.Perm (Fin 6)) = ⊥ := by
  by_contra hn
  have hnt : Nontrivial (pCore 3 (Equiv.Perm (Fin 6))) := (nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 6)) hnt
  have hdiv : 360 ∣ Nat.card (pCore 3 (Equiv.Perm (Fin 6))) := by
    have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact hc ▸ card_dvd_of_le hle
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 3) (G := Equiv.Perm (Fin 6))).exists_card_eq
  have htwo : 2 ∣ 3 ^ n := hn ▸ (dvd_trans (by decide : 2 ∣ 360) hdiv)
  exact (by decide : ¬ 2 ∣ 3) (Nat.prime_two.dvd_of_dvd_pow htwo)

/-- The actual six-point action on either max3/max4 two-core quotient has
kernel of order dividing three. -/
theorem quotientAction_kernel_card_dvd_three (i : Bool) :
    Nat.card (SixPoint.quotientAction i).ker ∣ 3 := by
  have hC : wordCore i ≤ pCore 2 (localOvergroup i) :=
    le_sSup ⟨wordCore_normal i, wordCore_isPGroup i⟩
  have hmap : (wordCore i).map (localQuotientMap i) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [localQuotientMap, QuotientGroup.ker_mk'] using hC
  have hker : (SixPoint.quotientAction i).ker ≤
      zpowers (localQuotientMap i (kernelThird i)) := by
    calc
      _ = ((SixPoint.action i).ker).map (localQuotientMap i) :=
        QuotientGroup.ker_lift _ _ _
      _ ≤ (kernelEnvelope i).map (localQuotientMap i) :=
        map_mono (nativeKernel_le_kernelEnvelope i)
      _ = _ := by
        simp only [kernelEnvelope, Subgroup.map_sup, hmap, bot_sup_eq, MonoidHom.map_zpowers]
  apply (card_dvd_of_le hker).trans
  rw [Nat.card_zpowers]
  apply orderOf_dvd_of_pow_eq_one
  rw [← map_pow, kernelThird_cube, map_one]

/-- The three-core of either literal max3/max4 two-core quotient has order
dividing three. -/
theorem max34_threeCore_card_dvd_three (i : Bool) :
    Nat.card (pCore 3 (LocalQuotient i)) ∣ 3 := by
  have hn : ((pCore 3 (LocalQuotient i)).map (SixPoint.quotientAction i)).Normal :=
    Subgroup.Normal.map inferInstance _ (SixPoint.quotientAction_surjective i)
  have hm : (pCore 3 (LocalQuotient i)).map (SixPoint.quotientAction i) ≤
      pCore 3 (Equiv.Perm (Fin 6)) :=
    le_sSup ⟨hn, pCore_isPGroup.map (SixPoint.quotientAction i)⟩
  rw [symmetricSix_threeCore] at hm
  have hker : pCore 3 (LocalQuotient i) ≤ (SixPoint.quotientAction i).ker :=
    (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hm)
  exact (card_dvd_of_le hker).trans (quotientAction_kernel_card_dvd_three i)

/-- The literal max5 quotient three-core cannot have order divisible by nine. -/
theorem max5_not_nine_dvd_threeCore_quotient :
    ¬ 9 ∣ Nat.card (pCore 3 (max5 ⧸ pCore 2 max5)) := by
  intro h
  have hd : 9 ∣ Nat.card max5 :=
    h.trans ((card_subgroup_dvd_card _).trans (card_quotient_dvd_card _))
  rw [Held.InvolutionFixedData.TwoB.max5_card] at hd
  exact (by decide : ¬ 9 ∣ 21504) hd

/-- None of the three literal Held candidate two-core quotients has a
three-core whose order is divisible by nine. -/
theorem not_nine_dvd_threeCore_quotient (i : Fin 3) :
    ¬ 9 ∣ Nat.card (pCore 3 (subgroup i ⧸ pCore 2 (subgroup i))) := by
  fin_cases i
  · exact fun h => (by decide : ¬ 9 ∣ 3) (h.trans (max34_threeCore_card_dvd_three false))
  · exact fun h => (by decide : ¬ 9 ∣ 3) (h.trans (max34_threeCore_card_dvd_three true))
  · exact max5_not_nine_dvd_threeCore_quotient

end Held.TwoLocalCandidates.ThreeCoreBounds
