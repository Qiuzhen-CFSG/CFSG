module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Data
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Base
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Coverage of the order-seven Hall--Janko elements

The literal nineteenth-index representative has order seven. Its cyclic subgroup
is Sylow because the certified carrier order contains exactly one factor seven.
Six checked carrier conjugators fuse its nonidentity powers. Sylow conjugacy
therefore proves coverage of every element of order seven.

Removing the factors 2, 3 and 5 from the carrier order also shows that every
remaining nonidentity element has order seven. This closes the final branch of
`Coverage`, without any exhaustive GAP conjugacy assertion.

Source: the retained ATLAS `J2G1-p100B0` normal forms and Lagrange/Sylow theorems.
Reproduce the finite witnesses with `source/generate_seven.py`.
-/

public section
namespace Sporadic.LeechRelated.J2.PowerFusionCertificate
open GeneratorPair.SecondOrbitCertificate

private instance seven_prime : Fact (Nat.Prime 7) := ⟨by decide⟩

private def sevenConjugatorIndex (k : Fin 6) : Index :=
  match k.val with
  | 0 => (0, 0, 0, 0)
  | 1 => (36, 3, 18, 0)
  | 2 => (4, 36, 12, 3)
  | 3 => (39, 49, 18, 3)
  | 4 => (64, 28, 23, 1)
  | _ => (79, 35, 21, 3)

private theorem representative_nineteen_pow : representative 19 ^ 7 = 1 := by
  apply carrier_ext_base
  decide +kernel

private theorem representative_nineteen_ne : representative 19 ≠ 1 := by
  intro h
  have he := congrArg (fun g : Carrier => inclusion g 0) h
  exact (by decide +kernel : inclusion (representative 19) 0 ≠ 0) he

theorem representative_nineteen_order : orderOf (representative 19) = 7 :=
  orderOf_eq_prime representative_nineteen_pow representative_nineteen_ne

private theorem seven_power_check : ∀ k : Fin 6, ∀ j : Fin 4,
    normalForm (sevenConjugatorIndex k)
        (normalForm (representativeIndex 19) (j.castLE (by decide))) =
      (normalForm (representativeIndex 19) ^ (k.val + 1))
        (normalForm (sevenConjugatorIndex k) (j.castLE (by decide))) := by
  apply allFin
  decide +kernel

theorem representative_nineteen_power_fusion (k : Fin 6) :
    IsConj (representative 19) (representative 19 ^ (k.val + 1)) := by
  apply isConj_of_base _ _ (element (sevenConjugatorIndex k))
  intro j
  simpa only [map_pow, representative, inclusion_element] using seven_power_check k j

private def sevenSylow : Sylow 7 Carrier :=
  (IsPGroup.of_card (n := 1) (G := Subgroup.zpowers (representative 19)) (by
    rw [Nat.card_zpowers, representative_nineteen_order]
    rfl)).toSylow (by
      have hc := (Subgroup.zpowers (representative 19)).card_mul_index
      rw [Nat.card_zpowers, representative_nineteen_order,
        ExceptionalParabolics.FirstParabolic.card_carrier] at hc
      intro hd
      obtain ⟨k, hk⟩ := hd
      omega)

theorem covered_of_order_seven (g : Carrier) (hg : orderOf g = 7) :
    ∃ i : Fin 21, IsConj (representative i) g := by
  obtain ⟨y, hy⟩ := sevenSylow.exists_isConj_of_orderOf_eq_prime_pow
    (hg.trans (pow_one 7).symm)
  have hm : (y : Carrier) ∈ Subgroup.zpowers (representative 19) := y.property
  have hm' := mem_zpowers_iff_mem_range_orderOf.mp hm
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm'
  have hn7 : n < 7 := by simpa only [Finset.mem_range, representative_nineteen_order] using hn
  by_cases hn0 : n = 0
  · have he1 : (y : Carrier) = 1 := by simpa only [hn0, pow_zero] using he.symm
    obtain ⟨c, hc⟩ := isConj_iff.mp hy
    have hg1 : g = 1 := (MulAut.conj c).injective (show MulAut.conj c g = MulAut.conj c 1 from
      hc.trans (he1.trans (map_one _).symm))
    simp [hg1] at hg
  · have hc := representative_nineteen_power_fusion ⟨n - 1, by omega⟩
    have hn1 : n - 1 + 1 = n := by omega
    rw [show (⟨n - 1, by omega⟩ : Fin 6).val + 1 = n from hn1, he] at hc
    exact ⟨19, hc.trans hy.symm⟩

/-- The carrier order has only one factor seven, after removing 2, 3 and 5. -/
theorem order_seven_of_no_small_prime (g : Carrier) (hg : g ≠ 1)
    (h2 : ¬2 ∣ orderOf g) (h3 : ¬3 ∣ orderOf g) (h5 : ¬5 ∣ orderOf g) :
    orderOf g = 7 := by
  have c2 : (orderOf g).Coprime (2 ^ 7) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm).pow_right _
  have c3 : (orderOf g).Coprime (3 ^ 3) :=
    (((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3).symm).pow_right _
  have c5 : (orderOf g).Coprime (5 ^ 2) :=
    (((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5).symm).pow_right _
  have hd : orderOf g ∣ 2 ^ 7 * (3 ^ 3 * (5 ^ 2 * 7)) := by
    change orderOf g ∣ 604800
    rw [← ExceptionalParabolics.FirstParabolic.card_carrier]
    exact orderOf_dvd_natCard g
  have h7 : orderOf g ∣ 7 := c5.dvd_of_dvd_mul_left
    (c3.dvd_of_dvd_mul_left (c2.dvd_of_dvd_mul_left hd))
  exact ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp h7).resolve_left
    (fun h => hg (orderOf_eq_one_iff.mp h))

end Sporadic.LeechRelated.J2.PowerFusionCertificate
