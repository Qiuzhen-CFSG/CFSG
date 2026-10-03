module
public import Stellmacher.Recognition.Parrott.ChosenCoreCoveringLift
public import Theory.GroupAction.BinarySixteenTwoPower
public import Theory.GroupTheory.FourthPowerCentralizerCard

/-!
# Keeping a covering actor in the supplied involution centralizer

Put S = C_G(z) ∩ C_G(a) and B = E ∩ F. The original Sylow normalizes B,
which is elementary of order sixteen. Every two-power automorphism of B
has fourth power one. An element of S also fixes a, so its fourth power
centralizes F = ⟨a⟩B. Since F is self-centralizing and elementary, that
fourth power belongs to F and its eighth power is one.

The covering quotient generator can therefore be chosen in S with eighth
power one, without changing either the supplied involution or Sylow.
Compatibility with E reduces to the remaining local obstruction: an element
of quotient order four and eighth power one has fourth power in E.
The conditional assembly below keeps this unproved input explicit.

There is also a weaker route to the required fixed-point bound. If an actor
in S has at most two fixed points on E, its fourth power is either a or az.
Indeed, that power is in F but outside E by the order-four fixed-point bound.
Writing it as ba with b in E ∩ F, both b and z are fixed by the actor, so
b is 1 or z. Excluding these two fourth-root equations would therefore
suffice. Their exclusion is not asserted here.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the covering-centralizer calculation on p.676.
-/

open Subgroup
open scoped IsMulCommutative Pointwise
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Every fourth power in the supplied involution centralizer lies in the
original elementary fixed join. -/
public theorem chosen_centralizer_fourth_power_mem_fixed_join
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    ∀ y : G, y ∈ S → y ^ 4 ∈ d.F := by
  intro S y hy
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let B := E ⊓ d.F
  let : IsElementaryAbelian 2 d.F := d.elementary
  let : IsElementaryAbelian 2 B := {
    toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
      (setLike_mul_comm (s := d.F) a.property.2 b.property.2)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun b =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := d.F) b b.property.2)) }
  have hHE : H ≤ normalizer (E : Set G) := by
    have hh := ((commutator J).map J.subtype).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype,
      map_map] using hh
  have hSN : S ≤ normalizer (B : Set G) :=
    (le_inf (inf_le_left.trans hHE)
      ((d.chosen_centralizer_le_sylow h).trans d.sylow_le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  let f : S →* MulAut B := B.normalizerMonoidHom.comp (inclusion hSN)
  let ys : S := ⟨y, hy⟩
  obtain ⟨n, hn⟩ := (d.chosen_centralizer_isPGroup h).exists_pow_pow_eq_one ys
  have hf : f ys ^ 4 = 1 :=
    MulAut.fourth_power_eq_one_of_card_sixteen_of_two_power d.inf_card (f ys) n
      (by rw [← map_pow, hn, map_one])
  have hyB : y ^ 4 ∈ centralizer (B : Set G) := by
    intro b hb
    have hh := congrArg (fun u : MulAut B => (u ⟨b, hb⟩ : G)) hf
    rw [← map_pow] at hh
    change y ^ 4 * b * (y ^ 4)⁻¹ = b at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have ha : (d.a : G) ∈ centralizer ({y ^ 4} : Set G) :=
    mem_centralizer_singleton_iff.mpr
      ((show Commute (d.a : G) y from
        (mem_centralizer_singleton_iff.mp hy.2).symm).pow_right 4)
  have hB : B ≤ centralizer ({y ^ 4} : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (hyB b hb)
  have hF : d.F ≤ centralizer ({y ^ 4} : Set G) := by
    rw [d.fixed_join, ← d.inf_eq]
    exact sup_le (zpowers_le.mpr ha) hB
  rw [← d.centralizer_eq]
  intro b hb
  exact mem_centralizer_singleton_iff.mp (hF hb)

/-- The supplied involution centralizer has exponent dividing eight. -/
public theorem chosen_centralizer_eighth_power_eq_one
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    ∀ y : G, y ∈ S → y ^ 8 = 1 := by
  intro S y hy
  let : IsElementaryAbelian 2 d.F := d.elementary
  have hh := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := d.F)
    (y ^ 4) (d.chosen_centralizer_fourth_power_mem_fixed_join h y hy)
  simpa only [← pow_mul] using hh

/-- The covering generator lies in the actual centralizer and has eighth
power one. This conclusion concerns the same witness throughout. -/
public theorem chosen_covering_exists_lift_eighth_power_eq_one
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    (J.map H.subtype).relIndex S = 4 →
      ∃ y : H, (y : G) ∈ S ∧ orderOf (QuotientGroup.mk' J y) = 4 ∧ y ^ 8 = 1 := by
  intro H J S hi
  obtain ⟨y, hyS, hyOrder⟩ := d.chosen_covering_quotient_generator h hi
  exact ⟨y, hyS, hyOrder, Subtype.ext (d.chosen_centralizer_eighth_power_eq_one h y hyS)⟩

/-- Reduction to an intrinsic obstruction in H, with no chosen involution
in the remaining premise. No order is inferred from quotient order. -/
public theorem chosen_covering_compatible_lift_of_eighth_power_obstruction
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    (∀ y : H, orderOf (QuotientGroup.mk' J y) = 4 → y ^ 8 = 1 →
      y ^ 4 ∈ (commutator J).map J.subtype) →
    (J.map H.subtype).relIndex S = 4 →
      ∃ y : H, (y : G) ∈ S ∧ orderOf (QuotientGroup.mk' J y) = 4 ∧
        (y : G) ^ 4 ∈ centralizer (E : Set G) := by
  intro H J E S hobstruction hi
  obtain ⟨y, hyS, hyOrder, hyEight⟩ := d.chosen_covering_exists_lift_eighth_power_eq_one h hi
  refine ⟨y, hyS, hyOrder, ?_⟩
  rw [parrott_derived_centralizer z h]
  have hh := mem_map_of_mem H.subtype (hobstruction y hyOrder hyEight)
  rw [map_map] at hh
  exact hh

/-- If the derived fixed subgroup has at most two elements, the fourth
power is one of two specified involutions in the original fixed join.
This reduction keeps the actual actor and the supplied involution. -/
public theorem chosen_centralizer_small_fixed_fourth_power
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    ∀ y : H, (y : G) ∈ S →
      Nat.card (E ⊓ centralizer ({(y : G)} : Set G) : Subgroup G) ≤ 2 →
      (y : G) ^ 4 = (d.a : G) ∨ (y : G) ^ 4 = (d.a : G) * z := by
  classical
  intro H J E S y hyS hc
  let B := E ⊓ centralizer ({(d.a : G)} : Set G)
  let C := E ⊓ centralizer ({(y : G)} : Set G)
  obtain ⟨_, _, _, _, _, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator J) := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := commutator J)
      (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  have hHE : H ≤ normalizer (E : Set G) := by
    have hh := ((commutator J).map J.subtype).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype,
      map_map] using hh
  have hy4E : (y : G) ^ 4 ∉ E := by
    intro hm
    have hh := two_lt_centralizer_card_of_card_thirty_two_of_fourth_power
      E hEcard (y : G) (hHE y.property) (E.le_centralizer hm)
    omega
  have hzC : zpowers z = C := by
    apply eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      exact ⟨d.z_mem_inf.1,
        mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp y.property).symm⟩
    · rw [Nat.card_zpowers, h.involution]
      exact hc
  have hyF := d.chosen_centralizer_fourth_power_mem_fixed_join h y hyS
  have haCB : (d.a : G) ∈ centralizer (B : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mp hb.2
  have hprod : (y : G) ^ 4 ∈ (B : Set G) * (zpowers (d.a : G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left B (zpowers (d.a : G))
      ((zpowers_le.mpr haCB).trans (Subgroup.centralizer_le_normalizer _)), sup_comm,
      ← d.fixed_join]
    exact hyF
  obtain ⟨b, hb, a, ha, hba⟩ := hprod
  have haorder : orderOf (d.a : G) = 2 := (Subgroup.orderOf_coe d.a).trans d.a_order
  change a ∈ zpowers (d.a : G) at ha
  rw [mem_zpowers_iff_mem_range_orderOf, haorder] at ha
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
  have hnlt : n < 2 := Finset.mem_range.mp hn
  have hyba : (y : G) ^ 4 = b * (d.a : G) := by
    interval_cases n
    · have heq : (y : G) ^ 4 = b := by simpa only [pow_zero, mul_one] using hba.symm
      exact (hy4E (heq ▸ hb.1)).elim
    · simpa only [pow_one] using hba.symm
  have hbC : b ∈ C := by
    refine ⟨hb.1, ?_⟩
    have ha2 : (d.a : G) ^ 2 = 1 := haorder ▸ pow_orderOf_eq_one (d.a : G)
    have hbexpr : b = (y : G) ^ 4 * (d.a : G) := by
      rw [hyba, mul_assoc, ← pow_two, ha2, mul_one]
    rw [hbexpr]
    apply (centralizer ({(y : G)} : Set G)).mul_mem
    · exact mem_centralizer_singleton_iff.mpr ((Commute.refl (y : G)).pow_left 4)
    · exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp hyS.2).symm
  have hbz : b ∈ zpowers z := hzC.symm ▸ hbC
  rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hbz
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hbz
  have hmlt : m < 2 := Finset.mem_range.mp hm
  interval_cases m
  · exact Or.inl (by simpa only [pow_zero, one_mul] using hyba)
  · apply Or.inr
    simpa only [pow_one, (mem_centralizer_singleton_iff.mp d.a.property)] using hyba


/-- Excluding fourth roots of the two specified involutions suffices for
the weaker covering target, a derived fixed subgroup of order greater than
two. The root exclusions remain explicit hypotheses. -/
public theorem chosen_covering_large_fixed_of_no_fourth_roots
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    (∀ y : H, (y : G) ∈ S → orderOf (QuotientGroup.mk' J y) = 4 →
      (y : G) ^ 4 ≠ (d.a : G) ∧ (y : G) ^ 4 ≠ (d.a : G) * z) →
    (J.map H.subtype).relIndex S = 4 →
      ∃ y : H, (y : G) ∈ S ∧ orderOf (QuotientGroup.mk' J y) = 4 ∧
        2 < Nat.card (E ⊓ centralizer ({(y : G)} : Set G) : Subgroup G) := by
  intro H J E S hroots hi
  obtain ⟨y, hyS, hyOrder⟩ := d.chosen_covering_quotient_generator h hi
  refine ⟨y, hyS, hyOrder, ?_⟩
  by_contra hc
  rcases d.chosen_centralizer_small_fixed_fourth_power h y hyS (Nat.not_lt.mp hc)
    with ha | haz
  · exact (hroots y hyS hyOrder).1 ha
  · exact (hroots y hyS hyOrder).2 haz

end Stellmacher.Recognition.ParrottSecondElementaryData
