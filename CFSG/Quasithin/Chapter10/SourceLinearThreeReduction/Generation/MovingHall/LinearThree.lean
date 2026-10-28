module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.LinearThree.Placement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.LinearThree.Overgroups

/-!
# The original linear-three Hall subgroup without a center assumption

The two-component quotient and residual calculations put the faithful odd
Hall actor in L₀. The proper Sylow overgroup H∩L₀T has only primes two and
three, so the original odd subgroup B is a three-group. This reuses the
completed central-branch calculations under their actual hypotheses; the
center of T need not be centralized by H.

Source: Aschbacher--Smith 10.1.3 and 10.2.3(ii), printed pp.742 and 745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 CentralHall CentralHall.LinearThree
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem pair_automorphism_isPGroup [IsQuasisimple Matrix.PSL3Two.SL] :
    IsPGroup 42 (MulAut (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL)) := by
  let A := Matrix.PSL3Two.SL × Matrix.PSL3Two.SL
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
  have ha : IsPGroup 42 A := IsPGroup.of_card_dvd_pow (n := 6) (by
    dsimp [A]
    rw [Nat.card_prod, Matrix.PSL3Two.card_SL]
    norm_num)
  have hi : IsPGroup 42 (MulAut.innerSubgroup A) :=
    ha.of_surjective MulAut.conj.rangeRestrict MulAut.conj.rangeRestrict_surjective
  have ho : IsPGroup 42 (MulAut.Outer A) :=
    (AutomorphismSquare.outer_isPGroup_two Matrix.PSL3Two.center_eq_bot
      Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup).mono (by decide)
  have hk : IsPGroup 42 (QuotientGroup.mk' (MulAut.innerSubgroup A)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hi
  have hh := (ho.to_subgroup ⊤).comap_of_ker_isPGroup
    (QuotientGroup.mk' (MulAut.innerSubgroup A)) hk
  simpa using hh.of_equiv Subgroup.topEquiv

/-- The literal faithful odd actor lies in the original orbit. -/
theorem linear_three_hall_le_orbit
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} {B : Subgroup H}
    (hBM : B ≤ D.maximalLocal.subgroupOf H) (hodd : Odd (Nat.card B))
    (hfaith : B.map H.subtype ⊓ Chapter4.sectionCentralizer (localOrbit T L) = ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL) :
    B.map H.subtype ≤ localOrbit T L := by
  let R := localOrbit T L
  let M := D.maximalLocal
  let C := B.map H.subtype
  have hCM : C ≤ M := map_le_iff_le_comap.mpr hBM
  obtain ⟨eqR⟩ := quotient_equiv D e hn
  let := D.quasisimple
  let : IsQuasisimple Matrix.PSL3Two.SL := IsQuasisimple.of_mulEquiv e
  have hAut : IsPGroup 42 (MulAut (R ⧸ pCore 2 R)) :=
    pair_automorphism_isPGroup.of_equiv (MulAut.congr eqR).symm
  have hB42 : IsPGroup 42 B := hAut.of_injective
    (action D B hBM) (action_injective D B hBM hfaith)
  obtain ⟨n,hcard⟩ := hB42.exists_card_dvd_pow
  have hcard21 : Nat.card B ∣ 21 ^ n := by
    have hh : Nat.card B ∣ 2 ^ n * 21 ^ n := by
      simpa only [←mul_pow, show 2 * 21 = 42 by decide] using hcard
    exact (hodd.coprime_two_right.pow_right n).dvd_of_dvd_mul_left hh
  let N := R.subgroupOf M
  let CM := C.subgroupOf M
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (show M ≤ normalizer (R : Set G) from le_rfl)
  have hc3 : Nat.Coprime 3 N.index := by
    have he : N = primeToResidual 3 M := by
      apply map_injective M.subtype_injective
      rw [map_subgroupOf_eq_of_le R.le_normalizer,
        source_nonnormal_cubic_residual D hn]
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL]
      norm_num
    rw [he]
    exact primeToResidual_index_coprime 3
  have hc7 : Nat.Coprime 7 N.index :=
    source_linearThree_orbit_index_coprime_seven D e hn
  have hc21 : Nat.Coprime 21 N.index := by
    simpa only [show 3 * 7 = 21 by decide] using hc3.mul_left hc7
  have hcCM : Nat.card CM ∣ 21 ^ n := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv]
    simpa only [C,card_map_of_injective H.subtype_injective] using hcard21
  have hcop : Nat.Coprime N.index (Nat.card CM) :=
    (hc21.pow_left n).symm.coprime_dvd_right hcCM
  have hle : CM ≤ N := relIndex_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hcop (N.relIndex_dvd_index_of_normal CM)
      (N.relIndex_dvd_card CM))
  intro b hb
  exact hle (show (⟨b,hCM hb⟩ : M) ∈ CM from hb)

/-- The full Hall conclusion for the original SL₃(2) quotient. -/
theorem linear_three_hall_isThreeGroup
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    {B : Subgroup H} (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes
      (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hfaith : B.map H.subtype ⊓ Chapter4.sectionCentralizer (localOrbit T L) = ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL) : IsPGroup 3 B := by
  have hodd : Odd (Nat.card B) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    apply hHall.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ _ rfl
    rw [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
    exact even_iff_two_dvd.mp he
  have hBP : B.map H.subtype ≤ H ⊓ localJoin T L :=
    le_inf (map_subtype_le B)
      ((linear_three_hall_le_orbit D hn hBM hodd hfaith e).trans le_sup_left)
  have h6 := (source_proper_overgroup_six D e hn (H ⊓ localJoin T L)
    (le_inf hH.1.1.2 le_sup_right) (source_hstar_inf_localJoin_lt D hH)).to_le hBP
  have hB6 : IsPGroup 6 B :=
    h6.of_equiv (B.equivMapOfInjective H.subtype H.subtype_injective).symm
  obtain ⟨n,hn⟩ := hB6.exists_card_dvd_pow
  have hn' : Nat.card B ∣ 2 ^ n * 3 ^ n := by
    simpa only [←mul_pow,show 2 * 3 = 6 by decide] using hn
  exact IsPGroup.of_card_dvd_pow
    ((hodd.coprime_two_right.pow_right n).dvd_of_dvd_mul_left hn')

end CFSG.Quasithin.Chapter10.MovingHall
