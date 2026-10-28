module
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.NineExtension
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.ProjectiveBound
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.CentralTwist
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers

/-!
# Odd core and Sylow subgroup of the marked extended centralizer

The projective order bound, faithful central-four action and nontrivial
central twist bound the centralizer and its kernel on the intrinsic nine-group.
The diagonal cubic then generates an extraspecial Sylow subgroup of order27
and exponent3. Full surjectivity onto the residual automorphism group is
unnecessary. All involutions and subgroup maps remain the original ones.

Source: Aschbacher--Smith15.3.38, printed p.1137.
-/

public section
open Subgroup
open scoped Pointwise
namespace Matrix.PSL3Four.ExtendedCentralizer.BoundedNineExtension
local notation "E₉" => Multiplicative (Fin 2 → ZMod 3)
variable {H : Type*} [Group H] [Finite H] (R : Subgroup H) [R.Normal]
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

omit [Finite H] [R.Normal] in
private theorem residual_card (e : R ≃* E₉) : Nat.card R = 9 := by
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

omit [Finite H] [R.Normal] in
private theorem residual_cube (e : R ≃* E₉) (r : R) : r ^ 3 = 1 := by
  apply e.injective
  rw [map_pow, map_one]
  change (3 : ℕ) • Multiplicative.toAdd (e r) = 0
  exact ZModModule.char_nsmul_eq_zero 3 _

omit [Finite H] in
private theorem odd_mem_residual
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker))
    (x : H) (hx : x ∈ (MulAut.conjNormal : H →* MulAut R).ker)
    (hodd : Nat.Coprime 2 (orderOf x)) : x ∈ R := by
  let K := (MulAut.conjNormal : H →* MulAut R).ker
  let q := QuotientGroup.mk' (R.subgroupOf K)
  let k : K := ⟨x, hx⟩
  have hq : q k = 1 := by
    obtain ⟨n, hn⟩ := hkernel.exists_orderOf_eq_pow (q k)
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes (hodd.pow_left n)
      (hn ▸ dvd_refl _) (by simpa [k] using orderOf_map_dvd q k)
  exact (QuotientGroup.eq_one_iff (N := R.subgroupOf K) k).mp hq

omit [Finite H] in
private theorem join_card (e : R ≃* E₉) (d : H)
    (hd : orderOf d = 3) (hdR : d ∉ R) : Nat.card (R ⊔ zpowers d : Subgroup H) = 27 := by
  rw [card_sup_eq_mul_of_normalizes_of_disjoint R (zpowers d)
    (by rw [R.normalizer_eq_top]; exact le_top)
    (R.disjoint_zpowers_of_prime_order_not_mem d hd hdR),
    residual_card R e, Nat.card_zpowers, hd]

omit [Finite H] in
private theorem join_noncomm
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker))
    (d : H) (hd : orderOf d = 3) (hdR : d ∉ R) :
    ¬ IsMulCommutative (R ⊔ zpowers d : Subgroup H) := by
  intro hc
  let P := R ⊔ zpowers d
  let : IsMulCommutative P := hc
  have hdP : d ∈ P := (le_sup_right : zpowers d ≤ R ⊔ zpowers d) (mem_zpowers d)
  have hdker : d ∈ (MulAut.conjNormal : H →* MulAut R).ker := by
    change MulAut.conjNormal d = (1 : MulAut R)
    ext r
    rw [MulAut.conjNormal_apply]
    have hrP : r.val ∈ P := (le_sup_left : R ≤ R ⊔ zpowers d) r.property
    have hcomm := congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨d, hdP⟩ : P) ⟨r.val, hrP⟩)
    change d * r.val = r.val * d at hcomm
    rw [hcomm, mul_inv_cancel_right]
    rfl
  exact hdR (odd_mem_residual R hkernel d hdker (by norm_num [hd]))

private theorem join_cube (e : R ≃* E₉)
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker))
    (d : H) (hd : orderOf d = 3) (hdR : d ∉ R)
    (x : (R ⊔ zpowers d : Subgroup H)) : x ^ 3 = 1 := by
  let P := R ⊔ zpowers d
  have hcard := join_card R e d hd hdR
  have hncomm := join_noncomm R hkernel d hd hdR
  have hx : x.val ∈ (R : Set H) * (zpowers d : Set H) := by
    rw [← coe_mul_of_right_le_normalizer_left R (zpowers d)
      (by rw [R.normalizer_eq_top]; exact le_top)]
    exact x.property
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  let aP : P := ⟨a, (le_sup_left : R ≤ R ⊔ zpowers d) ha⟩
  let bP : P := ⟨b, (le_sup_right : zpowers d ≤ R ⊔ zpowers d) hb⟩
  have heq : x = aP * bP := Subtype.ext hab.symm
  have ha3 : aP ^ 3 = 1 := by
    apply Subtype.ext
    exact congrArg (fun r : R => (r : H)) (residual_cube R e ⟨a, ha⟩)
  have hb3 : bP ^ 3 = 1 := by
    apply Subtype.ext
    exact orderOf_dvd_iff_pow_eq_one.mp (by
      simpa only [hd] using orderOf_dvd_of_mem_zpowers hb)
  rw [heq, OrderTwentySeven.cube_mul hcard hncomm, ha3, hb3, mul_one]

private theorem join_extraspecial (e : R ≃* E₉)
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker))
    (d : H) (hd : orderOf d = 3) (hdR : d ∉ R) :
    IsExtraspecial 3 (R ⊔ zpowers d : Subgroup H) := by
  let P := R ⊔ zpowers d
  have hcard := join_card R e d hd hdR
  have hncomm := join_noncomm R hkernel d hd hdR
  have hQ := OrderTwentySeven.quotient_center_card hcard hncomm
  refine ⟨OrderTwentySeven.center_card hcard hncomm, ?_, ?_⟩
  · refine { toIsMulCommutative :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by simpa using hQ)
             exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center P) q
    rw [← map_pow, join_cube R e hkernel d hd hdR x, map_one]
  · exact Finite.one_lt_card_iff_nontrivial.mp (by omega)

/-- A full residual automizer is unnecessary: the actual centralizer order
bound and a two-group residual kernel already suffice. -/
theorem exists_sylow_of_card_dvd (e : R ≃* E₉)
    (hcardH : Nat.card H ∣ 864)
    (hkernel : IsPGroup 2 ((MulAut.conjNormal : H →* MulAut R).ker ⧸
      R.subgroupOf (MulAut.conjNormal : H →* MulAut R).ker))
    (d : H) (hd : orderOf d = 3) (hdR : d ∉ R) :
    ∃ P : Sylow 3 H, (P : Subgroup H) = R ⊔ zpowers d ∧
      IsExtraspecial 3 P ∧ Nat.card P = 27 ∧ Monoid.exponent P = 3 := by
  let D := R ⊔ zpowers d
  have hcard : Nat.card D = 27 := join_card R e d hd hdR
  have hp : IsPGroup 3 D := IsPGroup.of_card (n := 3) (by simpa using hcard)
  have hindex : ¬ 3 ∣ D.index := by
    have hi : D.index ∣ 32 := by
      apply Nat.dvd_of_mul_dvd_mul_left (k := 27) (by decide)
      change 27 * D.index ∣ 864
      rw [← hcard, D.card_mul_index]
      exact hcardH
    exact fun hthree => (by decide : ¬ 3 ∣ 32) (hthree.trans hi)
  let P : Sylow 3 H := hp.toSylow hindex
  have hexp : Monoid.exponent D = 3 := by
    apply Nat.dvd_antisymm
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (join_cube R e hkernel d hd hdR)
    · let dD : D := ⟨d, (le_sup_right : zpowers d ≤ R ⊔ zpowers d) (mem_zpowers d)⟩
      have hdD : orderOf dD = 3 := by rwa [← Subgroup.orderOf_coe]
      exact hdD ▸ Monoid.order_dvd_exponent dD
  exact ⟨P, rfl, join_extraspecial R e hkernel d hd hdR, hcard, hexp⟩

end Matrix.PSL3Four.ExtendedCentralizer.BoundedNineExtension

namespace Matrix.PSL3Four.ExtendedCentralizer
variable {I : Type*} [Group I] [Finite I] {L : Subgroup I} [L.Normal]

/-- The marked center-action and central-twist calculations discharge both
extended-centralizer conclusions, retaining the original involutions and cubic. -/
theorem NormalizerGeometry.oddCore_and_sylow
    (d : Overgroup L) (n : NormalizerGeometry d)
    (e : pResidual 2 (MulAut.conjNormal n.graphFieldI : MulAut L).fixedSubgroup ≃*
      ElementaryNine) :
    Nonempty (pPrimeCore 2 (centralizerIn n.graphFieldI) ≃* ElementaryNine) ∧
      ∃ P : Sylow 3 (centralizerIn n.graphFieldI),
        IsExtraspecial 3 P ∧ Nat.card P = 27 ∧ Monoid.exponent P = 3 := by
  have hb := CoverCentralizers.marked_bounds_of_model_calculations d n
    (CoverCentralizers.graphField_projectiveCentralizer_card_dvd d n e)
    (CoverCentralizers.DiagonalCenter.centralFourAction_surjective d n)
    (CoverCentralizers.CentralTwist.marked_nontrivial_defect d n e)
  have he := oddCore_eq_residual_of_centerCentralizer_card_dvd d n.graphFieldI e hb.2
  let eR : residualIn (L := L) n.graphFieldI ≃* ElementaryNine :=
    (fixedResidualEquiv n.graphFieldI).symm.trans e
  have hk := kernel_quotient_two_of_projectedFixer_card_dvd d n.graphFieldI e
    (projectedResidualFixer_card_dvd d.cover n.graphFieldI e)
  obtain ⟨P, _, hP, hc, hex⟩ := BoundedNineExtension.exists_sylow_of_card_dvd
    (residualIn (L := L) n.graphFieldI) eR hb.1 hk n.diagonalInCentralizer
    n.diagonalInCentralizer_order n.diagonalInCentralizer_notMem_residual
  exact ⟨⟨(MulEquiv.subgroupCongr he).trans eR⟩, P, hP, hc, hex⟩

end Matrix.PSL3Four.ExtendedCentralizer
