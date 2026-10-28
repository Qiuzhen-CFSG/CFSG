module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.CentralFusion
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# Prime-field source centralizer and congruence in E.2.2

The original unique maximal overgroup centralizes a marked involution of
K ∩ Z(T). Burnside fusion in the intrinsic Sylow normalizer makes this the
unique central Sylow involution. Dihedral coordinates identify the whole
Sylow center and exclude a four-group Sylow intersection. Thus eight divides
|K|, giving p ≡ ±1 mod 8, and the original intersection is exactly
C_K(Z(T ∩ K)). The prime seven and the automizer bound remain separate.

Source: Aschbacher–Smith E.2.2(2c), printed pp.215–216.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure

/-- The original intersection has its actual order-two Sylow center. -/
theorem prime_linear_source_sylow_center {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : 9 < p)
    (eK : K ≃* PSL2MatrixGroup F) :
    ∃ S : Sylow 2 K, (S : Subgroup K) = (T : Subgroup H).subgroupOf K ∧
      ∃ t : K, orderOf t = 2 ∧
        (center S).map (S : Subgroup K).subtype = zpowers t ∧
        (ChapterB.minimalParabolicMax T hP).subgroupOf K = centralizer ({t} : Set K) ∧
        8 ∣ Nat.card S := by
  obtain ⟨t, ht, htT, hfix, _, hMK⟩ := prime_linear_source_centralizer T hP K hgen ho hF hp eK
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal K
  have htS : t ∈ (S : Subgroup K) := hS ▸ htT
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, ho, by decide, by simpa using hF⟩
  let S' := S.mapSurjective (f := eK.toMonoidHom) eK.surjective
  obtain ⟨m, hm, ⟨d⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd S'
  let dS : S ≃* DihedralGroup (2 ^ m) :=
    ((S : Subgroup K).equivMapOfInjective eK.toMonoidHom eK.injective).trans d
  let : IsSimpleGroup (PSL2MatrixGroup F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup K := eK.isSimpleGroup
  let : Group.IsPerfect (PSL2MatrixGroup F) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  have hSbot : (S : Subgroup K) ≠ ⊥ := by
    intro he
    exact ht.1 (mem_bot.mp (show t ∈ (⊥ : Subgroup K) from he ▸ htS))
  have hStop : (S : Subgroup K) ≠ ⊤ := by
    intro he
    have hh : IsPGroup 2 (⊤ : Subgroup K) := he ▸ S.isPGroup'
    have hK := hh.of_equiv (topEquiv : (⊤ : Subgroup K) ≃* K)
    exact Group.IsPerfect.not_isNilpotent K hK.isNilpotent
  have hfusion : ∀ y : K, orderOf y = 2 → IsConj t y := by
    intro y hy
    have ht' : GorensteinWalter.IsInvolution (eK t) :=
      (orderOf_eq_prime_iff.mp ((eK.orderOf_eq t).trans (orderOf_eq_prime ht.2 ht.1))).symm
    have hy' : GorensteinWalter.IsInvolution (eK y) :=
      (orderOf_eq_prime_iff.mp ((eK.orderOf_eq y).trans hy)).symm
    obtain ⟨g, hg⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power
      F hodd (eK t) (eK y) ht' hy'
    apply isConj_iff.mpr
    refine ⟨eK.symm g, eK.injective ?_⟩
    simpa only [map_mul, map_inv, eK.apply_symm_apply] using hg
  have hu := unique_sylow_central_involution_of_max_centralizer
    T hP K S hS hSbot hStop t hfix hMK hfusion
  have htC : t ∈ centralizer (S : Set K) := by
    intro s hs
    apply Subtype.ext
    have hsT : s ∈ (T : Subgroup H).subgroupOf K := hS ▸ hs
    exact mem_centralizer_singleton_iff.mp (hfix hsT)
  have hZ := sylow_center_eq_zpowers_of_dihedral_unique (S : Subgroup K) dS t htS htC hu
  have hZcard : Nat.card (center S) = 2 := by
    have hc := congrArg (fun U : Subgroup K => Nat.card U) hZ
    rw [card_map_of_injective (S : Subgroup K).subtype_injective,
      Nat.card_zpowers, orderOf_eq_prime ht.2 ht.1] at hc
    exact hc
  have hm2 : 2 ≤ m := by
    by_contra! hh
    have hm1 : m = 1 := by omega
    have hcomm : IsMulCommutative S := ⟨⟨fun a b => dS.injective (by
      rw [map_mul, map_mul]
      subst m
      exact (IsKleinFour.isMulCommutative (G := DihedralGroup 2)).is_comm.comm _ _)⟩⟩
    have hz : center S = ⊤ := center_eq_top_iff.mpr hcomm
    rw [hz, card_top, Nat.card_congr dS.toEquiv, DihedralGroup.nat_card, hm1] at hZcard
    norm_num at hZcard
  refine ⟨S, hS, t, orderOf_eq_prime ht.2 ht.1, hZ, hMK, ?_⟩
  rw [Nat.card_congr dS.toEquiv, DihedralGroup.nat_card]
  exact (Nat.mul_dvd_mul_left 2 (pow_dvd_pow 2 hm2))

/-- The centralizer equality and congruence in the original prime-field
odd row, with no centralizer or Sylow-size conclusion assumed. -/
theorem prime_linear_source_geometry {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : 9 < p)
    (eK : K ≃* PSL2MatrixGroup F) :
    (p % 8 = 1 ∨ p % 8 = 7) ∧
      (ChapterB.minimalParabolicMax T hP).subgroupOf K =
        centralizer (((center ((T : Subgroup H).subgroupOf K)).map
          ((T : Subgroup H).subgroupOf K).subtype) : Set K) := by
  obtain ⟨S, hS, t, _, hZ, hM, h8⟩ := prime_linear_source_sylow_center T hP K hgen ho hF hp eK
  constructor
  · have h8K := h8.trans (S : Subgroup K).card_subgroup_dvd_card
    rw [Nat.card_congr eK.toEquiv] at h8K
    simpa only [hF] using Theory.PSL2.mod_eight_of_eight_dvd_psl_card (hF ▸ ho) h8K
  · rw [← hS, hZ, hM]
    apply Subgroup.ext
    intro x
    rw [mem_centralizer_singleton_iff, mem_centralizer_iff]
    constructor
    · intro hx y hy
      obtain ⟨n, rfl⟩ := hy
      exact (Commute.zpow_right hx n).eq.symm
    · intro hx
      exact (hx t (mem_zpowers t)).symm

end CFSG.Quasithin.ChapterE.Structure
