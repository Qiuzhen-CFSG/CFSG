module

public import CFSG.Quasithin.ChapterE.Section02.Structure.OddLinearTwo.PrimeAutomizer
public import Theory.SpecificGroups.PSL2.QuadraticInvolutionCentralizerMaximal
/-!
# Actual quadratic odd-PSL₂ source geometry

The original Sylow supplies a central involution in the normal component.
The proved quadratic Dickson calculation makes its centralizer maximal.
Unique maximality and involution fusion identify the literal intersection
M∩K with C_K(Z(T∩K)); the small-Sylow fusion obstruction gives the actual
automizer order greater than eight when O₂(H)=1.

Source: Aschbacher–Smith E.2.2(2c), printed pp.215–216. The separate
exclusion of inner-field automorphisms is not claimed in this file.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure
/-- The original normal quadratic-field branch supplies its actual centralizer
and a marked involution of the original Sylow subgroup. -/
theorem quadratic_linear_source_centralizer {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (eK : K ≃* PSL2MatrixGroup F) :
    ∃ t : K, GorensteinWalter.IsInvolution t ∧ (t : H) ∈ (T : Subgroup H) ∧
      (T : Subgroup H) ≤ centralizer ({(t : H)} : Set H) ∧
      ChapterB.minimalParabolicMax T hP = centralizer ({(t : H)} : Set H) ∧
      (ChapterB.minimalParabolicMax T hP).subgroupOf K = centralizer ({t} : Set K) := by
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 2, Fact.out, ho, by decide, hF⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := PSL2MatrixGroup F)
  obtain ⟨m, _, ⟨d⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd S
  have heven : 2 ∣ Nat.card K := by
    rw [Nat.card_congr eK.toEquiv]
    have hS : 2 ∣ Nat.card S := by
      rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
      exact dvd_mul_right 2 _
    exact hS.trans (S : Subgroup (PSL2MatrixGroup F)).card_subgroup_dvd_card
  obtain ⟨t, ht, htT, hfix⟩ := normal_even_subgroup_central_sylow_involution T K heven
  have hmap : (centralizer ({t} : Set K)).map eK.toMonoidHom =
      centralizer ({eK t} : Set (PSL2MatrixGroup F)) := by
    ext y
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    rw [← eK.injective.eq_iff]
    simp only [map_mul, eK.apply_symm_apply]
  have hti : GorensteinWalter.IsInvolution (eK t) :=
    ⟨fun he => ht.1 (eK.injective (by simpa using he)), by rw [← map_pow, ht.2, map_one]⟩
  have hmax : IsCoatom (centralizer ({t} : Set K)) := by
    apply (OrderIso.isCoatom_iff eK.mapSubgroup _).mp
    change IsCoatom ((centralizer ({t} : Set K)).map eK.toMonoidHom)
    rw [hmap]
    exact Theory.PSL2.quadratic_involution_centralizer_isCoatom ho hF hp (eK t) hti
  exact ⟨t, ht, htT, hfix, minimalParabolic_max_eq_involution_centralizer T hP K hgen t hmax hfix⟩


/-- The original intersection has its actual order-two Sylow center. -/
theorem quadratic_linear_source_sylow_center {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (eK : K ≃* PSL2MatrixGroup F) :
    ∃ S : Sylow 2 K, (S : Subgroup K) = (T : Subgroup H).subgroupOf K ∧
      ∃ t : K, orderOf t = 2 ∧
        (center S).map (S : Subgroup K).subtype = zpowers t ∧
        (ChapterB.minimalParabolicMax T hP).subgroupOf K = centralizer ({t} : Set K) ∧
        8 ∣ Nat.card S := by
  have hfieldlarge : 3 < Nat.card F := by rw [hF]; nlinarith
  obtain ⟨t, ht, htT, hfix, _, hMK⟩ := quadratic_linear_source_centralizer T hP K hgen ho hF hp eK
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal K
  have htS : t ∈ (S : Subgroup K) := hS ▸ htT
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 2, Fact.out, ho, by decide, hF⟩
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

/-- The centralizer equality and congruence in the original quadratic-field
odd row, with no centralizer or Sylow-size conclusion assumed. -/
theorem quadratic_linear_source_geometry {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (eK : K ≃* PSL2MatrixGroup F) :
    (p ^ 2 % 8 = 1 ∨ p ^ 2 % 8 = 7) ∧
      (ChapterB.minimalParabolicMax T hP).subgroupOf K =
        centralizer (((center ((T : Subgroup H).subgroupOf K)).map
          ((T : Subgroup H).subgroupOf K).subtype) : Set K) := by
  have hfieldlarge : 3 < Nat.card F := by rw [hF]; nlinarith
  obtain ⟨S, hS, t, _, hZ, hM, h8⟩ := quadratic_linear_source_sylow_center T hP K hgen ho hF hp eK
  constructor
  · have h8K := h8.trans (S : Subgroup K).card_subgroup_dvd_card
    rw [Nat.card_congr eK.toEquiv] at h8K
    simpa only [hF] using Theory.PSL2.mod_eight_of_eight_dvd_psl_card (hF ▸ ho.pow) h8K
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


/-- The source Sylow and its literal conjugation image both have order greater than eight. -/
theorem quadratic_linear_source_automizer_bound {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (eK : K ≃* PSL2MatrixGroup F) :
    8 < Nat.card T ∧
      8 < Nat.card ((T : Subgroup H).map (MulAut.conjNormal : H →* MulAut K)) := by
  have hfieldlarge : 3 < Nat.card F := by rw [hF]; nlinarith
  obtain ⟨t, ht, htT, hfix, hM, _⟩ := quadratic_linear_source_centralizer T hP K hgen ho hF hp eK
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal K
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 2, Fact.out, ho, by decide, hF⟩
  let S' := S.mapSurjective (f := eK.toMonoidHom) eK.surjective
  obtain ⟨m, hm, ⟨d⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hodd S'
  let dS : S ≃* DihedralGroup (2 ^ m) :=
    ((S : Subgroup K).equivMapOfInjective eK.toMonoidHom eK.injective).trans d
  obtain ⟨V, hVS, hV⟩ := GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (S : Subgroup K) hm dS
  let := hV
  have hex : ∃ y : K, y ∈ V ∧ orderOf y = 2 ∧ y ≠ t := by
    by_contra! hno
    have hVt : V ≤ zpowers t := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]; exact one_mem _
      have hy2 : y ^ 2 = 1 := by
        rw [pow_two]
        exact congrArg (fun v : V => (v : K)) (IsKleinFour.mul_self (⟨y, hy⟩ : V))
      rw [hno y hy (orderOf_eq_prime hy2 hy1)]
      exact mem_zpowers t
    have hc := card_le_of_le hVt
    rw [hV.card_four, Nat.card_zpowers, orderOf_eq_prime ht.2 ht.1] at hc
    omega
  obtain ⟨y, hy, hyo, hyt⟩ := hex
  have ht' : GorensteinWalter.IsInvolution (eK t) :=
    (orderOf_eq_prime_iff.mp ((eK.orderOf_eq t).trans (orderOf_eq_prime ht.2 ht.1))).symm
  have hy' : GorensteinWalter.IsInvolution (eK y) :=
    (orderOf_eq_prime_iff.mp ((eK.orderOf_eq y).trans hyo)).symm
  obtain ⟨g, hg⟩ := GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power
    F hodd (eK t) (eK y) ht' hy'
  have hconj : eK.symm g * t * (eK.symm g)⁻¹ = y := by
    apply eK.injective
    simpa only [map_mul, map_inv, eK.apply_symm_apply] using hg
  have hlarge : 8 < Nat.card T := by
    apply eight_lt_sylow_card_of_max_centralizer T hP hO (t : H)
      ((orderOf_injective K.subtype K.subtype_injective t).trans (orderOf_eq_prime ht.2 ht.1)) htT
    · intro a ha
      exact mem_centralizer_singleton_iff.mp (hfix ha)
    · exact hM
    · refine ⟨(eK.symm g : H), ?_, ?_⟩
      all_goals
        have hc : (eK.symm g : H) * (t : H) * (eK.symm g : H)⁻¹ = (y : H) :=
          congrArg (fun x : K => (x : H)) hconj
        rw [hc]
      · exact show y ∈ (T : Subgroup H).subgroupOf K from hS ▸ hVS hy
      · exact fun he => hyt (Subtype.ext he)
  have hZ : center K = ⊥ := by
    apply le_bot_iff.mp
    intro k hk
    have hcent : eK k ∈ center (PSL2MatrixGroup F) := (centerCongr eK ⟨k, hk⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F, mem_bot] at hcent
    exact mem_bot.mpr (eK.injective (by simpa only [map_one] using hcent))
  have hC := centralizer_eq_bot_of_centerless_sylow_supplement T K hgen hZ hO
  have hfaith := MulAut.conjNormal_injective_of_centralizer_eq_bot K hC
  refine ⟨hlarge, ?_⟩
  rw [card_map_of_injective hfaith]
  exact hlarge


/-- The centralizer, congruence and automizer conclusions of the quadratic row. -/
theorem quadratic_linear_source_row {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (K : Subgroup H) [K.Normal] (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hO : pCore 2 H = ⊥)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (eK : K ≃* PSL2MatrixGroup F) :
    (p ^ 2 % 8 = 1 ∨ p ^ 2 % 8 = 7) ∧
      (ChapterB.minimalParabolicMax T hP).subgroupOf K =
        centralizer (((center ((T : Subgroup H).subgroupOf K)).map
          ((T : Subgroup H).subgroupOf K).subtype) : Set K) ∧
      8 < Nat.card ((T : Subgroup H).map (MulAut.conjNormal : H →* MulAut K)) := by
  have hfieldlarge : 3 < Nat.card F := by rw [hF]; nlinarith
  obtain ⟨hc, hM⟩ := quadratic_linear_source_geometry T hP K hgen ho hF hp eK
  exact ⟨hc, hM, (quadratic_linear_source_automizer_bound T hP K hgen hO ho hF hp eK).2⟩


end CFSG.Quasithin.ChapterE.Structure
