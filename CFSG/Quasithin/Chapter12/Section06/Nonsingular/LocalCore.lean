module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CoreQuotient
public import Theory.GroupTheory.PCoreQuotientAction
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Computing the original local two-core before normalization

With L normalized by T, C_LT(v)/L_v is a two-group: first pass to LT/L,
then use the two-residual in C_L(v). If L_v/O₂(L_v) is centerless, the
quotient-action kernel theorem identifies O₂(C_LT(v)) with the centralizer
of L_v/O₂(L_v) inside C_LT(v). Comparison with the star quotient then gives
R ∩ T_v = R_v whenever T_v is Sylow in C_LT(v).

Only T_v is known to normalize L_v at this point. The argument does not
use the later normalization of R, and retains both original quotient maps.
This removes the intersection premise from the proof of Lemmas 12.6.4--5.
The marked A₆ quotient and the source Sylow position still need the preceding
model calculation in the assembly of Theorem 12.6.2.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Section 12.6, printed pp.823--824.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

theorem inf_coreQuotientCentralizer_eq_core (A H : Subgroup G)
    (hAH : A ≤ H) [(A.subgroupOf H).Normal]
    (hq : IsPGroup 2 (H ⧸ A.subgroupOf H))
    (hz : center (Star A) = ⊥) :
    H ⊓ coreQuotientCentralizer A = H.pCoreIn 2 := by
  let A' := A.subgroupOf H
  let e := subgroupOfEquivOfLe hAH
  let eQ : (A' ⧸ pCore 2 A') ≃* Star A :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hz' : center (A' ⧸ pCore 2 A') = ⊥ := by
    apply bot_unique
    intro x hx
    have hc : eQ x ∈ center (Star A) := by
      rw [mem_center_iff] at hx ⊢
      intro y
      obtain ⟨z, rfl⟩ := eQ.surjective y
      simpa only [map_mul] using congrArg eQ (hx z)
    rw [hz, mem_bot] at hc
    exact mem_bot.mpr (eQ.injective (hc.trans eQ.map_one.symm))
  let f := (quotientAut (pCore 2 A')).comp (MulAut.conjNormal : H →* MulAut A')
  have hf : f.ker = pCore 2 H := quotientAction_ker_eq_pCore 2 A' hq hz'
  have hker : f.ker = (coreQuotientCentralizer A).subgroupOf H := by
    ext h
    have hn : h ∈ normalizer (A' : Set H) := by rw [normalizer_eq_top]; trivial
    have he := mem_coreQuotientCentralizer_iff_map H.subtype A'
      (IsPGroup.ker_isPGroup_of_injective H.subtype_injective) hn
    rw [show A'.map H.subtype = A from map_subgroupOf_eq_of_le hAH] at he
    simp only [subtype_apply] at he
    change f h = 1 ↔ (h : G) ∈ coreQuotientCentralizer A
    rw [← he]
    constructor
    · intro hh
      exact ⟨⟨h, hn⟩, hh, rfl⟩
    · rintro ⟨n, hn', he'⟩
      have hn'' : n = ⟨h, hn⟩ := Subtype.ext he'
      subst n
      exact hn'
  have hm := congrArg (Subgroup.map H.subtype) (hker.symm.trans hf)
  simpa only [subgroupOf_map_subtype, inf_comm, pCoreIn] using hm

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

theorem localCentralizer_quotient_Lv_isPGroup (T : Sylow 2 G) (L : Subgroup G)
    (hT : (T : Subgroup G) ≤ M L) (v : G)
    [((Lv L v).subgroupOf (LT T L ⊓ Gv v)).Normal] :
    IsPGroup 2 ((LT T L ⊓ Gv v : Subgroup G) ⧸ (Lv L v).subgroupOf (LT T L ⊓ Gv v)) := by
  let J := LT T L
  let H := LT T L ⊓ Gv v
  have hLJ : L ≤ J := le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  let : (L.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLJ).mpr (sup_le L.le_normalizer hT)
  have hsup : L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    apply (map_injective J.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLJ, map_subgroupOf_eq_of_le hTJ,
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hpJ : IsPGroup 2 (J ⧸ L.subgroupOf J) :=
    isPGroup_quotient_of_sup_eq_top _ _ T.isPGroup'.comap_subtype hsup
  intro w
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective ((Lv L v).subgroupOf H) w
  obtain ⟨n, hn⟩ := hpJ (QuotientGroup.mk' (L.subgroupOf J) ⟨h, h.property.1⟩)
  have hnL : (h : G) ^ 2 ^ n ∈ L := by
    have hn' : QuotientGroup.mk' (L.subgroupOf J) ((⟨h, h.property.1⟩ : J) ^ 2 ^ n) = 1 := by
      rwa [map_pow]
    exact (QuotientGroup.eq_one_iff ((⟨h, h.property.1⟩ : J) ^ 2 ^ n)).mp hn'
  let b : CLv L v := ⟨(h : G) ^ 2 ^ n, hnL, (Gv v).pow_mem h.property.2 _⟩
  obtain ⟨m, hm⟩ := isPGroup_quotient_pResidual 2
    (QuotientGroup.mk' (pResidual 2 (CLv L v)) b)
  have hb : b ^ 2 ^ m ∈ pResidual 2 (CLv L v) := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pResidual 2 (CLv L v)) (b ^ 2 ^ m) = 1
    rwa [map_pow]
  refine ⟨n + m, ?_⟩
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  change (h : G) ^ 2 ^ (n + m) ∈ Lv L v
  rw [pow_add, pow_mul]
  exact mem_map.mpr ⟨b ^ 2 ^ m, hb, rfl⟩

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

/-- The actual core of C_LT(v) is its centralizer on L_v/O₂(L_v). -/
theorem Rv_eq_inf_coreQuotientCentralizer (T : Sylow 2 G) (L : Subgroup G)
    (hT : (T : Subgroup G) ≤ M L) (v : G)
    (hz : center (Star (Lv L v)) = ⊥) :
    Rv T L v = (LT T L ⊓ Gv v) ⊓ coreQuotientCentralizer (Lv L v) := by
  have hLH : Lv L v ≤ LT T L ⊓ Gv v :=
    le_inf ((Lv_le_L L v).trans le_sup_left) (Lv_le_Gv L v)
  let : ((Lv L v).subgroupOf (LT T L ⊓ Gv v)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLH).mpr
      ((inf_le_inf (sup_le L.le_normalizer hT) le_rfl).trans (Mv_le_normalizer_Lv L v))
  exact (inf_coreQuotientCentralizer_eq_core (Lv L v) _ hLH
    (localCentralizer_quotient_Lv_isPGroup T L hT v) hz).symm

/-- Comparison only on T_v, which already normalizes L_v; no claim that R
normalizes L_v is used at this stage. -/
theorem R_inf_Tv_eq_Tv_inf_coreQuotientCentralizer
    (T : Sylow 2 G) (L K S : Subgroup G) (v : G)
    (hT : (T : Subgroup G) ≤ M L)
    (hLK : Lv L v ≤ K) (hTvS : Tv T v ≤ S) :
    R L K S v ⊓ Tv T v = Tv T v ⊓ coreQuotientCentralizer (Lv L v) := by
  let H := K ⊔ S
  let A := (Lv L v).subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hLH : Lv L v ≤ H := hLK.trans le_sup_left
  have hTvH : Tv T v ≤ H := hTvS.trans le_sup_right
  have hnorm : Tv T v ≤ normalizer (Lv L v : Set G) :=
    (inf_le_inf hT le_rfl).trans (Mv_le_normalizer_Lv L v)
  have hqker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hcompare (r : H) (hn : (r : G) ∈ normalizer (Lv L v : Set G)) :
      q r ∈ coreQuotientCentralizer (A.map q) ↔
        (r : G) ∈ coreQuotientCentralizer (Lv L v) := by
    have hrA : r ∈ normalizer (A : Set H) := by
      dsimp only [A]
      rw [← subgroupOf_normalizer_eq hLH]
      exact hn
    have h := (mem_coreQuotientCentralizer_iff_map q A hqker hrA).symm.trans
      (mem_coreQuotientCentralizer_iff_map H.subtype A
        (IsPGroup.ker_isPGroup_of_injective H.subtype_injective) hrA)
    simpa only [A, map_subgroupOf_eq_of_le hLH, subtype_apply] using h
  ext r
  constructor
  · rintro ⟨hr, ht⟩
    refine ⟨ht, ?_⟩
    obtain ⟨y, hy, he⟩ := hr.2
    change (y : G) = r at he
    have hn : (y : G) ∈ normalizer (Lv L v : Set G) := he.symm ▸ hnorm ht
    exact he ▸ (hcompare y hn).mp hy
  · rintro ⟨ht, hc⟩
    let rH : H := ⟨r, hTvH ht⟩
    exact ⟨⟨hTvS ht, rH, (hcompare rH (hnorm ht)).mpr hc, rfl⟩, ht⟩

/-- The defining intersection R∩T_v=R_v follows from the source Sylow
alignment and the centerless A₆ quotient; it is no longer an independent input. -/
theorem R_inf_Tv_eq_Rv (T : Sylow 2 G) (L K S : Subgroup G) (v : G)
    (hT : (T : Subgroup G) ≤ M L) (hLK : Lv L v ≤ K)
    (hTvS : Tv T v ≤ S)
    (P : Sylow 2 (LT T L ⊓ Gv v : Subgroup G))
    (hP : (P : Subgroup (LT T L ⊓ Gv v : Subgroup G)).map (LT T L ⊓ Gv v).subtype = Tv T v)
    (hz : center (Star (Lv L v)) = ⊥) :
    R L K S v ⊓ Tv T v = Rv T L v := by
  rw [R_inf_Tv_eq_Tv_inf_coreQuotientCentralizer T L K S v hT hLK hTvS]
  have hcoreTv : Rv T L v ≤ Tv T v := (pCoreIn_le_sylow _ P).trans hP.le
  apply le_antisymm
  · rw [Rv_eq_inf_coreQuotientCentralizer T L hT v hz]
    exact inf_le_inf (inf_le_inf le_sup_right le_rfl) le_rfl
  · exact le_inf hcoreTv ((Rv_eq_inf_coreQuotientCentralizer T L hT v hz).le.trans inf_le_right)
end CFSG.Quasithin.Chapter12.Section06
