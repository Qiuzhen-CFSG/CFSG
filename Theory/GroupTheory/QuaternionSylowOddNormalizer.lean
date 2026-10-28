module
public import Theory.GroupTheory.QuaternionSylowOddDecomposition
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# Normalizers of groups with quaternion Sylow two-subgroups

Brauer–Suzuki makes an involution central modulo the odd core. Since all
involutions in a group with quaternion-eight Sylow subgroups are conjugate,
the odd core together with any involution is characteristic. Coprime
normalizer lifting (Frattini's argument) then decomposes the ambient
normalizer into the embedded odd core and the involution centralizer.

Source: Fong–Wong, Nagoya Math. J.36 (1969), §3B(ii), printed p.156.
`G2Recognition.CubicNormalizer` applies the result to the literal cubic
centralizer in the I.4.5 configuration.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
private theorem quaternion_involutions_conjugate (P : Sylow 2 G)
    (e : P ≃* QuaternionGroup 2) (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    IsConj a b := by
  obtain ⟨u,hu⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) ha
  obtain ⟨v,hv⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) hb
  have hu2 : orderOf (e u) = 2 := (e.orderOf_eq u).trans ((orderOf_coe u).symm.trans ((SemiconjBy.orderOf_eq _ hu.choose_spec).symm.trans ha))
  have hv2 : orderOf (e v) = 2 := (e.orderOf_eq v).trans ((orderOf_coe v).symm.trans ((SemiconjBy.orderOf_eq _ hv.choose_spec).symm.trans hb))
  have he : e u = e v := (by decide : ∀ u v : QuaternionGroup 2,
    u≠1 → u^2=1 → v≠1 → v^2=1 → u=v) _ _
      (by intro hh; simp [hh] at hu2) (by simpa only [hu2] using pow_orderOf_eq_one (e u))
      (by intro hh; simp [hh] at hv2) (by simpa only [hv2] using pow_orderOf_eq_one (e v))
  exact hu.trans ((e.injective he) ▸ hv.symm)

theorem oddCore_sup_involution_characteristic_of_quaternion_sylow
    (P : Sylow 2 G) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (z : G) (hz : orderOf z = 2) :
    (pPrimeCore 2 G ⊔ zpowers z).Characteristic := by
  let D := pPrimeCore 2 G
  let q := QuotientGroup.mk' D
  have hzI : BenderSuzuki.PFAppendixIII.IsInvolution z :=
    ⟨by intro he; simp [he] at hz,by simpa only [hz] using pow_orderOf_eq_one z⟩
  have hzC := BenderSuzuki.PFAppendixII.appendixII_quotient_involution_central_public
    P (n := 3) (by decide) hP z hzI
  have hzc : zpowers (q z) ≤ center (G ⧸ D) := zpowers_le.mpr hzC
  let : (zpowers (q z)).Normal := ⟨fun a ha b => by
    rw [mem_center_iff.mp (hzc ha) b,mul_inv_cancel_right]
    exact ha⟩
  have he : (zpowers (q z)).comap q = D ⊔ zpowers z := by
    rw [← MonoidHom.map_zpowers,comap_map_eq,QuotientGroup.ker_mk',sup_comm]
  let : (D ⊔ zpowers z).Normal := he ▸ inferInstance
  apply characteristic_iff_map_le.mpr
  intro a
  rw [Subgroup.map_sup,characteristic_iff_map_eq.mp (inferInstance : D.Characteristic) a,
    MonoidHom.map_zpowers]
  refine sup_le le_sup_left (zpowers_le.mpr ?_)
  obtain ⟨g,hg⟩ := isConj_iff.mp (quaternion_involutions_conjugate P hP.some z (a z)
    hz ((a.orderOf_eq z).trans hz))
  change a z ∈ D ⊔ zpowers z
  rw [←hg]
  exact (inferInstance : (D ⊔ zpowers z).Normal).conj_mem z (mem_sup_right (mem_zpowers z)) g

private theorem coprime_normal_sup_supplement (D T : Subgroup G) [D.Normal]
    (hD : Nat.Coprime 2 (Nat.card D)) (hT : IsPGroup 2 T)
    (hJ : (D ⊔ T).Normal) : D ⊔ normalizer (T : Set G) = ⊤ := by
  let q := QuotientGroup.mk' D
  let : Fact (IsPGroup 2 T) := ⟨hT⟩
  let : (D ⊔ T).Normal := hJ
  have he : (D ⊔ T).map q = T.map q := by
    rw [Subgroup.map_sup,show D.map q=⊥ from (map_eq_bot_iff _).mpr (by change D ≤ (QuotientGroup.mk' D).ker; rw [QuotientGroup.ker_mk'])]
    exact bot_sup_eq _
  let : (T.map q).Normal := he ▸ (inferInstance : ((D ⊔ T).map q).Normal)
  have hn := normalizer_map_quotient_eq_map_normalizer 2 T D inferInstance hD
  change normalizer (T.map q : Set (G ⧸ D)) = (normalizer (T : Set G)).map q at hn
  rw [normalizer_eq_top] at hn
  have hh := congrArg (Subgroup.comap q) hn
  rw [comap_top,comap_map_eq,QuotientGroup.ker_mk'] at hh
  exact (sup_comm _ _).trans hh.symm

theorem normalizer_eq_oddCore_sup_inf_centralizer_of_quaternion_sylow
    (C : Subgroup G) (P : Sylow 2 C) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (z : C) (hz : orderOf z = 2) :
    normalizer (C : Set G) = (pPrimeCore 2 C).map C.subtype ⊔
      (normalizer (C : Set G) ⊓ centralizer ({(z:G)} : Set G)) := by
  let N := normalizer (C : Set G)
  let f : C →* N := inclusion C.le_normalizer
  let D := (pPrimeCore 2 C).map f
  let zz : N := f z
  let J := D ⊔ zpowers zz
  have hchar := oddCore_sup_involution_characteristic_of_quaternion_sylow P hP z hz
  have hDN : N ≤ normalizer (((pPrimeCore 2 C).map C.subtype) : Set G) :=
    normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C)
  have hJN : N ≤ normalizer ((((pPrimeCore 2 C ⊔ zpowers z).map C.subtype)) : Set G) := by
    let : (pPrimeCore 2 C ⊔ zpowers z).Characteristic := hchar
    exact normalizer_le_normalizer_characteristic_image C _
  have hDmap : D.map N.subtype = (pPrimeCore 2 C).map C.subtype := by
    rw [Subgroup.map_map]; rfl
  have hJmap : J.map N.subtype = (pPrimeCore 2 C ⊔ zpowers z).map C.subtype := by
    rw [Subgroup.map_sup,hDmap,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]; rfl
  have normal_of_image (K : Subgroup N) (hn : N ≤ normalizer (K.map N.subtype : Set G)) : K.Normal := by
    refine ⟨fun k hk n => ?_⟩
    have hh := (hn n.property (k:G)).mp (mem_map_of_mem N.subtype hk)
    exact (mem_map_iff_mem N.subtype_injective).mp hh
  let : D.Normal := normal_of_image D (by rwa [hDmap])
  have hJ : J.Normal := normal_of_image J (by rwa [hJmap])
  have hDodd : Nat.Coprime 2 (Nat.card D) := by
    rw [card_map_of_injective (inclusion_injective C.le_normalizer)]
    exact pPrimeCore_coprime_card
  have hzz : orderOf zz = 2 := ((orderOf_injective f (inclusion_injective C.le_normalizer) z)).trans hz
  have hh := coprime_normal_sup_supplement D (zpowers zz) hDodd
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hzz]; rfl)) hJ
  rw [normalizer_zpowers_eq_centralizer_of_order_two zz hzz] at hh
  have hm := congrArg (fun K : Subgroup N => K.map N.subtype) hh
  rw [Subgroup.map_sup,hDmap,map_subtype_centralizer_singleton,←MonoidHom.range_eq_map,N.range_subtype] at hm
  exact hm.symm
end Subgroup
