module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.InvolutionOrbit
public import Theory.GroupTheory.CoreInvolutionFusion
public import Theory.GroupTheory.QuaternionCentralProductInvolutionCentralizers

/-!
# Splitting the marked index-two extension

Every noncentral involution t of the quaternion core is conjugate to the
marked involution z. Its H-centralizer E has order 32, while C_G(t) has
Sylow order 64. If no conjugate of z lay outside the core in H, the
conjugates in E would generate C_Q(t). That subgroup has derived group
⟨z⟩, so every normalizer of E would fix z. The normalizer condition in a
Sylow subgroup of C_G(t) contradicts this control.

Thus there is an actual involution n outside Q, fused to z. Since
|H₁H₂:Q| = 9, n lies outside H₁H₂ and its cyclic subgroup is an actual
complement. No splitting premise is assumed. ExtensionInvolution records
the simultaneous nontrivial factor actions; Chapter14Extension applies
these results to SourceLocalData. Ambient G₂(3) recognition remains open.

Source: the normalizer and involution-generation argument of
Janko–Thompson (1970), §4, printed p.390, applied to the marked data of
Aschbacher–Smith I.4(G1)–(G2), p.417; compare Fong–Wong §2F, pp.153–154.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

/-- Fusion escapes the quaternion core inside the marked involution centralizer. -/
theorem exists_fused_involution_outside_core :
    ∃ (z : G) (n : c.H), orderOf z = 2 ∧ c.H = centralizer ({z} : Set G) ∧
      orderOf n = 2 ∧ n ∉ quaternionCore c ∧ IsConj z (n : G) := by
  classical
  obtain ⟨z,t,hz,hH,ht,htZ,hconj⟩ := exists_distinguished_fusion_in_quaternionCore c
  let Q := quaternionCore c
  let d := quaternionCoreData c
  let zH : c.H := ⟨z,hH.symm ▸ mem_centralizer_singleton_iff.mpr rfl⟩
  have hzH : orderOf zH = 2 := (orderOf_coe zH).symm.trans hz
  have hzC : zH ∈ center c.H := mem_center_iff.mpr fun h =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hH ▸ h.property))
  have hzQ : zH ∈ Q := core_self_centralizing c (fun q _ => mem_center_iff.mp hzC q)
  have hzQcent : (⟨zH,hzQ⟩ : Q) ∈ center Q :=
    mem_center_iff.mpr (fun q => Subtype.ext (mem_center_iff.mp hzC q))
  have htz : (t : c.H) ≠ zH := by
    intro he
    exact htZ ((show t = (⟨zH,hzQ⟩ : Q) from Subtype.ext he).symm ▸ hzQcent)
  obtain ⟨hgen,hline⟩ := quaternion_central_product_involution_centralizer_geometry_in_ambient
    Q d.left d.right d.left_model d.right_model d.span d.intersection_card d.commute
    zH t hzH hzC hzQ ((orderOf_coe t).trans ht) t.property htz
  let E := centralizer ({(t : c.H)} : Set c.H)
  let D := Q ⊓ E
  let Eg := E.map c.H.subtype
  let Dg := D.map c.H.subtype
  have hEg : Eg = centralizer ({z} : Set G) ⊓ centralizer ({((t:c.H):G)} : Set G) := by
    change (centralizer ({(t:c.H)} : Set c.H)).map c.H.subtype = _
    rw [map_subtype_centralizer_singleton,← hH]
  have hEc : Nat.card Eg = 32 := by
    rw [card_map_of_injective c.H.subtype_injective]
    exact core_involution_local_centralizer_card c t ht htZ
  by_contra hn
  have hclosed (u : c.H) (hu : IsConj z (u:G)) : u ∈ Q := by
    have hu2 : orderOf u = 2 := by
      obtain ⟨g,hg⟩ := isConj_iff.mp hu
      have hh := (MulAut.conj g).orderOf_eq z
      change orderOf (g*z*g⁻¹)=orderOf z at hh
      rw [hg,hz] at hh
      exact (orderOf_coe u).symm.trans hh
    by_contra huQ
    exact hn ⟨z,u,hz,hH,hu2,huQ,hu⟩
  have hall (u : c.H) (hu : u ∈ Q) (hu2 : orderOf u = 2) : IsConj z (u:G) := by
    let uQ : Q := ⟨u,hu⟩
    have huQ2 : orderOf uQ = 2 := (orderOf_coe uQ).symm.trans hu2
    by_cases huC : uQ ∈ center Q
    · obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp d.center_card
      have hune : (⟨uQ,huC⟩ : center Q) ≠ 1 := by
        intro he
        have hh : uQ = 1 := congrArg Subtype.val he
        simp [hh] at huQ2
      have hzne : (⟨⟨zH,hzQ⟩,hzQcent⟩ : center Q) ≠ 1 := by
        intro he
        have hh : zH = 1 := congrArg (fun a : center Q => ((a:Q):c.H)) he
        simp [hh] at hzH
      have he : u = zH := congrArg (fun a : center Q => ((a:Q):c.H))
        ((hw _ hune).trans (hw _ hzne).symm)
      rw [he]
    · exact hconj.trans (c.H.subtype.map_isConj
        (core_noncentral_involutions_conjugate c t uQ ht htZ huQ2 huC))
  have hclass : Dg = closure {u : G | u ∈ Eg ∧ IsConj z u} := by
    change D.map c.H.subtype = _
    change closure {x : c.H | x ∈ D ∧ orderOf x = 2} = D at hgen
    rw [← hgen,MonoidHom.map_closure]
    congr 1
    ext u
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨mem_map_of_mem c.H.subtype hv.1.2,hall v hv.1.1 hv.2⟩
    · rintro ⟨⟨v,hv,rfl⟩,hvf⟩
      have hv2 : orderOf v = 2 := by
        obtain ⟨g,hg⟩ := isConj_iff.mp hvf
        have hh := (MulAut.conj g).orderOf_eq z
        change orderOf (g*z*g⁻¹)=orderOf z at hh
        rw [hg,hz] at hh
        exact (orderOf_coe v).symm.trans hh
      exact ⟨v,⟨⟨hclosed v hvf,hv⟩,hv2⟩,rfl⟩
  have hNE : normalizer (Eg : Set G) ≤ normalizer (Dg : Set G) := by
    rw [hclass]
    exact normalizer_le_normalizer_conjugacy_generated Eg z
  have hderived : (_root_.commutator Dg).map Dg.subtype = zpowers z := by
    rw [map_subtype_commutator]
    change ⁅D.map c.H.subtype,D.map c.H.subtype⁆ = _
    rw [← map_commutator,← map_subtype_commutator,hline,MonoidHom.map_zpowers]
    rfl
  have hN : normalizer (Eg : Set G) ≤ centralizer ({z} : Set G) :=
    hNE.trans (normalizer_le_centralizer_of_characteristic_involution Dg
      (_root_.commutator Dg) z hz hderived)
  obtain ⟨S,hS⟩ : ∃ S : Sylow 2 (centralizer ({z} : Set G)), Nat.card S = 64 := by
    rw [← hH]
    exact ⟨Classical.choice inferInstance,H_sylow_card c _⟩
  have hp : IsPGroup 2 Eg := IsPGroup.of_card (n := 5) hEc
  apply normalizer_inf_centralizer_not_le_of_isConj z ((t:c.H):G) hconj
    (hEg ▸ hp) S ?_ (by
      change normalizer ((centralizer ({z} : Set G) ⊓
        centralizer ({((t:c.H):G)} : Set G) : Subgroup G) : Set G) ≤ _
      rw [← hEg]
      exact hN)
  rw [← hEg,hEc,hS]
  decide

theorem residual_involution_mem_core (n : c.H) (hn : orderOf n = 2)
    (hK : n ∈ c.H₁ ⊔ c.H₂) : n ∈ quaternionCore c := by
  let K := c.H₁ ⊔ c.H₂
  let R := (quaternionCore c).subgroupOf K
  have hQK : quaternionCore c ≤ K :=
    sup_le_sup (c.H₁.pCoreIn_le 2) (c.H₂.pCoreIn_le 2)
  have hR : Nat.card R = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hQK).toEquiv).trans (quaternionCore_card c)
  have hquot : Nat.card (K ⧸ R) = 9 := by
    have hh := R.card_mul_index
    rw [hR,product_card c,index_eq_card] at hh
    omega
  let q := QuotientGroup.mk' R
  let nK : K := ⟨n,hK⟩
  have h2 : (q nK)^2=1 := by
    rw [← map_pow]
    exact (congrArg q (Subtype.ext (hn ▸ pow_orderOf_eq_one n))).trans (map_one q)
  have h9 : (q nK)^9=1 := hquot ▸ pow_card_eq_one' (x := q nK)
  have ho : orderOf (q nK) = 1 := Nat.dvd_one.mp
    (by simpa using Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h9))
  exact (QuotientGroup.eq_one_iff nK).mp (orderOf_eq_one_iff.mp ho)

/-- The original index-two product has an actual involution complement, fused
to the marked central involution in the ambient group. -/
theorem exists_fused_involution_complement :
    ∃ (z : G) (n : c.H), orderOf z = 2 ∧ c.H = centralizer ({z} : Set G) ∧
      orderOf n = 2 ∧ n ∉ c.H₁ ⊔ c.H₂ ∧
      (c.H₁ ⊔ c.H₂).IsComplement' (zpowers n) ∧ IsConj z (n : G) := by
  classical
  obtain ⟨z,n,hz,hH,hn,hnQ,hf⟩ := exists_fused_involution_outside_core c
  have hnK : n ∉ c.H₁ ⊔ c.H₂ := fun hh => hnQ (residual_involution_mem_core c n hn hh)
  refine ⟨z,n,hz,hH,hn,hnK,?_,hf⟩
  apply isComplement'_of_card_mul_and_disjoint
  · rw [product_card c,Nat.card_zpowers,hn,H_card c]
  · apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    rintro x ⟨hxK,hxn⟩
    change x ∈ c.H₁ ⊔ c.H₂ at hxK
    change x ∈ zpowers n at hxn
    change x = 1
    rw [mem_zpowers_iff_mem_range_orderOf,hn] at hxn
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hxn
    have hi2 := Finset.mem_range.mp hi
    interval_cases i
    · simpa using he.symm
    · exact (hnK (by simpa only [← he,pow_one] using hxK)).elim

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
