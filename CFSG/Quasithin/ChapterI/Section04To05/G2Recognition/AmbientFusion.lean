module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.ExtensionInvolution
public import Theory.GroupTheory.NormalSubgroupInvolutionFiber

/-!
# One ambient involution class

In a chosen H-Sylow, Q has index two. The both-outer quaternion cocycle
theorem conjugates any two involutions in its outside coset by Q. Sylow
conjugacy therefore fuses all involutions outside H₁H₂ inside H. The
constructed complement is fused to the marked central involution, and
the earlier order-nine orbit calculation already fuses every involution
of Q to it. All H-involutions, and then all G-involutions by the ambient
Sylow embedding, lie in that single class.

The proof retains the actual normal subgroup, conjugation action and
embedding into G. It completes the fusion conclusion of Fong–Wong §2F(ii),
Nagoya Math. J.36 (1969), pp.153–154, for the q = 3 configuration.
Chapter14Extension applies it to the selected-counterexample source data.
The remaining I.4.5 ambient recognition is not supplied by this fusion result.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

/-- Involutions outside the residual form one H-conjugacy class. -/
theorem outside_involutions_conjugate (n x : c.H) (hn : orderOf n=2)
    (hnout : n ∉ c.H₁ ⊔ c.H₂) (hx : orderOf x=2) (hxout : x ∉ c.H₁ ⊔ c.H₂) :
    IsConj n x := by
  let Q := quaternionCore c
  let d := quaternionCoreData c
  have hQK : Q ≤ c.H₁ ⊔ c.H₂ :=
    sup_le_sup (c.H₁.pCoreIn_le 2) (c.H₂.pCoreIn_le 2)
  have hnQ : n ∉ Q := fun hh=>hnout (hQK hh)
  have hxQ : x ∉ Q := fun hh=>hxout (hQK hh)
  have pn : IsPGroup 2 (zpowers n) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hn]; rfl)
  have px : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hx]; rfl)
  obtain ⟨T,hnT⟩ := pn.exists_le_sylow
  obtain ⟨U,hxU⟩ := px.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq c.H U T
  let y : c.H := g*x*g⁻¹
  have hyT : y ∈ (T : Subgroup c.H) := by
    rw [← hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hxU (mem_zpowers x))
  have hnT' : n ∈ (T : Subgroup c.H) := hnT (mem_zpowers n)
  have hyQ : y ∉ Q := by
    intro hh
    apply hxQ
    exact (mem_normalizer_iff.mp
      (show g ∈ normalizer (Q : Set c.H) by rw [Q.normalizer_eq_top]; trivial) x).mpr hh
  have hindex : (Q.subgroupOf (T : Subgroup c.H)).index=2 := by
    have hh := (Q.subgroupOf (T : Subgroup c.H)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (quaternionCore_le_sylow c T)).toEquiv,
      quaternionCore_card c,H_sylow_card c T] at hh
    omega
  have hcoset : y*n⁻¹∈Q := by
    have hh : (⟨y,hyT⟩ : T) * (⟨n,hnT'⟩ : T)⁻¹ ∈ Q.subgroupOf T :=
      ((Q.subgroupOf (T : Subgroup c.H)).mul_mem_iff_of_index_two hindex).mpr
        (by change y∈Q ↔ n⁻¹∈Q; rw [Q.inv_mem_iff]; simp [hyQ,hnQ])
    exact hh
  have hn2 : n^2=1 := hn ▸ pow_orderOf_eq_one n
  have hx2 : x^2=1 := hx ▸ pow_orderOf_eq_one x
  have hy2 : y^2=1 := by
    change ((MulAut.conj g) x)^2=1
    rw [← map_pow,hx2,map_one]
  have ha : (MulAut.conjNormal n : MulAut Q)^2=1 := by rw [← map_pow,hn2,map_one]
  have ho := outside_bothOuter c n hnout
  have hcocycle := (quaternion_central_product_outer_involution d.left d.right
    d.left_model d.right_model d.span d.intersection_card d.commute
    (MulAut.conjNormal n) ha ho.left_map ho.right_map ho.left_outer ho.right_outer).2.2
  have he : normalConjThrough Q (MulEquiv.refl Q) n = (MulAut.conjNormal n : MulAut Q) := by
    ext q
    rfl
  obtain ⟨q,hq⟩ := normalConjThrough_involution_orbit Q (MulEquiv.refl Q) n hn2
    (by rw [he]; exact hcocycle) y hy2 hcoset
  exact (isConj_iff.mpr ⟨(q:c.H),hq⟩).trans (isConj_iff.mpr ⟨g,rfl⟩).symm

private theorem marking_in_core_center (z : G) (hH : c.H = centralizer ({z} : Set G)) :
    ∃ q : quaternionCore c, ((q:c.H):G)=z ∧ q∈center (quaternionCore c) := by
  let zH : c.H := ⟨z,hH.symm ▸ mem_centralizer_singleton_iff.mpr rfl⟩
  have hc : zH∈center c.H := mem_center_iff.mpr fun x=>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hH ▸ x.property))
  have hq : zH∈quaternionCore c := core_self_centralizing c (fun x _=>mem_center_iff.mp hc x)
  exact ⟨⟨zH,hq⟩,rfl,mem_center_iff.mpr (fun x=>Subtype.ext (mem_center_iff.mp hc x))⟩

private theorem marked_involution_unique (z w : G) (hz : orderOf z=2) (hw : orderOf w=2)
    (hHz : c.H=centralizer ({z}:Set G)) (hHw : c.H=centralizer ({w}:Set G)) : z=w := by
  obtain ⟨q,hq,hqZ⟩ := marking_in_core_center c z hHz
  obtain ⟨r,hr,hrZ⟩ := marking_in_core_center c w hHw
  obtain ⟨u,_,hu⟩ := (Nat.card_eq_two_iff' (1 : center (quaternionCore c))).mp
    (quaternionCoreData c).center_card
  have hqn : (⟨q,hqZ⟩ : center (quaternionCore c)) ≠ 1 := by
    intro hh
    have he : z=1 := hq.symm.trans (congrArg (fun a : center (quaternionCore c)=>(((a:quaternionCore c):c.H):G)) hh)
    simp [he] at hz
  have hrn : (⟨r,hrZ⟩ : center (quaternionCore c)) ≠ 1 := by
    intro hh
    have he : w=1 := hr.symm.trans (congrArg (fun a : center (quaternionCore c)=>(((a:quaternionCore c):c.H):G)) hh)
    simp [he] at hw
  exact hq.symm.trans ((congrArg (fun a : center (quaternionCore c)=>(((a:quaternionCore c):c.H):G))
    ((hu _ hqn).trans (hu _ hrn).symm)).trans hr)

theorem marked_involution_fuses_core (z : G) (hz : orderOf z=2)
    (hH : c.H=centralizer ({z}:Set G)) (x : quaternionCore c) (hx : orderOf x=2) :
    IsConj z ((x:c.H):G) := by
  by_cases hxZ : x∈center (quaternionCore c)
  · obtain ⟨q,hq,hqZ⟩ := marking_in_core_center c z hH
    obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : center (quaternionCore c))).mp
      (quaternionCoreData c).center_card
    have hxn : (⟨x,hxZ⟩ : center (quaternionCore c)) ≠ 1 := by
      intro hh
      have he : x=1 := congrArg Subtype.val hh
      simp [he] at hx
    have hqn : (⟨q,hqZ⟩ : center (quaternionCore c)) ≠ 1 := by
      intro hh
      have he : z=1 := hq.symm.trans (congrArg (fun a : center (quaternionCore c)=>(((a:quaternionCore c):c.H):G)) hh)
      simp [he] at hz
    have he : x=q := congrArg Subtype.val ((hw _ hxn).trans (hw _ hqn).symm)
    rw [he,hq]
  · obtain ⟨w,hw,hHw,hf⟩ := core_noncentral_involution_fusion c x hx hxZ
    exact marked_involution_unique c z w hz hw hH hHw ▸ hf

theorem marked_involution_fuses_H (z : G) (hz : orderOf z=2)
    (hH : c.H=centralizer ({z}:Set G)) (x : c.H) (hx : orderOf x=2) : IsConj z (x:G) := by
  by_cases hxK : x∈c.H₁⊔c.H₂
  · exact marked_involution_fuses_core c z hz hH
      ⟨x,residual_involution_mem_core c x hx hxK⟩ (by rwa [orderOf_mk])
  · obtain ⟨w,n,hw,hHw,hn,hnout,_,hf⟩ := exists_fused_involution_complement c
    have he := marked_involution_unique c z w hz hw hH hHw
    exact he ▸ hf.trans (c.H.subtype.map_isConj (outside_involutions_conjugate c n x hn hnout hx hxK))

/-- Every involution in the original finite group is in the marked class. -/
theorem marked_involution_fuses_ambient (z : G) (hz : orderOf z=2)
    (hH : c.H=centralizer ({z}:Set G)) (x : G) (hx : orderOf x=2) : IsConj z x := by
  let T : Sylow 2 c.H := Classical.choice inferInstance
  obtain ⟨S,hS⟩ := H_sylow_is_ambient c T
  have px : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hx]; rfl)
  obtain ⟨U,hxU⟩ := px.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G U S
  have hyS : g*x*g⁻¹∈(S:Subgroup G) := by
    rw [← hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hxU (mem_zpowers x))
  have hyH : g*x*g⁻¹∈c.H := (hS ▸ map_subtype_le _) hyS
  let y : c.H := ⟨g*x*g⁻¹,hyH⟩
  have hy : orderOf y=2 := (orderOf_coe y).symm.trans (((MulAut.conj g).orderOf_eq x).trans hx)
  exact (marked_involution_fuses_H c z hz hH y hy).trans (isConj_iff.mpr ⟨g,rfl⟩).symm

include c in
theorem involutions_conjugate (x y : G) (hx : orderOf x=2) (hy : orderOf y=2) : IsConj x y := by
  obtain ⟨z,hz,_,hH⟩ := exists_marked_involution c
  have hzG := (orderOf_coe z).trans hz
  exact (marked_involution_fuses_ambient c z hzG hH x hx).symm.trans
    (marked_involution_fuses_ambient c z hzG hH y hy)

include c in
theorem involution_centralizer_card (x : G) (hx : orderOf x=2) :
    Nat.card (centralizer ({x}:Set G)) = 576 := by
  obtain ⟨z,hz,_,hH⟩ := exists_marked_involution c
  have hf := marked_involution_fuses_ambient c z ((orderOf_coe z).trans hz) hH x hx
  rw [← card_centralizer_eq_of_isConj (z:G) x hf,← hH,H_card c]

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
