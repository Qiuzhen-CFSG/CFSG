module
public import Theory.GroupTheory.WreathTwoThreeCore
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A normal cubic in an index-two binary-plane wreath subgroup

An elementary four-group in the standard dihedral Sylow subgroup normalizes
one of two explicit cubic lines. The characteristic cubic base has order nine
and belongs to every index-two subgroup. It commutes with either line, and its
join with the marked four-group has order 36, hence is the entire index-two
subgroup. The line is therefore normal. Sylow conjugacy transports both the
four-group and the containing subgroup; no subgroup-lattice enumeration is used.

The only finite certificate concerns the eight-element dihedral model and the
six-element plane group. This supplies the degree-four action endpoint in
Aschbacher--Smith 14.3.15, using the original index bound from G.9.4(4).
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.WreathTwoIndexTwo
private abbrev SL := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private abbrev C2 := Multiplicative (ZMod 2)
public abbrev W := WreathTwoResidual.Actor
private instance : DecidableEq W := fun a b => decidable_of_iff
  (a.left=b.left ∧ a.right=b.right) RegularWreathProduct.ext_iff.symm
private def cubic : SL := ⟨!![0,1;1,1],by decide⟩
private def lineGenerator (diagonal : Bool) : W :=
  ⟨fun i => if diagonal || i=1 then cubic else 1,1⟩
private theorem generator_order (side : Bool) : orderOf (lineGenerator side)=3 := by
  apply orderOf_eq_prime
  · cases side <;> decide +kernel
  · cases side <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem dihedral_certificate : ∀ a : DihedralGroup 4,
    a^2=1 → a≠1 → a≠DihedralGroup.r 2 → ∃ side : Bool,
      ∀ b : DihedralGroup 4, a*b=b*a →
        wreathTwoDihedralHom b * lineGenerator side * (wreathTwoDihedralHom b)⁻¹ = lineGenerator side ∨
        wreathTwoDihedralHom b * lineGenerator side * (wreathTwoDihedralHom b)⁻¹ = (lineGenerator side)⁻¹ := by
  decide +kernel

private theorem card_W : Nat.card W=72 := by
  rw [RegularWreathProduct.card]
  have h : Nat.card SL=6 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  rw [h]
  norm_num [Nat.card_eq_fintype_card]

private theorem cubic_mem_core (x : W) (hx : x^3=1) : x∈pCore 3 W := by
  let q := QuotientGroup.mk' (pCore 3 W)
  have hd : orderOf (q x)∣3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow,hx,map_one])
  have hc := WreathTwoResidual.threeCore_quotient_two.orderOf_coprime
    (by decide : Nat.Coprime 2 3) (q x)
  have he : orderOf (q x)=1 := Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hd
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp he)

private theorem core_le_index_two (H : Subgroup W) (hi : H.index=2) : pCore 3 W≤H := by
  let := WreathTwoResidual.threeCore_elementary
  intro x hx
  have hcube : x^3=1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 (pCore 3 W)) (⟨x,hx⟩ : pCore 3 W))
  have hfour := H.sq_mem_of_index_two hi (x^2)
  have he : (x^2)^2=x := by rw [← pow_mul,show (2:ℕ)*2=3+1 by decide,pow_add,hcube,pow_one,one_mul]
  rwa [he] at hfour

private theorem standard_four_normalizes_line (A : Subgroup W)
    [IsElementaryAbelian 2 A] (hle : A≤(wreathTwoSylow : Subgroup W))
    (hcard : Nat.card A=4) : ∃ side : Bool,
      A≤normalizer (zpowers (lineGenerator side) : Set W) := by
  classical
  have hex : ∃ x : A, (x:W)≠1 ∧ (x:W)≠wreathTwoDihedralHom (DihedralGroup.r 2) := by
    by_contra hn
    have hh : ∀ x : A, (x:W)=1 ∨ (x:W)=wreathTwoDihedralHom (DihedralGroup.r 2) := by
      intro x
      by_cases h : (x:W)=1
      · exact Or.inl h
      · exact Or.inr (by by_contra hz; exact hn ⟨x,h,hz⟩)
    let f : A → Bool := fun x => (x:W)≠1
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      rcases hh x with hx | hx <;> rcases hh y with hy | hy
      · exact hx.trans hy.symm
      · have hz : wreathTwoDihedralHom (DihedralGroup.r 2)≠1 := by decide +kernel
        have hfalse : f x=false := by change decide ((x:W)≠1)=false; simp only [hx,ne_eq,not_true_eq_false,decide_false]
        have htrue : f y=true := by change decide ((y:W)≠1)=true; apply decide_eq_true; exact hy ▸ hz
        rw [hfalse,htrue] at hxy
        contradiction
      · have hz : wreathTwoDihedralHom (DihedralGroup.r 2)≠1 := by decide +kernel
        have htrue : f x=true := by change decide ((x:W)≠1)=true; apply decide_eq_true; exact hx ▸ hz
        have hfalse : f y=false := by change decide ((y:W)≠1)=false; simp only [hy,ne_eq,not_true_eq_false,decide_false]
        rw [htrue,hfalse] at hxy
        contradiction
      · exact hx.trans hy.symm
    have hc := Nat.card_le_card_of_injective f hf
    rw [hcard] at hc
    norm_num at hc
  obtain ⟨x,hx1,hxz⟩ := hex
  obtain ⟨a,ha⟩ := wreathTwoSylow_coe ▸ hle x.property
  have ha2 : a^2=1 := wreathTwoDihedralHom_injective (by
    rw [map_pow,ha,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=A) (x:W) x.property)
  have ha1 : a≠1 := by intro he; exact hx1 (by rw [← ha,he,map_one])
  have haz : a≠DihedralGroup.r 2 := by intro he; exact hxz (by rw [← ha,he])
  obtain ⟨side,hside⟩ := dihedral_certificate a ha2 ha1 haz
  refine ⟨side,?_⟩
  intro y hy
  obtain ⟨b,hb⟩ := wreathTwoSylow_coe ▸ hle hy
  have hab : a*b=b*a := wreathTwoDihedralHom_injective (by
    simp only [map_mul,ha,hb]
    exact congrArg Subtype.val (mul_comm x (⟨y,hy⟩ : A)))
  rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
  change zpowers (y * lineGenerator side * y⁻¹) = _
  rcases hside b hab with he | he
  · rw [← hb,he]
  · rw [← hb,he,zpowers_inv]

private theorem standard_index_two (H A : Subgroup W) (hi : H.index=2)
    [IsElementaryAbelian 2 A] (hAH : A≤H)
    (hAS : A≤(wreathTwoSylow : Subgroup W)) (hA : Nat.card A=4) :
    ∃ C : Subgroup H, C.Normal ∧ Nat.card C=3 := by
  obtain ⟨side,hAnorm⟩ := standard_four_normalizes_line A hAS hA
  let L := zpowers (lineGenerator side)
  have hLcard : Nat.card L=3 := (Nat.card_zpowers _).trans (generator_order side)
  have hLcore : L≤pCore 3 W := zpowers_le.mpr (cubic_mem_core _ (by
    rw [← orderOf_dvd_iff_pow_eq_one,generator_order]))
  have hcoreH := core_le_index_two H hi
  have hLH := hLcore.trans hcoreH
  have hcorenorm : pCore 3 W≤normalizer (L : Set W) := by
    let := WreathTwoResidual.threeCore_elementary
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val
      (mul_comm (⟨y,hLcore hy⟩ : pCore 3 W) (⟨x,hx⟩ : pCore 3 W))
  have hjoin : pCore 3 W⊔A=H := by
    apply eq_of_le_of_card_ge (sup_le hcoreH hAH)
    have hd9 : 9∣Nat.card (pCore 3 W⊔A : Subgroup W) := by
      simpa only [WreathTwoResidual.threeCore_card] using
        card_dvd_of_le (le_sup_left : pCore 3 W≤pCore 3 W⊔A)
    have hd4 : 4∣Nat.card (pCore 3 W⊔A : Subgroup W) := by
      simpa only [hA] using card_dvd_of_le (le_sup_right : A≤pCore 3 W⊔A)
    have hd36 := (by decide : Nat.Coprime 9 4).mul_dvd_of_dvd_of_dvd hd9 hd4
    have hcH : Nat.card H=36 := by
      have hh := H.card_mul_index
      rw [hi,card_W] at hh
      omega
    rw [hcH]
    exact Nat.le_of_dvd Nat.card_pos hd36
  have hHnorm : H≤normalizer (L : Set W) := hjoin ▸ sup_le hcorenorm hAnorm
  refine ⟨L.subgroupOf H,(normal_subgroupOf_iff_le_normalizer hLH).mpr hHnorm,?_⟩
  exact (Nat.card_congr (subgroupOfEquivOfLe hLH).toEquiv).trans hLcard

/-- Every index-two subgroup containing a four-group has a normal cubic. -/
public theorem normal_cubic_of_index_two (H A : Subgroup W) (hi : H.index=2)
    [IsElementaryAbelian 2 A] (hAH : A≤H) (hA : Nat.card A=4) :
    ∃ C : Subgroup H, C.Normal ∧ Nat.card C=3 := by
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq W wreathTwoSylow P
  let e : W≃*W := (MulAut.conj g).symm
  have hP : (P:Subgroup W).map e.toMonoidHom=(wreathTwoSylow:Subgroup W) := by
    apply (map_symm_eq_iff_map_eq (e:=MulAut.conj g) (wreathTwoSylow:Subgroup W)).mpr
    exact congrArg (fun Q:Sylow 2 W => (Q:Subgroup W)) hg
  let A' := A.map e.toMonoidHom
  let H' := H.map e.toMonoidHom
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.map (A:=A) e.toMonoidHom
  have hA' : Nat.card A'=4 := (card_map_of_injective e.injective).trans hA
  obtain ⟨C,hCn,hCc⟩ := standard_index_two H' A'
    ((index_map_of_bijective e.bijective H).trans hi) (map_mono hAH)
    (hP ▸ map_mono hAP) hA'
  let f : H≃*H' := e.subgroupMap H
  let D := C.map f.symm.toMonoidHom
  refine ⟨D,hCn.map _ f.symm.surjective,?_⟩
  exact (card_map_of_injective f.symm.injective).trans hCc
end Theory.GroupTheory.WreathTwoIndexTwo
