module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.Assembly
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.InvolutionGeometry
public import CFSG.Quasithin.ChapterA.Section05To06.Counting
public import Theory.SpecificGroups.Suzuki.InvolutionFusion
public import Theory.GroupTheory.ConjugacyOrderCensus

/-!
# The commuting-class closure and mixed involution count in J.3

The product of two commuting z-class involutions cannot belong to the s-class:
a conjugate carrying their product to s puts both factors in the actual Suzuki
residual, whereas s lies outside that residual by the marked direct product.
The one involution class of Sz(8), the literal residual centralizer of order64,
and the proved Suzuki order give exactly455 z-conjugates commuting with s.

The only earlier-source inputs are the two actual involution classes and the
J.2.9 SuzukiSourceConclusion, with all ambient subgroup maps retained.
Source: Aschbacher--Smith J.3.2--3, printed pp.438--439.
-/

public section
open Subgroup BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterJ.Section03
open ChapterA.Section05To06 Centralizers
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

private theorem s_not_mem_residual (c : Choices d) (r : c.SuzukiSourceConclusion) :
    c.s ∉ c.Ls := by
  intro hs
  have he : r.product (⟨c.s,c.s_mem⟩,1) = r.product (1,⟨c.s,hs⟩) := by
    apply Subtype.ext
    simp only [r.product_apply, OneMemClass.coe_one, mul_one, one_mul]
  have hh := congrArg (fun p : c.S0 × c.Ls => (p.1 : G)) (r.product.injective he)
  exact c.s_ne_one hh

theorem class_closed_of_suzuki (c : Choices d) (r : c.SuzukiSourceConclusion)
    (h : TwoInvolutionClasses c.z c.s) :
    ∀ u v : G, IsConj c.z u → IsConj c.z v → Commute u v →
      u*v ≠ 1 → IsConj c.z (u*v) := by
  intro u v hu hv hc hn
  have hu2 : u^2 = 1 := by
    obtain ⟨g,rfl⟩ := isConj_iff.mp hu
    simpa only [map_pow, map_one, MulAut.conj_apply] using
      congrArg (MulAut.conj g) ((orderOf_eq_prime_iff.mp h.order_z).1)
  have hv2 : v^2 = 1 := by
    obtain ⟨g,rfl⟩ := isConj_iff.mp hv
    simpa only [map_pow, map_one, MulAut.conj_apply] using
      congrArg (MulAut.conj g) ((orderOf_eq_prime_iff.mp h.order_z).1)
  have ho : orderOf (u*v) = 2 := orderOf_eq_prime (by rw [hc.mul_pow,hu2,hv2,one_mul]) hn
  rcases h.exhaustive (u*v) ho with hz | hs
  · exact hz
  · obtain ⟨g,hg⟩ := isConj_iff.mp hs
    let f := MulAut.conj g⁻¹
    have huv : f (u*v) = c.s := by
      change g⁻¹*(u*v)*(g⁻¹)⁻¹ = c.s
      rw [← hg]
      group
    have huconj : IsConj c.z (f u) := hu.trans (isConj_iff.mpr ⟨g⁻¹,rfl⟩)
    have hvconj : IsConj c.z (f v) := hv.trans (isConj_iff.mpr ⟨g⁻¹,rfl⟩)
    have hcu : Commute (f u) c.s := huv ▸ ((Commute.refl u).mul_right hc).map f
    have hcv : Commute (f v) c.s := huv ▸ (hc.symm.mul_right (Commute.refl v)).map f
    have huL : f u ∈ c.Ls := by
      have hm : f u ∈ {x : G | IsConj c.z x} ∩ (c.Gs : Set G) :=
        ⟨huconj,mem_centralizer_singleton_iff.mpr hcu.eq⟩
      rw [r.involutions] at hm
      exact hm.1
    have hvL : f v ∈ c.Ls := by
      have hm : f v ∈ {x : G | IsConj c.z x} ∩ (c.Gs : Set G) :=
        ⟨hvconj,mem_centralizer_singleton_iff.mpr hcv.eq⟩
      rw [r.involutions] at hm
      exact hm.1
    exact False.elim (s_not_mem_residual c r (huv ▸ (map_mul f u v).symm ▸ c.Ls.mul_mem huL hvL))
/-- The literal Suzuki residual supplies the exact mixed-class count of J.3.3. -/
theorem count_commuting_s_of_suzuki (c : Choices d) (r : c.SuzukiSourceConclusion) :
    Nat.card {u : G // IsConj c.z u ∧ Commute u c.s} = 455 := by
  have hzV : c.z ∈ d.V := (d.center_eq.le c.z_mem_Z).1
  have hz1 : c.z ≠ 1 := by
    intro he
    have ho := InvolutionGeometry.z_order c
    simp [he] at ho
  have hsH : c.s ∈ d.toTypeRuSetup.H := d.S_le_H c.s_mem.1
  have hzGs : c.z ∈ c.Gs := by
    apply mem_centralizer_singleton_iff.mpr
    have hsC := c.H_eq_centralizer_z ▸ hsH
    exact (mem_centralizer_singleton_iff.mp hsC).symm
  have hzL : c.z ∈ c.Ls := by
    have hh : c.z ∈ {x : G | IsConj c.z x} ∩ (c.Gs : Set G) := ⟨IsConj.refl _,hzGs⟩
    rw [r.involutions] at hh
    exact hh.1
  let zL : c.Ls := ⟨c.z,hzL⟩
  have hzLo : orderOf zL = 2 := by
    change orderOf (⟨c.z,hzL⟩ : c.Ls) = 2
    rw [← Subgroup.orderOf_coe]
    exact InvolutionGeometry.z_order c
  have hC : Nat.card (centralizer ({zL} : Set c.Ls)) = 64 := by
    rw [r.centralizers zL hzV (by exact fun he => hz1 (congrArg Subtype.val he)),← r.sylow_eq]
    exact r.sylow_card
  have hconj (x : c.Ls) : IsInvolution x ↔ IsConj zL x := by
    constructor
    · intro hx
      have hz' : orderOf (r.model zL) = 2 := (r.model.orderOf_eq zL).trans hzLo
      have hx' : orderOf (r.model x) = 2 := (r.model.orderOf_eq x).trans
        (orderOf_eq_prime hx.2 hx.1)
      simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using r.model.symm.toMonoidHom.map_isConj
        (BenderSuzuki.MatrixGroups.suzuki_involutions_isConj 1 (by decide) _ _ hz' hx')
    · intro hx
      have ho : orderOf x = 2 := by
        obtain ⟨g,rfl⟩ := isConj_iff.mp hx
        exact ((MulAut.conj g).orderOf_eq zL).trans hzLo
      exact (orderOf_eq_prime_iff.mp ho).symm
  have hI : Nat.card {x : c.Ls // IsInvolution x} = 455 := by
    have hc := ConjClasses.nat_card_carrier_mul_card_centralizer zL
    have hcard : Nat.card c.Ls = 29120 := by
      rw [Nat.card_congr r.model.toEquiv, BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card 1 (by decide)]
      norm_num
    rw [hC,hcard] at hc
    have hcar : (ConjClasses.mk zL).carrier = {x : c.Ls | IsConj zL x} := by
      ext x
      simp only [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, Set.mem_ofPred_eq]
      exact isConj_comm
    rw [hcar] at hc
    change Nat.card {x : c.Ls // IsConj zL x} * 64 = 29120 at hc
    have he : Nat.card {x : c.Ls // IsInvolution x} = Nat.card {x : c.Ls // IsConj zL x} :=
      Nat.card_congr (Equiv.subtypeEquivRight hconj)
    rw [he]
    omega
  let e : {u : G // IsConj c.z u ∧ Commute u c.s} ≃ {x : c.Ls // IsInvolution x} := {
    toFun := fun u => by
      have hmem : u.val ∈ {x : G | IsConj c.z x} ∩ (c.Gs : Set G) :=
        ⟨u.property.1, mem_centralizer_singleton_iff.mpr u.property.2.eq⟩
      rw [r.involutions] at hmem
      exact ⟨⟨u.val,hmem.1⟩, (by exact fun he => hmem.2.1 (congrArg Subtype.val he)),
        Subtype.ext hmem.2.2⟩
    invFun := fun x => by
      have hmem : x.val.val ∈ {u : G | u ∈ c.Ls ∧ IsInvolution u} :=
        ⟨x.val.property, (by exact fun he => x.property.1 (Subtype.ext he)),
          congrArg Subtype.val x.property.2⟩
      rw [← r.involutions] at hmem
      exact ⟨x.val.val,hmem.1,mem_centralizer_singleton_iff.mp hmem.2⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }
  exact (Nat.card_congr e).trans hI

end CFSG.Quasithin.ChapterJ.Section03
