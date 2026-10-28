module
public import Theory.GroupTheory.ElementaryS3CentralRetraction
public import Theory.GroupTheory.ElementaryEightSymmetricThreeCenter
public import Theory.GroupTheory.CentralTwoSymmetricFourRecognition
public import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Splitting an elementary-eight extension of S₃

A self-centralizing elementary kernel of order eight has a central line of
order two. A cubic lift fixes exactly that line, by orbit counting. An
involution outside the kernel then gives a central retraction, and its kernel
is S₄. Thus the whole group is C₂×S₄. The involutory lift is essential: the
nonsplit group A₄:C₄ also has an elementary-eight core and S₃ quotient.

This supplies the original local vertex recognition in the Sp₄(2) branch of
Aschbacher–Smith F.1.12(I)(2) and F.6.5, printed pp.262,305.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem fixed_eight_cubic_card_two {E : Type*} [Group E] [Finite E]
    (hE : Nat.card E=8) (B : Subgroup (MulAut E)) (hB : Nat.card B=3) :
    Nat.card (FixedPoints.subgroup B E)=2 := by
  let F := FixedPoints.subgroup B E
  have hp : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using hB)
  have hm := hp.card_modEq_card_fixedPoints E
  change Nat.card E%3=Nat.card F%3 at hm
  rw [hE] at hm
  have hd : Nat.card F∣8 := hE ▸ F.card_subgroup_dvd_card
  have hn : Nat.card F≠8 := by
    intro hh
    have ht : F=⊤ := F.eq_top_of_card_eq (hh.trans hE.symm)
    have hb : B=⊥ := by
      apply eq_bot_iff.mpr
      intro b hb
      apply MulEquiv.ext
      intro x
      exact (show x∈F from ht ▸ mem_top x) ⟨b,hb⟩
    rw [hb,card_bot] at hB
    omega
  have hmem := Nat.mem_divisors.mpr ⟨hd,by decide⟩
  have hdivs : (8:ℕ).divisors={1,2,4,8} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  change Nat.card F=2
  omega

private theorem fixed_cyclic_iff {E : Type*} [Group E] (a : MulAut E) (x : E) :
    x∈FixedPoints.subgroup (zpowers a) E ↔ a x=x := by
  constructor
  · intro h; exact h ⟨a,mem_zpowers a⟩
  · intro h ⟨b,hb⟩
    obtain ⟨n,rfl⟩ := hb
    have hh : x∈MulAction.fixedBy E a := h
    exact MulAction.mem_fixedBy_zpow hh n

/-- An elementary-eight extension of S₃ with self-centralizing kernel and
an involution outside that kernel is the split C₂×S₄ group. -/
theorem c2_symmetric_four_of_elementary_eight_s3_involution
    (f : G→*Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hE : IsElementaryAbelian 2 f.ker) (hcard : Nat.card f.ker=8)
    (hself : centralizer (f.ker : Set G)≤f.ker)
    (w : G) (hw : w^2=1) (hwn : f w≠1) :
    Nonempty (G≃*Multiplicative (ZMod 2)×Equiv.Perm (Fin 4)) := by
  let := hE
  have hindex : f.ker.index=6 := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hf,Nat.card_congr Subgroup.topEquiv.toEquiv]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hG : Nat.card G=48 := by
    have hh := f.ker.card_mul_index
    rw [hcard,hindex] at hh
    omega
  obtain ⟨Z,hZcard,hZE,hZ⟩ := exists_central_card_two_of_abelian_eight_index_six
    f.ker hcard hself hindex
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hG];decide)
  have ha3 : a^3=1 := by rw [←ha];exact pow_orderOf_eq_one a
  have han : f a≠1 := by
    intro hh
    let z : f.ker := ⟨a,hh⟩
    have hz : orderOf z=3 := (Subgroup.orderOf_coe z).symm.trans ha
    have hc := (IsElementaryAbelian.isPGroup 2 f.ker).orderOf_coprime
      (by decide : Nat.Coprime 2 3) z
    rw [hz] at hc
    norm_num at hc
  have haf : orderOf (f a)=3 := orderOf_eq_prime (by rw [←map_pow,ha3,map_one]) han
  let α : MulAut f.ker := MulAut.conjNormal a
  have hα3 : α^3=1 := by change (MulAut.conjNormal a)^3=1;rw [←map_pow,ha3,map_one]
  have hαn : α≠1 := by
    intro he
    apply han
    apply hself
    intro x hx
    have hh := congrArg (fun b : MulAut f.ker => (b ⟨x,hx⟩ : G)) he
    change a*x*a⁻¹=x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let F := FixedPoints.subgroup (zpowers α) f.ker
  have hFcard : Nat.card F=2 := fixed_eight_cubic_card_two hcard _
    ((Nat.card_zpowers α).trans (orderOf_eq_prime hα3 hαn))
  have hZF : Z.subgroupOf f.ker≤F := by
    intro x hx
    apply (fixed_cyclic_iff α x).mpr
    apply Subtype.ext
    change a*(x:G)*a⁻¹=x
    have hc : a*(x:G)=(x:G)*a := mem_center_iff.mp (hZ hx) a
    rw [hc,mul_inv_cancel_right]
  have hZF_eq : Z.subgroupOf f.ker=F := eq_of_le_of_card_ge hZF (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZE).toEquiv,hZcard,hFcard])
  have hfixed (x : G) (hx : x∈f.ker) : Commute a x ↔ x∈Z := by
    have hh := fixed_cyclic_iff α (⟨x,hx⟩ : f.ker)
    change (⟨x,hx⟩ : f.ker)∈F ↔ _ at hh
    rw [←hZF_eq] at hh
    change x∈Z ↔ α ⟨x,hx⟩=⟨x,hx⟩ at hh
    rw [Subtype.ext_iff] at hh
    change x∈Z ↔ a*x*a⁻¹=x at hh
    exact (hh.trans mul_inv_eq_iff_eq_mul).symm
  have hwf : orderOf (f w)=2 := orderOf_eq_prime (by rw [←map_pow,hw,map_one]) hwn
  obtain ⟨r,hr⟩ := exists_central_retraction_of_elementary_s3_quotient f hf hE Z hZE hZ
    hZcard a ha3 haf hfixed w hw hwf
  have hcomp : Z.IsComplement' r.ker := by
    constructor
    · rintro ⟨z,x⟩ ⟨t,y⟩ he
      have ht : z=t := by
        have hh := congrArg r he
        simpa only [map_mul,hr,MonoidHom.mem_ker.mp x.property,
          MonoidHom.mem_ker.mp y.property,mul_one] using hh
      subst t
      have hxy : x=y := Subtype.ext (mul_left_cancel he)
      exact Prod.ext rfl hxy
    · intro g
      let z := r g
      let x : r.ker := ⟨(z:G)⁻¹*g,by
        change r ((z:G)⁻¹*g)=1
        rw [map_mul,map_inv,hr,inv_mul_cancel]⟩
      exact ⟨(z,x),mul_inv_cancel_left _ _⟩
  exact c2_symmetric_four_of_central_complement f.ker Z r.ker hcard hself hZ hZE hZcard hG hcomp
end Theory.GroupTheory
